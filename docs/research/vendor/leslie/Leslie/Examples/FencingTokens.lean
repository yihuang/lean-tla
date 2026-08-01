import Leslie.Action
import Leslie.Rules.StatePred

/-! ## Fencing Tokens (Kleppmann) — explicit-network model

    A from-scratch Leslie model of the **fencing token** discipline described
    in Martin Kleppmann's "How to do distributed locking"
    (https://martin.kleppmann.com/2016/02/08/how-to-do-distributed-locking.html).

    ### The scenario fencing defends against

    A lock service grants a lease on a shared resource (storage). A client
    acquires the lock, but then stalls — a GC pause, a page fault, a network
    delay — long enough for its lease to expire. The lock service, seeing the
    expiry, grants the lock to a second client. Now **two clients believe they
    hold the lock at the same time**. The first, on waking, issues a write to
    storage and corrupts the second client's work.

    ### The fix

    Every lock grant carries a strictly increasing **fencing token**. A client
    attaches its token to every write. Storage remembers the highest token it
    has ever accepted (`highToken`) and **rejects any write whose token is not
    strictly greater**. The stalled client's write carries a now-stale token,
    so storage rejects it. No corruption, even though mutual exclusion at the
    lock service was violated.

    ### What is modeled here

    Three roles, communicating over an **explicit network** (`network : List Msg`):

    * **Lock service** — owns `nextToken`, the next token to hand out.
    * **Clients** (`Fin n`) — each remembers the token it currently holds
      (`held`), retained across an arbitrarily long stall before it writes.
    * **Storage** — owns `highToken`, the high-water mark of accepted tokens.

    The GC-pause attack is a genuine interleaving of this spec: a client may
    `recvGrant` an old token, then — many `grantToken`/`storageAccept` steps
    later — `sendWrite` with that stale token, which `storageReject` drops.
-/

open TLA

namespace FencingTokens

/-! ### Messages on the network -/

inductive Msg (n : Nat) where
  /-- Lock service → client `p`: you are granted fencing token `token`. -/
  | grant (p : Fin n) (token : Nat)
  /-- Client `p` → storage: please apply my write, tagged with `token`. -/
  | write (p : Fin n) (token : Nat)
  deriving DecidableEq

/-! ### State -/

structure FenceState (n : Nat) where
  /-- Lock service: next fencing token to issue. -/
  nextToken : Nat
  /-- Storage: highest token it has ever accepted (the fence). -/
  highToken : Nat
  /-- Client-local: the token client `p` currently believes it holds. -/
  held : Fin n → Option Nat
  /-- In-flight messages. -/
  network : List (Msg n)

def initialFence (n : Nat) : FenceState n where
  nextToken := 1            -- tokens issued are 1, 2, 3, …
  highToken := 0            -- storage has accepted nothing yet
  held := fun _ => none
  network := []

/-! ### Actions -/

inductive FenceAction (n : Nat) where
  | grantToken    (p : Fin n)             -- lock service issues a token to `p`
  | recvGrant     (p : Fin n) (t : Nat)   -- client `p` receives & stores token `t`
  | sendWrite     (p : Fin n) (t : Nat)   -- client `p` writes, tagged with held token `t`
  | storageAccept (p : Fin n) (t : Nat)   -- storage accepts a fresh-enough write
  | storageReject (p : Fin n) (t : Nat)   -- storage drops a stale write

def fenceSpec (n : Nat) : ActionSpec (FenceState n) (FenceAction n) where
  init := fun s => s = initialFence n
  actions := fun
    | .grantToken p => {
        -- Lock service always willing to grant (lease expiry of a prior holder
        -- is abstracted away — that is precisely how two clients end up live).
        gate := fun _ => True
        transition := fun s s' =>
          s' = { s with
            nextToken := s.nextToken + 1
            network := s.network ++ [Msg.grant p s.nextToken] } }
    | .recvGrant p t => {
        gate := fun s => Msg.grant p t ∈ s.network
        transition := fun s s' =>
          s' = { s with
            held := fun q => if q = p then some t else s.held q
            network := s.network.erase (Msg.grant p t) } }
    | .sendWrite p t => {
        -- A client writes using whatever token it holds — possibly long stale.
        gate := fun s => s.held p = some t
        transition := fun s s' =>
          s' = { s with network := s.network ++ [Msg.write p t] } }
    | .storageAccept p t => {
        -- The fence: accept only a strictly greater token; advance the fence.
        gate := fun s => Msg.write p t ∈ s.network ∧ t > s.highToken
        transition := fun s s' =>
          s' = { s with
            highToken := t
            network := s.network.erase (Msg.write p t) } }
    | .storageReject p t => {
        -- Stale token: drop the write, leave the fence untouched.
        gate := fun s => Msg.write p t ∈ s.network ∧ t ≤ s.highToken
        transition := fun s s' =>
          s' = { s with network := s.network.erase (Msg.write p t) } }

/-! ### Invariant

    Every token in the system — held by a client, in flight, or already
    accepted by storage — was genuinely issued by the lock service, hence is
    strictly below the issue counter `nextToken`. This is the inductive engine:
    it certifies that the storage fence `highToken` reflects a real, issued
    token (no client can forge a large token to leapfrog the fence). -/

structure FenceInv {n : Nat} (s : FenceState n) : Prop where
  /-- The storage fence is below the next-to-issue counter. -/
  high_lt_next  : s.highToken < s.nextToken
  /-- Every token a client holds was issued. -/
  held_lt_next  : ∀ p t, s.held p = some t → t < s.nextToken
  /-- Every granted token in flight was issued. -/
  grant_lt_next : ∀ p t, Msg.grant p t ∈ s.network → t < s.nextToken
  /-- Every write token in flight was issued. -/
  write_lt_next : ∀ p t, Msg.write p t ∈ s.network → t < s.nextToken

/-! ### Main safety theorems

    Two complementary statements of the fencing guarantee. Proofs deferred. -/

/-- **Invariant.** In every reachable state, all tokens were genuinely issued
    (the storage fence reflects a real token, never a forged one). -/
theorem fenceInv_holds (n : Nat) :
    pred_implies (fenceSpec n).safety [tlafml| □ ⌜ FenceInv ⌝] := by
  apply init_invariant
  · -- Base case: the initial state satisfies the invariant.
    intro s hs; subst hs
    exact {
      high_lt_next  := by simp [initialFence]
      held_lt_next  := by simp [initialFence]
      grant_lt_next := by simp [initialFence]
      write_lt_next := by simp [initialFence] }
  · -- Inductive step: every action preserves the invariant.
    rintro s s' ⟨i, hgate, htrans⟩ hinv
    cases i with
    | grantToken p =>
      simp only [fenceSpec] at htrans; subst htrans
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := hinv.high_lt_next; dsimp only; omega
      · intro q t ht; dsimp only at ht ⊢; have := hinv.held_lt_next q t ht; omega
      · intro q t ht
        simp only [List.mem_append, List.mem_singleton, Msg.grant.injEq] at ht
        rcases ht with h | ⟨_, rfl⟩
        · have := hinv.grant_lt_next q t h; dsimp only; omega
        · dsimp only; omega
      · intro q t ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with h | h
        · have := hinv.write_lt_next q t h; dsimp only; omega
        · exact absurd h (by simp)
    | recvGrant p t₀ =>
      simp only [fenceSpec] at hgate htrans; subst htrans
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hinv.high_lt_next
      · intro q t ht
        dsimp only at ht
        by_cases hq : q = p
        · rw [if_pos hq, Option.some.injEq] at ht; subst ht
          exact hinv.grant_lt_next p t₀ hgate
        · rw [if_neg hq] at ht; exact hinv.held_lt_next q t ht
      · intro q t ht; exact hinv.grant_lt_next q t (List.erase_subset ht)
      · intro q t ht; exact hinv.write_lt_next q t (List.erase_subset ht)
    | sendWrite p t₀ =>
      simp only [fenceSpec] at hgate htrans; subst htrans
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hinv.high_lt_next
      · exact hinv.held_lt_next
      · intro q t ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with h | h
        · exact hinv.grant_lt_next q t h
        · exact absurd h (by simp)
      · intro q t ht
        simp only [List.mem_append, List.mem_singleton, Msg.write.injEq] at ht
        rcases ht with h | ⟨rfl, rfl⟩
        · exact hinv.write_lt_next q t h
        · exact hinv.held_lt_next q t hgate
    | storageAccept p t₀ =>
      simp only [fenceSpec] at hgate htrans
      obtain ⟨hmem, _⟩ := hgate; subst htrans
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hinv.write_lt_next p t₀ hmem
      · exact hinv.held_lt_next
      · intro q t ht; exact hinv.grant_lt_next q t (List.erase_subset ht)
      · intro q t ht; exact hinv.write_lt_next q t (List.erase_subset ht)
    | storageReject p t₀ =>
      simp only [fenceSpec] at hgate htrans
      obtain ⟨hmem, _⟩ := hgate; subst htrans
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hinv.high_lt_next
      · exact hinv.held_lt_next
      · intro q t ht; exact hinv.grant_lt_next q t (List.erase_subset ht)
      · intro q t ht; exact hinv.write_lt_next q t (List.erase_subset ht)

/-- **Headline safety: the fence never regresses.** Across every step of the
    protocol — including a stalled client's stale write — the storage
    high-water mark `highToken` is monotonically non-decreasing. Combined with
    the `storageAccept` gate (`t > highToken`), this means storage accepts a
    strictly increasing sequence of tokens: once a write at token `t` is
    committed, no write at a token `≤ t` is ever accepted again. A delayed
    client holding a superseded token can never overwrite newer work — exactly
    Kleppmann's fencing guarantee. -/
theorem highToken_monotone (n : Nat) :
    pred_implies (fenceSpec n).safety
      [tlafml| □ ⟨fun s s' => s.highToken ≤ s'.highToken⟩] := by
  -- Step-level fact: no single action lowers the storage fence.
  have key : ∀ s s' : FenceState n, (fenceSpec n).toSpec.next s s' →
      s.highToken ≤ s'.highToken := by
    rintro s s' ⟨i, hgate, htrans⟩
    cases i with
    | grantToken p => simp only [fenceSpec] at htrans; subst htrans; simp
    | recvGrant p t => simp only [fenceSpec] at htrans; subst htrans; simp
    | sendWrite p t => simp only [fenceSpec] at htrans; subst htrans; simp
    | storageAccept p t =>
      simp only [fenceSpec] at hgate htrans
      obtain ⟨_, hgt⟩ := hgate; subst htrans; simp only; omega
    | storageReject p t => simp only [fenceSpec] at htrans; subst htrans; simp
  -- Lift the step-level fact through □.
  apply pred_implies_trans (q := [tlafml| □ ⟨(fenceSpec n).toSpec.next⟩])
  · intro e he; exact he.2
  · apply always_monotone; intro e h; exact key _ _ h

end FencingTokens
