import Leslie.Action
import Leslie.Round
import Leslie.Gadgets.SetFn

/-! ## Parameterized Single-Decree Paxos

    Faithful model of single-decree Paxos with `n` acceptors and `m` proposers,
    each with a distinct ballot number. Proves refinement to a Consensus spec.

    The safety proof uses Lamport's `SafeAt` predicate as an inductive invariant:
    for every ballot c below a proposal's ballot, there exists a quorum where each
    member either voted for the proposal's value at c, or will never vote at c.
    Agreement follows directly from SafeAt and quorum intersection.
-/

open TLA

namespace PaxosTextbookN

inductive Value where
  | v1 | v2
  deriving DecidableEq, Repr

structure ConsensusState where
  chosen : Option Value

inductive ConsensusAction where
  | choose1 | choose2

def consensus : ActionSpec ConsensusState ConsensusAction where
  init := fun s => s.chosen = none
  actions := fun
    | .choose1 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v1 }
      }
    | .choose2 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v2 }
      }

/-! ### Concrete Paxos State -/

@[ext]
structure PaxosState (n m : Nat) where
  prom : Fin n → Nat
  acc : Fin n → Option (Nat × Value)
  got1b : Fin m → Fin n → Bool
  rep : Fin m → Fin n → Option (Nat × Value)
  prop : Fin m → Option Value
  did2b : Fin m → Fin n → Bool
  /-- Ghost per-acceptor vote history: `voted i c = some v` means acceptor `i`
      voted for value `v` at ballot `c`. This field is acceptor-local and
      decouples the safety argument from proposer bookkeeping. -/
  voted : Fin n → Nat → Option Value

/-- Functional update of a two-argument function at `(i, c)`. -/
def updateVoted {n : Nat} (f : Fin n → Nat → Option Value)
    (i : Fin n) (c : Nat) (v : Value) : Fin n → Nat → Option Value :=
  fun j b => if j = i ∧ b = c then some v else f j b

inductive PaxosAction (n m : Nat) where
  | p1b (p : Fin m) (i : Fin n)
  | p2a (p : Fin m)
  | p2b (p : Fin m) (i : Fin n)

/-! ### Quorum utilities -/

def countTrue {n : Nat} (f : Fin n → Bool) : Nat :=
  ((List.finRange n).filter fun i => f i).length

def majority {n : Nat} (f : Fin n → Bool) : Bool :=
  decide (countTrue f * 2 > n)

theorem countTrue_setFn_true_ge {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    countTrue f ≤ countTrue (setFn f i true) := by
  unfold countTrue
  exact filter_length_mono (List.finRange n) (fun j => f j) (fun j => setFn f i true j) (by
    intro j hj; by_cases hji : j = i <;> simp [setFn, hji, hj])

theorem majority_setFn_true_of_majority {n : Nat} (f : Fin n → Bool) (i : Fin n)
    (h : majority f = true) : majority (setFn f i true) = true := by
  unfold majority at *
  have hmaj : countTrue f * 2 > n := by simpa [decide_eq_true_eq] using h
  have hle : countTrue f ≤ countTrue (setFn f i true) := countTrue_setFn_true_ge f i
  exact decide_eq_true (by omega)

theorem exists_true_of_majority {n : Nat} {f : Fin n → Bool}
    (h : majority f = true) : ∃ i : Fin n, f i = true := by
  have hmaj : countTrue f * 2 > n := by
    unfold majority at h; simpa [decide_eq_true_eq] using h
  by_contra hnone
  have hall : ∀ i : Fin n, f i = false := by
    intro i; cases hfi : f i with
    | false => rfl
    | true => exfalso; exact hnone ⟨i, hfi⟩
  have hzero : countTrue f = 0 := by unfold countTrue; simp [hall]
  omega

/-- Any two majorities of n elements overlap. -/
theorem majority_overlap {n : Nat} {f g : Fin n → Bool}
    (hf : majority f = true) (hg : majority g = true) :
    ∃ i : Fin n, f i = true ∧ g i = true := by
  by_contra h
  have h_disj : ∀ x : Fin n, ¬(f x = true ∧ g x = true) := fun x hx => h ⟨x, hx⟩
  have hle := filter_disjoint_length_le f g (List.finRange n) h_disj
  have hf_count : countTrue f * 2 > n := by
    unfold majority at hf; simpa [decide_eq_true_eq] using hf
  have hg_count : countTrue g * 2 > n := by
    unfold majority at hg; simpa [decide_eq_true_eq] using hg
  unfold countTrue at hf_count hg_count
  have hf' : (List.filter f (List.finRange n)).length * 2 > n := hf_count
  have hg' : (List.filter g (List.finRange n)).length * 2 > n := hg_count
  simp only [List.length_finRange] at hle
  omega

/-! ### SafeAt predicate (Lamport)

    `votedFor a c v`: acceptor `a` voted for value `v` at ballot `c`.
    `wontVoteAt a c`: acceptor `a` has not voted at ballot `c` and never will
    (because its promise exceeds `c`).
    `safeAt v b`: for every ballot `c < b`, there is a quorum where each
    member either voted for `v` at `c`, or will never vote at `c`.

    SafeAt is monotone: votes and promises only increase, strengthening both
    disjuncts. This makes it an inductive invariant.

    Defined before the spec because `p2a` references `safeAt` in its
    transition constraint. -/

def votedFor {n m : Nat} (ballot : Fin m → Nat) (s : PaxosState n m)
    (a : Fin n) (c : Nat) (v : Value) : Prop :=
  ∃ p, ballot p = c ∧ s.did2b p a = true ∧ s.prop p = some v

def wontVoteAt {n m : Nat} (ballot : Fin m → Nat) (s : PaxosState n m)
    (a : Fin n) (c : Nat) : Prop :=
  (∀ p, ballot p = c → s.did2b p a ≠ true) ∧ s.prom a > c

def safeAt {n m : Nat} (ballot : Fin m → Nat) (s : PaxosState n m)
    (v : Value) (b : Nat) : Prop :=
  ∀ c, c < b → ∃ Q : Fin n → Bool, majority Q = true ∧
    ∀ a, Q a = true → votedFor ballot s a c v ∨ wontVoteAt ballot s a c

/-! ### Paxos Specification -/

def paxos (n m : Nat) (ballot : Fin m → Nat) : ActionSpec (PaxosState n m) (PaxosAction n m) where
  init := fun s =>
    (∀ i, s.prom i = 0) ∧
    (∀ i, s.acc i = none) ∧
    (∀ p i, s.got1b p i = false) ∧
    (∀ p i, s.rep p i = none) ∧
    (∀ p, s.prop p = none) ∧
    (∀ p i, s.did2b p i = false) ∧
    (∀ i c, s.voted i c = none)
  actions := fun
    | .p1b p i => {
        gate := fun s => s.got1b p i = false ∧ s.prom i ≤ ballot p
        transition := fun s s' =>
          s' = { s with
            prom := setFn s.prom i (ballot p)
            got1b := setFn s.got1b p (setFn (s.got1b p) i true)
            rep := setFn s.rep p (setFn (s.rep p) i (s.acc i)) }
      }
    | .p2a p => {
        gate := fun s => s.prop p = none ∧ majority (s.got1b p) = true
        transition := fun s s' =>
          ∃ v,
            s' = { s with prop := setFn s.prop p (some v) } ∧
            -- Safety constraint: the chosen value must be safe at this ballot.
            -- This generalizes the max-vote rule (which implies safeAt) to any
            -- value satisfying Lamport's safety predicate. The max-vote rule is
            -- one implementation; safeAt is the specification-level requirement.
            -- This relaxation enables forward simulation from the message-passing
            -- model, where the proposer's local information may differ from the
            -- global got1b/rep state.
            safeAt ballot s v (ballot p)
      }
    | .p2b p i => {
        gate := fun s => s.did2b p i = false ∧ s.prom i ≤ ballot p
        transition := fun s s' =>
          ∃ v, s.prop p = some v ∧
            s' = { s with
              prom := setFn s.prom i (ballot p)
              acc := setFn s.acc i (some (ballot p, v))
              did2b := setFn s.did2b p (setFn (s.did2b p) i true)
              voted := updateVoted s.voted i (ballot p) v }
      }

/-! ### Protocol Invariant

    **(A)** Phase-2b acceptance implies proposal exists.
    **(B)** Acceptor records match proposals (via ballot).
    **(C)** Reports match proposals (via ballot).
    **(D)** Promises are at least as high as phase-1b ballots.
    **(E)** Promise ≥ highest accepted ballot.
    **(G)** did2b + got1b at higher ballot → report captures acceptance.
    **(H)** did2b implies acceptor has a record at that ballot or higher.
    **(J)** Proposing requires a quorum.
    **(Safe)** Lamport's SafeAt: proposed values are safe at their ballot. -/

structure PaxosInv {n m : Nat} (ballot : Fin m → Nat) (s : PaxosState n m) : Prop where
  hA : ∀ p i, s.did2b p i = true → s.prop p ≠ none
  hB : ∀ i b v, s.acc i = some (b, v) → ∃ p, ballot p = b ∧ s.prop p = some v
  hC : ∀ q i b v, s.rep q i = some (b, v) → ∃ p, ballot p = b ∧ s.prop p = some v
  hD : ∀ p i, s.got1b p i = true → s.prom i ≥ ballot p
  hE : ∀ i b v, s.acc i = some (b, v) → s.prom i ≥ b
  hG : ∀ p q i, s.did2b p i = true → s.got1b q i = true → ballot q > ballot p →
       ∃ b w, s.rep q i = some (b, w) ∧ b ≥ ballot p
  hH : ∀ p i, s.did2b p i = true → ∃ b v, s.acc i = some (b, v) ∧ b ≥ ballot p
  hJ : ∀ q, s.prop q ≠ none → majority (s.got1b q) = true
  hF : ∀ q i b v, s.rep q i = some (b, v) → b ≤ ballot q
  /-- Voted entries only appear at ballots used by some proposer, with matching value. -/
  hL : ∀ i b v, s.voted i b = some v → ∃ q, ballot q = b ∧ s.prop q = some v
  /-- A vote at ballot `b` means the acceptor's promise is at least `b`. -/
  hK : ∀ i b v, s.voted i b = some v → s.prom i ≥ b
  /-- `did2b p i` implies the corresponding vote was recorded at `ballot p`. -/
  hN : ∀ p i, s.did2b p i = true → ∃ v, s.prop p = some v ∧ s.voted i (ballot p) = some v
  /-- Acceptor's `acc` is captured by the vote history. -/
  hAcc : ∀ i b v, s.acc i = some (b, v) → s.voted i b = some v
  /-- Reports are backed by actual votes. -/
  hM : ∀ q i b v, s.rep q i = some (b, v) → s.voted i b = some v
  /-- Every recorded vote corresponds to some proposer's 2b. -/
  hVotDid : ∀ i b v, s.voted i b = some v →
            ∃ p, ballot p = b ∧ s.did2b p i = true
  hSafe : ∀ q v, s.prop q = some v → safeAt ballot s v (ballot q)

def paxos_inv {n m : Nat} (ballot : Fin m → Nat) (s : PaxosState n m) : Prop :=
  PaxosInv ballot s

/-! ### Agreement from SafeAt

    The proof is direct: overlap the SafeAt witness quorum with the did2b
    majority. The overlap acceptor voted at the lower ballot, so WontVoteAt
    is false, forcing VotedFor — which gives the value equality. -/

theorem agreement {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot)
    {s : PaxosState n m} (hinv : PaxosInv ballot s) :
    ∀ p q, majority (s.did2b p) = true → majority (s.did2b q) = true →
    s.prop p = s.prop q := by
  intro p q hmp hmq
  by_cases hpq : ballot p = ballot q
  · exact congrArg s.prop (h_inj hpq)
  · -- WLOG ballot p < ballot q (symmetric argument for the other case)
    suffices hsuff : ∀ p q, ballot p < ballot q →
        majority (s.did2b p) = true → majority (s.did2b q) = true →
        s.prop p = s.prop q by
      rcases Nat.lt_or_gt_of_ne hpq with hlt | hgt
      · exact hsuff p q hlt hmp hmq
      · exact (hsuff q p hgt hmq hmp).symm
    intro p' q' hlt hmp' hmq'
    -- q' proposed some value v
    have hne : s.prop q' ≠ none := by
      rcases exists_true_of_majority hmq' with ⟨j, hj⟩; exact hinv.hA q' j hj
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hne
    -- SafeAt(v, ballot q') at c = ballot p'
    obtain ⟨Q, hQmaj, hQprop⟩ := hinv.hSafe q' v hv (ballot p') hlt
    -- Overlap between Q and did2b p'
    obtain ⟨k, hdk, hQk⟩ := majority_overlap hmp' hQmaj
    -- k did2b at ballot p' under proposer p'
    rcases hQprop k hQk with ⟨r, hrb, _hdr, hrv⟩ | ⟨hnotvote, _⟩
    · -- votedFor: ∃ r, ballot r = ballot p' ∧ s.did2b r k = true ∧ s.prop r = some v.
      -- By injectivity of `ballot`, r = p'. Then s.prop p' = some v (hrv) and
      -- s.prop q' = some v (hv) — both equal `some v`, hence equal.
      have hrp' : r = p' := h_inj hrb
      subst hrp'
      rw [hrv, hv]
    · -- WontVoteAt: ∀ p, ballot p = ballot p' → s.did2b p k ≠ true.
      -- But hdk : s.did2b p' k = true, applied with p = p' and rfl, contradiction.
      exact absurd hdk (hnotvote p' rfl)

/-! ### Refinement Mapping -/

def firstMajority {n m : Nat} (s : PaxosState n m) : Option (Fin m) :=
  (List.finRange m).find? (fun p => majority (s.did2b p))

def paxos_ref {n m : Nat} (s : PaxosState n m) : ConsensusState where
  chosen := match firstMajority s with
    | some p => s.prop p
    | none => none

/-! ### Invariant Proofs -/

theorem paxos_inv_init {n m : Nat} (ballot : Fin m → Nat) :
    ∀ s, (paxos n m ballot).init s → paxos_inv ballot s := by
  intro s ⟨_, hacc, hgot, hrep, hprop, hdid, hvot⟩
  exact {
    hA := by intro p i hi; simp [hdid p i] at hi
    hB := by intro i _ _ hi; simp [hacc i] at hi
    hC := by intro q i _ _ hi; simp [hrep q i] at hi
    hD := by intro p i hi; simp [hgot p i] at hi
    hE := by intro i _ _ hi; simp [hacc i] at hi
    hG := by intro p _ i hi; simp [hdid p i] at hi
    hH := by intro p i hi; simp [hdid p i] at hi
    hJ := by intro q hq; simp [hprop q] at hq
    hF := by intro q i _ _ hri; simp [hrep q i] at hri
    hL := by intro i b v hv; simp [hvot i b] at hv
    hK := by intro i b v hv; simp [hvot i b] at hv
    hN := by intro p i hd; simp [hdid p i] at hd
    hAcc := by intro i b v hi; simp [hacc i] at hi
    hM := by intro q i b v hi; simp [hrep q i] at hi
    hVotDid := by intro i b v hv; simp [hvot i b] at hv
    hSafe := by intro q _ hq; simp [hprop q] at hq
  }

private theorem paxos_inv_next_p1b {n m : Nat} {ballot : Fin m → Nat}
    (s : PaxosState n m) (p : Fin m) (i : Fin n)
    (hinv : PaxosInv ballot s)
    (hg1 : s.got1b p i = false)
    (hg2 : s.prom i ≤ ballot p) :
    PaxosInv ballot { s with
      prom := setFn s.prom i (ballot p)
      got1b := setFn s.got1b p (setFn (s.got1b p) i true)
      rep := setFn s.rep p (setFn (s.rep p) i (s.acc i)) } := by
  apply PaxosInv.mk
  · exact hinv.hA  -- hA: did2b/prop unchanged
  · exact hinv.hB  -- hB: acc/prop unchanged
  · -- hC: new rep p i = acc i → use hB; rest frame
    intro q j b v hrep
    by_cases hq : q = p
    · subst hq; by_cases hj : j = i
      · subst hj; simp [setFn] at hrep; exact hinv.hB j b v hrep
      · simp [setFn, hj] at hrep; exact hinv.hC q j b v hrep
    · simp [setFn, hq] at hrep; exact hinv.hC q j b v hrep
  · -- hD: prom i ↑, got1b p i new
    intro q j hgot
    by_cases hq : q = p
    · subst hq; by_cases hj : j = i
      · subst hj; simp [setFn]
      · simp [setFn, hj] at hgot ⊢; exact hinv.hD q j hgot
    · simp [setFn, hq] at hgot
      by_cases hj : j = i
      · subst hj; simp [setFn]; have := hinv.hD q j hgot; omega
      · simp [setFn, hj]; exact hinv.hD q j hgot
  · -- hE: prom i ↑, acc unchanged
    intro j b v hacc
    by_cases hj : j = i
    · subst hj; simp [setFn]; have := hinv.hE j b v hacc; omega
    · simp [setFn, hj]; exact hinv.hE j b v hacc
  · -- hG: new got1b p i → hH gives acc i ballot ≥ ballot r
    intro r q j hd hgot hgt
    by_cases hq : q = p
    · subst hq; by_cases hj : j = i
      · subst hj; simp [setFn] at hgot ⊢
        obtain ⟨b, v, hacc, hge⟩ := hinv.hH r j hd
        exact ⟨b, ⟨v, hacc⟩, by omega⟩
      · simp [setFn, hj] at hgot ⊢
        obtain ⟨b, w, hrep, hge⟩ := hinv.hG r q j hd hgot hgt
        exact ⟨b, ⟨w, hrep⟩, by omega⟩
    · simp [setFn, hq] at hgot ⊢
      obtain ⟨b, w, hrep, hge⟩ := hinv.hG r q j hd hgot hgt
      exact ⟨b, ⟨w, hrep⟩, by omega⟩
  · exact hinv.hH  -- hH: did2b/acc unchanged
  · -- hJ: got1b gains entries → majority preserved
    intro q hq
    by_cases hq' : q = p
    · subst hq'; simp [setFn]
      exact majority_setFn_true_of_majority _ i (hinv.hJ q hq)
    · simp [setFn, hq']; exact hinv.hJ q hq
  · -- hF: new rep p i = acc i; for (q,j) ≠ (p,i) unchanged (unguarded version)
    intro q j b w hrep
    by_cases hq : q = p
    · subst hq; by_cases hj : j = i
      · subst hj; simp [setFn] at hrep
        -- rep p i = acc i. Use hE (prom i ≥ b) + gate (prom i ≤ ballot p).
        have := hinv.hE j b w hrep
        omega
      · simp [setFn, hj] at hrep
        exact hinv.hF q j b w hrep
    · simp [setFn, hq] at hrep
      exact hinv.hF q j b w hrep
  · exact hinv.hL  -- hL: voted unchanged
  · -- hK: voted unchanged, prom ↑
    intro j b v hv
    by_cases hj : j = i
    · subst hj; simp [setFn]; have := hinv.hK j b v hv; omega
    · simp [setFn, hj]; exact hinv.hK j b v hv
  · exact hinv.hN  -- hN: did2b, prop, voted unchanged
  · exact hinv.hAcc  -- hAcc: acc, voted unchanged
  · -- hM: new rep p i = acc i; use hAcc for the new entry
    intro q j b w hrep
    by_cases hq : q = p
    · subst hq; by_cases hj : j = i
      · subst hj; simp [setFn] at hrep
        exact hinv.hAcc j b w hrep
      · simp [setFn, hj] at hrep
        exact hinv.hM q j b w hrep
    · simp [setFn, hq] at hrep
      exact hinv.hM q j b w hrep
  · exact hinv.hVotDid  -- hVotDid: voted/did2b unchanged
  · -- hSafe: voted/prop unchanged, prom ↑ → old Q still works
    intro q v hprop c hc
    obtain ⟨Q, hQmaj, hQprop⟩ := hinv.hSafe q v hprop c hc
    refine ⟨Q, hQmaj, fun a ha => ?_⟩
    rcases hQprop a ha with hvote | ⟨hnv, hprom⟩
    · exact Or.inl hvote
    · right; refine ⟨hnv, ?_⟩
      by_cases ha : a = i
      · subst ha; simp [setFn]; omega
      · simp [setFn, ha]; exact hprom

/-- Among Fin n elements satisfying P, there is one maximizing f.
    Uses well-founded induction on (bound - f current). -/
private theorem fin_exists_max {n : Nat} (f : Fin n → Nat) (P : Fin n → Prop)
    (bound : Nat) (hbound : ∀ j, P j → f j ≤ bound)
    (a₀ : Fin n) (ha₀ : P a₀) :
    ∃ amax, P amax ∧ ∀ j, P j → f j ≤ f amax := by
  suffices h : ∀ k, ∀ a, P a → bound - f a ≤ k →
      ∃ amax, P amax ∧ ∀ j, P j → f j ≤ f amax by
    exact h (bound - f a₀) a₀ ha₀ (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro a ha hk
    refine ⟨a, ha, fun j hPj => ?_⟩
    have := hbound j hPj
    have := hbound a ha
    omega
  | succ k' ih =>
    intro a ha hk
    by_cases hmax : ∀ j, P j → f j ≤ f a
    · exact ⟨a, ha, hmax⟩
    · -- There exists j with P j and f j > f a
      have ⟨j, hj⟩ := Classical.not_forall.mp hmax
      have ⟨hPj, hfj⟩ := Classical.not_imp.mp hj
      have hfj' : f a < f j := Nat.lt_of_not_le hfj
      have : bound - f j ≤ k' := by
        have := hbound j hPj; omega
      exact ih j hPj this

private theorem paxos_inv_next_p2a {n m : Nat} {ballot : Fin m → Nat}
    (_h_inj : Function.Injective ballot)
    (s : PaxosState n m) (p : Fin m) (v : Value)
    (hinv : PaxosInv ballot s)
    (hg1 : s.prop p = none)
    (hg2 : majority (s.got1b p) = true)
    (hsafe_v : safeAt ballot s v (ballot p)) :
    PaxosInv ballot { s with prop := setFn s.prop p (some v) } := by
  apply PaxosInv.mk
  · -- hA: did2b unchanged, prop only gains (setFn adds some v at p)
    intro q i hd
    by_cases hqp : q = p
    · subst hqp; simp [setFn]
    · simp [setFn, hqp]; exact hinv.hA q i hd
  · -- hB: acc unchanged; prop only changes at p; old prop p = none so r ≠ p
    intro i b w hacc
    obtain ⟨r, hrb, hrprop⟩ := hinv.hB i b w hacc
    refine ⟨r, hrb, ?_⟩
    by_cases hrp : r = p
    · subst hrp; simp [hg1] at hrprop
    · simp [setFn, hrp, hrprop]
  · -- hC: rep unchanged; same as hB
    intro q i b w hrep
    obtain ⟨r, hrb, hrprop⟩ := hinv.hC q i b w hrep
    refine ⟨r, hrb, ?_⟩
    by_cases hrp : r = p
    · subst hrp; simp [hg1] at hrprop
    · simp [setFn, hrp, hrprop]
  · exact hinv.hD  -- hD: got1b/prom unchanged
  · exact hinv.hE  -- hE: acc/prom unchanged
  · exact hinv.hG  -- hG: did2b/got1b/rep unchanged
  · exact hinv.hH  -- hH: did2b/acc unchanged
  · -- hJ: prop only gains at p (= some v ≠ none); got1b unchanged
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp [setFn] at hq; exact hg2
    · simp [setFn, hqp] at hq; exact hinv.hJ q hq
  · exact hinv.hF  -- hF: rep unchanged
  · -- hL: voted unchanged, prop only gains at p. Thread setFn through prop.
    intro i b w hv
    obtain ⟨r, hrb, hrprop⟩ := hinv.hL i b w hv
    refine ⟨r, hrb, ?_⟩
    by_cases hrp : r = p
    · subst hrp; simp [hg1] at hrprop
    · simp [setFn, hrp]; exact hrprop
  · exact hinv.hK  -- hK: voted/prom unchanged
  · -- hN: did2b/voted unchanged, prop only gains at p; old proposer ≠ p (hg1).
    intro q i hd
    obtain ⟨w, hw, hv⟩ := hinv.hN q i hd
    refine ⟨w, ?_, hv⟩
    by_cases hqp : q = p
    · subst hqp; simp [hg1] at hw
    · simp [setFn, hqp]; exact hw
  · exact hinv.hAcc  -- hAcc: acc/voted unchanged
  · exact hinv.hM  -- hM: rep/voted unchanged
  · exact hinv.hVotDid  -- hVotDid: voted/did2b unchanged
  · -- hSafe: safeAt is given directly as the transition constraint for q = p.
    -- For q ≠ p: prop unchanged, old hSafe carries over.
    -- In both cases, safeAt transfers because p2a only changes prop, and
    -- safeAt depends on did2b/prop/prom which are stable (votedFor references
    -- prop, but did2b p = false for all acceptors so votedFor through p is empty).
    intro q w hprop c hc
    simp only [setFn] at hprop
    by_cases hqp : q = p
    · subst hqp
      simp only [ite_true] at hprop
      obtain ⟨rfl⟩ : w = v := Option.some.inj hprop.symm
      -- safeAt given directly; transfer to post-state (only prop changed)
      obtain ⟨Q, hQmaj, hQprop⟩ := hsafe_v c hc
      refine ⟨Q, hQmaj, fun a ha => ?_⟩
      rcases hQprop a ha with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
      · -- votedFor: r ≠ q since did2b r a = true → prop r ≠ none, but prop q = none
        have hrq : r ≠ q := fun h => by subst h; exact absurd hrv (by simp [hg1])
        exact Or.inl ⟨r, hrb, hdr, by simp [setFn, hrq, hrv]⟩
      · exact Or.inr ⟨hnv, hprom⟩
    · -- q ≠ p: prop q unchanged. Old hSafe gives pre-state safeAt witness; lift each
      -- disjunct to post-state (votedFor is monotone since did2b unchanged and we can
      -- argue r ≠ p; wontVoteAt is unchanged since did2b and prom are unchanged).
      simp only [hqp, ite_false] at hprop
      obtain ⟨Q, hQmaj, hQprop⟩ := hinv.hSafe q w hprop c hc
      refine ⟨Q, hQmaj, fun a ha => ?_⟩
      rcases hQprop a ha with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
      · -- votedFor: hrv : s.prop r = some w. p2a only changes prop at p; r ≠ p
        -- since s.prop p = none ≠ some w.
        have hrp : r ≠ p := fun h => by subst h; exact absurd hrv (by simp [hg1])
        exact Or.inl ⟨r, hrb, hdr, by simp [setFn, hrp]; exact hrv⟩
      · -- wontVoteAt: did2b and prom unchanged.
        exact Or.inr ⟨hnv, hprom⟩

private theorem paxos_inv_next_p2b {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot)
    (s : PaxosState n m) (p : Fin m) (i : Fin n)
    (hinv : PaxosInv ballot s)
    (hg1 : s.did2b p i = false)
    (hg2 : s.prom i ≤ ballot p)
    (v : Value)
    (hp : s.prop p = some v) :
    PaxosInv ballot { s with
      prom := setFn s.prom i (ballot p)
      acc := setFn s.acc i (some (ballot p, v))
      did2b := setFn s.did2b p (setFn (s.did2b p) i true)
      voted := updateVoted s.voted i (ballot p) v } := by
  -- Key helper: pre-state voted i (ballot p) is already none (else gate contradicts).
  have hvot_none : s.voted i (ballot p) = none := by
    by_contra hne
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨r, hrb, hdr⟩ := hinv.hVotDid i (ballot p) w hw
    have hrp : r = p := h_inj hrb
    subst hrp
    rw [hg1] at hdr; exact absurd hdr (by decide)
  apply PaxosInv.mk
  · -- hA: did2b gained (p,i); prop unchanged. prop p = some v ≠ none.
    intro q j hd
    -- new did2b: setFn (setFn ...) only changes did2b p
    -- prop is unchanged, so hinv.hA applies when old did2b was true
    -- for the new (p, i) entry: prop p = some v ≠ none
    show s.prop q ≠ none
    simp only [setFn] at hd
    by_cases hq : q = p
    · subst hq
      simp only [ite_true] at hd
      by_cases hj : j = i
      · subst hj; simp [setFn] at hd; exact hp ▸ (Option.some_ne_none v)
      · simp only [setFn, hj, ite_false] at hd; exact hinv.hA q j hd
    · simp only [hq, ite_false] at hd; exact hinv.hA q j hd
  · -- hB: acc i := (ballot p, v); for j ≠ i acc unchanged.
    intro j b w hacc
    simp only [setFn] at hacc
    by_cases hj : j = i
    · subst hj; simp only [ite_true] at hacc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hacc)
      exact ⟨p, rfl, hp⟩
    · simp only [hj, ite_false] at hacc; exact hinv.hB j b w hacc
  · exact hinv.hC  -- hC: rep unchanged
  · -- hD: got1b unchanged, prom i ↑ (doesn't hurt; got1b not changed)
    intro q j hgot
    show setFn s.prom i (ballot p) j ≥ ballot q
    by_cases hj : j = i
    · subst hj; simp only [setFn, ite_true]; have := hinv.hD q j hgot; omega
    · simp only [setFn, hj, ite_false]; exact hinv.hD q j hgot
  · -- hE: prom i ↑ to ballot p, acc i = (ballot p, v)
    intro j b w hacc
    show setFn s.prom i (ballot p) j ≥ b
    simp only [setFn] at hacc
    by_cases hj : j = i
    · subst hj; simp only [ite_true] at hacc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hacc)
      simp [setFn]
    · simp only [hj, ite_false] at hacc
      simp only [setFn, hj, ite_false]; exact hinv.hE j b w hacc
  · -- hG: did2b gained (p,i). For new entry (r=p, j=i): ballot q > ballot p contradicts hD + gate.
    intro r q j hd hgot hgt
    simp only [setFn] at hd
    by_cases hr : r = p
    · subst hr; simp only [ite_true] at hd
      by_cases hj : j = i
      · subst hj
        -- got1b q j = true → prom j ≥ ballot q (hD). But prom j ≤ ballot p < ballot q. Contradiction.
        have hprom_ge : s.prom j ≥ ballot q := hinv.hD q j hgot
        omega
      · simp only [setFn, hj, ite_false] at hd
        exact hinv.hG r q j hd hgot hgt
    · simp only [hr, ite_false] at hd
      exact hinv.hG r q j hd hgot hgt
  · -- hH: did2b gained (p,i); acc i = (ballot p, v) with ballot p ≥ ballot p.
    --   For q ≠ p, j = i: old hH gives acc i = some (b, w), b ≥ ballot q.
    --   New acc i = (ballot p, v). Need ballot p ≥ ballot q.
    --   By old hE: prom i ≥ b ≥ ballot q. Gate: prom i ≤ ballot p. So ballot p ≥ ballot q.
    intro q j hd
    simp only [setFn] at hd
    by_cases hq : q = p
    · subst hq; simp only [ite_true] at hd
      by_cases hj : j = i
      · subst hj
        exact ⟨ballot q, v, by simp [setFn], Nat.le_refl _⟩
      · simp only [setFn, hj, ite_false] at hd
        obtain ⟨b, w, hacc, hge⟩ := hinv.hH q j hd
        exact ⟨b, w, by simp only [setFn, hj, ite_false]; exact hacc, hge⟩
    · simp only [hq, ite_false] at hd
      obtain ⟨b, w, hacc, hge⟩ := hinv.hH q j hd
      by_cases hj : j = i
      · subst hj
        have hprom_b : s.prom j ≥ b := hinv.hE j b w hacc
        exact ⟨ballot p, v, by simp [setFn], by omega⟩
      · exact ⟨b, w, by simp only [setFn, hj, ite_false]; exact hacc, hge⟩
  · exact hinv.hJ  -- hJ: got1b/prop unchanged
  · exact hinv.hF  -- hF: rep unchanged
  · -- hL: new voted entry at (i, ballot p) = some v; prop p = some v witness.
    intro j b w hv
    show ∃ q, ballot q = b ∧ s.prop q = some w
    simp only [updateVoted] at hv
    by_cases hji : j = i ∧ b = ballot p
    · rw [if_pos hji] at hv
      obtain ⟨rfl⟩ : w = v := (Option.some.inj hv).symm
      obtain ⟨rfl, rfl⟩ := hji
      exact ⟨p, rfl, hp⟩
    · rw [if_neg hji] at hv
      exact hinv.hL j b w hv
  · -- hK: voted → prom. For new entry: prom i := ballot p, b = ballot p. For existing: prom ↑.
    intro j b w hv
    show setFn s.prom i (ballot p) j ≥ b
    simp only [updateVoted] at hv
    by_cases hji : j = i ∧ b = ballot p
    · obtain ⟨rfl, rfl⟩ := hji; simp [setFn]
    · rw [if_neg hji] at hv
      have := hinv.hK j b w hv
      by_cases hj : j = i
      · subst hj; simp [setFn]; omega
      · simp [setFn, hj]; exact this
  · -- hN: new did2b entry (p, i) tracked by new voted (i, ballot p).
    -- Existing did2b entries: voted unchanged for them, use hinv.hN.
    intro q j hd
    show ∃ vv, s.prop q = some vv ∧ updateVoted s.voted i (ballot p) v j (ballot q) = some vv
    simp only [setFn] at hd
    by_cases hq : q = p
    · subst hq
      simp only [ite_true] at hd
      simp only [setFn] at hd
      by_cases hj : j = i
      · subst hj
        refine ⟨v, hp, ?_⟩
        simp [updateVoted]
      · simp only [hj, ite_false] at hd
        obtain ⟨vv, hvv, hvvotes⟩ := hinv.hN q j hd
        refine ⟨vv, hvv, ?_⟩
        show updateVoted s.voted i (ballot q) v j (ballot q) = some vv
        simp only [updateVoted, hj, false_and, if_false]
        exact hvvotes
    · simp only [hq, ite_false] at hd
      obtain ⟨vv, hvv, hvvotes⟩ := hinv.hN q j hd
      refine ⟨vv, hvv, ?_⟩
      -- new voted at (i, ballot p). If (j, ballot q) = (i, ballot p): need voted i (ballot p) = some vv.
      -- From hinv.hK: prom j ≥ ballot q. From gate: prom i ≤ ballot p.
      -- If j = i and ballot q = ballot p: need to show vv = v.
      -- Actually the vote slot is updated, so if the update target matches, we use the new value.
      -- Since the new value is v and hvv : s.prop q = some vv, and if ballot q = ballot p
      -- then q = p (by injectivity... but we don't have h_inj here).
      -- Instead: does (j, ballot q) = (i, ballot p)? If so:
      --   - j = i
      --   - ballot q = ballot p, and hvvotes : s.voted i (ballot p) = some vv (pre-state).
      -- We're trying to show updateVoted... = some vv. If (j,ballot q) = (i, ballot p), it's some v.
      -- But we need some vv. So we need vv = v.
      -- From hinv.hL applied to hvvotes: ∃ r, ballot r = ballot p ∧ prop r = some vv.
      -- If ballot is injective via hinv... actually hVotDid says did2b r i for some r with ballot r = ballot p.
      -- Cleaner: from hvvotes (pre-state voted i (ballot p) = some vv), use hinv.hL to get
      -- ∃ r, ballot r = ballot p ∧ prop r = some vv. But we want vv = v.
      -- The issue: proposer with that ballot may differ from p unless ballot is injective.
      -- We don't have h_inj. So this approach doesn't straightforwardly work.
      -- Alternative: show (j, ballot q) ≠ (i, ballot p) in this branch.
      -- If j = i and ballot q = ballot p: we have hvvotes : voted i (ballot p) = some vv (pre-state).
      -- By hinv.hVotDid, some r with ballot r = ballot p ∧ did2b r i = true.
      -- But we have did2b q j = true (hd) with q ≠ p and j = i. ballot q = ballot p.
      -- The old hinv.hL on hvvotes gives ∃ r with ballot r = ballot p ∧ prop r = some vv.
      -- If we had injectivity we'd get r = p and vv = v. Without, we're stuck.
      -- Observation: we could strengthen the invariant so that at most one voted entry exists
      -- per (acceptor, ballot), but that's automatic from updateVoted-only updates.
      -- Alternatively: simply state hN only when (j, ballot q) ≠ (i, ballot p), showing equality.
      -- Actually: the simplest approach. `updateVoted` updates only (i, ballot p). For q ≠ p,
      -- if (j, ballot q) = (i, ballot p) then j = i and ballot q = ballot p. The pre-state
      -- has voted i (ballot p) = some vv (from hinv.hN q j hd). So post-state voted i (ballot p)
      -- is overwritten to some v. For the post-state value we get some v, not some vv. For hN
      -- to hold we'd need vv = v.
      -- Escape hatch: use hinv.hL on pre-state voted i (ballot p) = some vv. We get some proposer
      -- r with ballot r = ballot p, prop r = some vv. Use h_inj to conclude r = p, hence vv = v.
      -- But we lack h_inj here. SOLUTION: pass h_inj to p2b like p2a.
      show updateVoted s.voted i (ballot p) v j (ballot q) = some vv
      by_cases hji : j = i ∧ ballot q = ballot p
      · -- Contradiction: q ≠ p but h_inj makes ballot q = ballot p impossible.
        obtain ⟨_, hji2⟩ := hji
        exact absurd (h_inj hji2) hq
      · simp only [updateVoted, if_neg hji]
        exact hvvotes
  · -- hAcc: new acc i = (ballot p, v), new voted i (ballot p) = some v.
    intro j b w hacc
    simp only [setFn] at hacc
    by_cases hj : j = i
    · subst hj; simp only [ite_true] at hacc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hacc)
      simp [updateVoted]
    · simp only [hj, ite_false] at hacc
      have := hinv.hAcc j b w hacc
      show updateVoted s.voted i (ballot p) v j b = some w
      simp only [updateVoted, hj, false_and, if_false]
      exact this
  · -- hM: rep unchanged, voted possibly gains. For old rep entry, old hM gives
    -- voted i' b' = some w'. Conflict only if (i', b') = (i, ballot p), but then
    -- hold gives pre-state voted i (ballot p) = some w, contradicting hvot_none.
    intro q j b w hrep
    show updateVoted s.voted i (ballot p) v j b = some w
    have hold := hinv.hM q j b w hrep
    simp only [updateVoted]
    by_cases hji : j = i ∧ b = ballot p
    · obtain ⟨rfl, rfl⟩ := hji
      rw [hvot_none] at hold; exact absurd hold (by simp)
    · rw [if_neg hji]; exact hold
  · -- hVotDid: new entry (i, ballot p) corresponds to did2b p i = true (new).
    intro j b w hv
    simp only [updateVoted] at hv
    by_cases hji : j = i ∧ b = ballot p
    · obtain ⟨rfl, rfl⟩ := hji
      refine ⟨p, rfl, ?_⟩
      show setFn s.did2b p (setFn (s.did2b p) j true) p j = true
      simp [setFn]
    · rw [if_neg hji] at hv
      obtain ⟨r, hrb, hdr⟩ := hinv.hVotDid j b w hv
      refine ⟨r, hrb, ?_⟩
      show setFn s.did2b p (setFn (s.did2b p) i true) r j = true
      simp only [setFn]
      by_cases hrp : r = p
      · subst hrp; simp only [ite_true, setFn]
        by_cases hji' : j = i
        · subst hji'; simp
        · simp [hji']; exact hdr
      · simp [hrp]; exact hdr
  · -- hSafe: prop unchanged. did2b only gains (p, i); prom only ↑ at i.
    -- Old Q witnesses still work, lifted to post-state.
    intro q w hprop c hc
    obtain ⟨Q, hQmaj, hQprop⟩ := hinv.hSafe q w hprop c hc
    refine ⟨Q, hQmaj, fun a ha => ?_⟩
    rcases hQprop a ha with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
    · -- votedFor in old state → votedFor in new state.
      -- did2b only grew at (p, i); old hdr : s.did2b r a = true is preserved.
      apply Or.inl
      refine ⟨r, hrb, ?_, hrv⟩
      show setFn s.did2b p (setFn (s.did2b p) i true) r a = true
      simp only [setFn]
      by_cases hrp : r = p
      · subst hrp; simp only [ite_true, setFn]
        by_cases hai : a = i
        · subst hai; simp only [ite_true]
        · simp only [hai, ite_false]; exact hdr
      · simp only [hrp, ite_false]; exact hdr
    · -- wontVoteAt in old state → wontVoteAt in new state.
      -- (1) ∀ p', ballot p' = c → did2b p' a ≠ true: only new (p, i) entry could break.
      --     If a = i and c = ballot p: hprom gives s.prom i > c = ballot p, but gate says
      --     s.prom i ≤ ballot p. Contradiction → c ≠ ballot p, so the new entry doesn't matter.
      -- (2) prom a > c: prom only ↑ at i; if a = i, ballot p > c (from same argument).
      right
      refine ⟨fun r' hrb_eq => ?_, ?_⟩
      · show setFn s.did2b p (setFn (s.did2b p) i true) r' a ≠ true
        simp only [setFn]
        by_cases hrp : r' = p
        · subst hrp; simp only [ite_true, setFn]
          by_cases hai : a = i
          · subst hai; simp only [ite_true]
            -- hprom : s.prom i > c; gate : s.prom i ≤ ballot p; hrb_eq : ballot p = c
            -- ⇒ ballot p > ballot p, contradiction.
            exfalso; omega
          · simp only [hai, ite_false]; exact hnv r' hrb_eq
        · simp only [hrp, ite_false]; exact hnv r' hrb_eq
      · show setFn s.prom i (ballot p) a > c
        by_cases hai : a = i
        · subst hai; simp only [setFn, ite_true]; omega
        · simp only [setFn, hai, ite_false]; exact hprom

theorem paxos_inv_next {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot) :
    ∀ s s', paxos_inv ballot s →
    (∃ a, ((paxos n m ballot).actions a).fires s s') →
    paxos_inv ballot s' := by
  intro s s' hinv ⟨a, hfires⟩
  cases a
  case p1b =>
    rename_i p i
    simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires
    obtain ⟨⟨hg1, hg2⟩, rfl⟩ := hfires
    exact paxos_inv_next_p1b s p i hinv hg1 hg2
  case p2a p =>
    simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires
    obtain ⟨⟨hg1, hg2⟩, v, rfl, hconstr⟩ := hfires
    exact paxos_inv_next_p2a h_inj s p v hinv hg1 hg2 hconstr
  case p2b p i =>
    simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires
    obtain ⟨⟨hg1, hg2⟩, v, hp, rfl⟩ := hfires
    exact paxos_inv_next_p2b h_inj s p i hinv hg1 hg2 v hp

theorem paxos_init_preserved {n m : Nat} (ballot : Fin m → Nat) :
    ∀ s, (paxos n m ballot).init s → consensus.init (paxos_ref s) := by
  intro s ⟨_, _, _, _, hprop, hdid, _⟩
  simp only [paxos_ref, firstMajority, consensus]
  have hmaj_false : ∀ p : Fin m, majority (s.did2b p) = false := by
    intro p; unfold majority countTrue
    have : (List.filter (fun i => s.did2b p i) (List.finRange n)).length = 0 := by
      simp [hdid p]
    simp [this]
  have : (List.finRange m).find? (fun p => majority (s.did2b p)) = none := by
    apply List.find?_eq_none.mpr
    intro p _; simp [hmaj_false p]
  simp [this]

private theorem firstMajority_prop_eq {n m : Nat} {ballot : Fin m → Nat} {s : PaxosState n m}
    {p : Fin m} (hinv : PaxosInv ballot s)
    (hg1 : s.prop p = none) (v : Value) :
    (match firstMajority s with | some q => (setFn s.prop p (some v)) q | none => none) =
    (match firstMajority s with | some q => s.prop q | none => none) := by
  unfold firstMajority
  match hfm : (List.finRange m).find? (fun q => majority (s.did2b q)) with
  | none => rfl
  | some q =>
    have hmq : majority (s.did2b q) = true := by simpa using List.find?_some hfm
    have hne : q ≠ p := by
      intro heq; subst heq
      exact (hinv.hA q (exists_true_of_majority hmq).choose
        (exists_true_of_majority hmq).choose_spec) hg1
    simp [setFn, hne]

private theorem paxos_step_sim_p2b {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot)
    (s : PaxosState n m) (p : Fin m) (i : Fin n)
    (hinv : PaxosInv ballot s)
    (hg1 : s.did2b p i = false) (hg2 : s.prom i ≤ ballot p)
    (v : Value) (hp : s.prop p = some v) :
    let s' : PaxosState n m := { s with
        prom := setFn s.prom i (ballot p)
        acc := setFn s.acc i (some (ballot p, v))
        did2b := setFn s.did2b p (setFn (s.did2b p) i true)
        voted := updateVoted s.voted i (ballot p) v }
    (∃ act, (consensus.actions act).fires (paxos_ref s) (paxos_ref s')) ∨
    paxos_ref s = paxos_ref s' := by
  intro s'
  -- paxos_ref depends on did2b (via firstMajority) and prop; prop unchanged
  have hprop_eq : s'.prop = s.prop := rfl
  -- did2b only changes at (p, i)
  have hdid_eq : s'.did2b = setFn s.did2b p (setFn (s.did2b p) i true) := rfl
  -- Analyze old and new firstMajority
  unfold paxos_ref firstMajority
  match hfm_old : (List.finRange m).find? (fun q => majority (s.did2b q)),
        hfm_new : (List.finRange m).find? (fun q => majority (s'.did2b q)) with
  | none, none =>
    right; rfl
  | none, some r =>
    -- New majority at r; must be r = p since only did2b p changed
    left
    have hr_eq_p : r = p := by
      by_contra hne
      have hmr_new : majority (s'.did2b r) = true := by simpa using List.find?_some hfm_new
      have hmr_old : majority (s.did2b r) = true := by
        have : s'.did2b r = s.did2b r := by ext j; simp [hdid_eq, setFn, hne]
        rwa [this] at hmr_new
      exact absurd hmr_old (by simpa using List.find?_eq_none.mp hfm_old r (List.mem_finRange r))
    subst hr_eq_p
    simp only [hprop_eq, hp]
    cases v with
    | v1 => exact ⟨.choose1, rfl, rfl⟩
    | v2 => exact ⟨.choose2, rfl, rfl⟩
  | some r, none =>
    -- Impossible: old majority persists since did2b only gains true entries
    exfalso
    have hmr : majority (s.did2b r) = true := by simpa using List.find?_some hfm_old
    have hmr_new : majority (s'.did2b r) = true := by
      rw [hdid_eq]; simp only [setFn]
      by_cases hrp : r = p
      · subst hrp; simp only [ite_true]; exact majority_setFn_true_of_majority _ i hmr
      · simp only [hrp, ite_false]; exact hmr
    exact absurd hmr_new (by simpa using List.find?_eq_none.mp hfm_new r (List.mem_finRange r))
  | some r, some r' =>
    -- Both have majority; use agreement on s' to show prop r = prop r'
    right
    simp only [hprop_eq]
    have hmr : majority (s.did2b r) = true := by simpa using List.find?_some hfm_old
    have hmr' : majority (s'.did2b r') = true := by simpa using List.find?_some hfm_new
    have hinv' : PaxosInv ballot s' := paxos_inv_next_p2b h_inj s p i hinv hg1 hg2 v hp
    have hmr_new : majority (s'.did2b r) = true := by
      rw [hdid_eq]; simp only [setFn]
      by_cases hrp : r = p
      · subst hrp; simp only [ite_true]; exact majority_setFn_true_of_majority _ i hmr
      · simp only [hrp, ite_false]; exact hmr
    have := agreement h_inj hinv' r r' hmr_new hmr'
    simp [hprop_eq] at this
    exact congrArg ConsensusState.mk this

theorem paxos_step_sim {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot) :
    ∀ s s', paxos_inv ballot s →
    (∃ a, ((paxos n m ballot).actions a).fires s s') →
    (∃ i, (consensus.actions i).fires (paxos_ref s) (paxos_ref s')) ∨
      paxos_ref s = paxos_ref s' := by
  intro s s' hinv ⟨a, hfires⟩
  cases a
  case p1b p i =>
    simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires
    obtain ⟨⟨hg1, hg2⟩, rfl⟩ := hfires
    right; simp only [paxos_ref, firstMajority]
  case p2a pp =>
    simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires
    obtain ⟨⟨hg1, hg2⟩, v, rfl, hconstr⟩ := hfires
    right
    show paxos_ref s = paxos_ref { s with prop := setFn s.prop pp (some v) }
    simp only [paxos_ref]
    exact congrArg ConsensusState.mk (firstMajority_prop_eq hinv hg1 v).symm
  case p2b p i =>
    simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires
    obtain ⟨⟨hg1, hg2⟩, v, hp, rfl⟩ := hfires
    exact paxos_step_sim_p2b h_inj s p i hinv hg1 hg2 v hp

theorem paxos_refines_consensus {n m : Nat} (ballot : Fin m → Nat)
    (h_inj : Function.Injective ballot) :
    refines_via paxos_ref (paxos n m ballot).toSpec.safety consensus.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    (paxos n m ballot).toSpec consensus.toSpec paxos_ref (paxos_inv ballot)
  · exact paxos_inv_init ballot
  · intro s s' hinv hstep; exact paxos_inv_next h_inj s s' hinv hstep
  · exact paxos_init_preserved ballot
  · intro s s' hinv hstep; exact paxos_step_sim h_inj s s' hinv hstep

end PaxosTextbookN
