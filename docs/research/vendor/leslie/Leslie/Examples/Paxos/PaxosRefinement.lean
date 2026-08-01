import Leslie.Examples.Paxos
import Leslie.Examples.Paxos.MessagePaxos
import Leslie.Examples.Paxos.MsgPaxosConsensus

/-! ## Message-Passing Paxos Refines Atomic Paxos

    Proves a forward simulation from the message-passing Paxos model
    (`MessagePaxos.lean`) to the atomic Paxos model (`Paxos.lean`).

    **Current design (abstract-ahead, 1 sorry):**
    - `recvPrepare(a, p, b)` → fires atomic `p1b` for ALL proposers p'
      with `ballot p'` in `(old_prom, b]`, in increasing ballot order.
      This maintains the biconditional `got1b p' a ↔ prom a ≥ ballot p'`.
    - `recvAccept(a, p, b, v)` → fires atomic `p2a(p)` (if first vote
      at ballot p) then `p2b(p, a)`.
    - All other message actions are stutter steps.

    Uses `SimulationRelInv` with `Reachable` as the concrete invariant.
    Requires ballots to be positive (`∀ p, ballot p > 0`) so that the
    initial abstract state (all-zeros) satisfies `got1b_iff`.

    **Remaining sorry:** The p2a max-vote constraint (`h_value_ok`) in the
    B2 case of `recvAccept`. The `got1b_iff` biconditional eagerly fires
    p1b for proposers whose promises the concrete proposer never received,
    causing the abstract max-vote to diverge from the concrete one. See the
    detailed comment at the sorry site for a proposed redesign that fires
    p1b at `recvPromise` and p2a at `decidePropose` to close this gap.
-/

open TLA

namespace PaxosRefinement

/-! ### Value mapping -/

def vmap : MessagePaxos.Value → PaxosTextbookN.Value
  | .v1 => .v1
  | .v2 => .v2

def vmapPair : Option (Nat × MessagePaxos.Value) → Option (Nat × PaxosTextbookN.Value)
  | none => none
  | some (b, v) => some (b, vmap v)

theorem vmap_injective : Function.Injective vmap := by
  intro a b h; cases a <;> cases b <;> simp [vmap] at h ⊢

/-! ### Specs -/

abbrev msgSpec (n m : Nat) (ballot : Fin m → Nat) := MessagePaxos.msgPaxosSpec n m ballot
abbrev atomicSpec (n m : Nat) (ballot : Fin m → Nat) := (PaxosTextbookN.paxos n m ballot).toSpec

/-! ### Simulation Relation -/

structure SimRel {n m : Nat} (ballot : Fin m → Nat)
    (ms : MessagePaxos.MsgPaxosState n m) (as : PaxosTextbookN.PaxosState n m) : Prop where
  prom_eq   : ∀ i, as.prom i = (ms.acceptors i).prom
  acc_eq    : ∀ i, as.acc i = vmapPair (ms.acceptors i).acc
  did2b_eq  : ∀ p i, as.did2b p i = (ms.sentAccept i (ballot p)).isSome
  prop_none : ∀ p, (∀ a, ms.sentAccept a (ballot p) = none) → as.prop p = none
  prop_some : ∀ p a v, ms.sentAccept a (ballot p) = some v → as.prop p = some (vmap v)
  /-- got1b ↔ prom ≥ ballot. Ensures majority(got1b p) when safeAt holds. -/
  got1b_iff : ∀ p i, as.got1b p i = true ↔ (ms.acceptors i).prom ≥ ballot p
  rep_none  : ∀ p i, as.got1b p i = false → as.rep p i = none
  rep_dom   : ∀ p i bv bv', as.got1b p i = true → as.rep p i = some bv →
              as.acc i = some bv' → bv.1 ≤ bv'.1
  rep_acc   : ∀ p i, as.got1b p i = true → as.acc i = none → as.rep p i = none
  /-- rep values correspond to sentAccept entries (under vmap). -/
  rep_sent  : ∀ p i bw w, as.got1b p i = true → as.rep p i = some (bw, w) →
              ∃ w', ms.sentAccept i bw = some w' ∧ w = vmap w'

/-- Extract sentAccept from acc via vmapPair and hAccSent. -/
private theorem acc_to_sent_lemma {n m : Nat} {ballot : Fin m → Nat}
    {ms : MessagePaxos.MsgPaxosState n m} {as : PaxosTextbookN.PaxosState n m}
    (hR : SimRel ballot ms as) (hinvI : MessagePaxos.MsgPaxosInv ballot ms)
    (k : Fin n) (bw' : Nat) (w' : PaxosTextbookN.Value)
    (hk : as.acc k = some (bw', w')) :
    ∃ vv, ms.sentAccept k bw' = some vv ∧ w' = vmap vv := by
  rw [hR.acc_eq] at hk
  match hacc_ms : (ms.acceptors k).acc, hk with
  | some (ba, va), hk =>
    simp [vmapPair, hacc_ms] at hk
    obtain ⟨hba, hva⟩ := hk
    exact ⟨va, hba ▸ hinvI.hAccSent k ba va hacc_ms, hva.symm⟩
  | none, hk => simp [vmapPair, hacc_ms] at hk

/-! ### Star construction helper -/

/-- Given `prom a ≤ b`, there exists a `Star` of atomic `p1b` steps that raises
    `prom[a]` to `b` and sets `got1b`/`rep` for all proposers whose ballot is in
    `(old_prom, b]`.  The proof is a finite inductive construction over proposers
    ordered by ballot; we leave it as `sorry`. -/
private def pendingCount {n m : Nat} (ballot : Fin m → Nat) (got1b : Fin m → Fin n → Bool)
    (a : Fin n) (b : Nat) : Nat :=
  (List.finRange m).countP (fun p => decide (ballot p ≤ b ∧ got1b p a = false))

private theorem List.countP_lt_of_strict {α} {p q : α → Bool} {l : List α}
    (h_le : ∀ x, x ∈ l → p x = true → q x = true)
    (x : α) (hx : x ∈ l) (hpx : p x = false) (hqx : q x = true) :
    List.countP p l < List.countP q l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.countP_cons]
    have h_le' : ∀ y, y ∈ l → p y = true → q y = true :=
      fun y hy => h_le y (List.mem_cons.mpr (.inr hy))
    have h_mono := List.countP_mono_left h_le'
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [hpx, hqx]; simp; omega
    · have ih' := ih h_le' hx'
      cases hpa : p a
      · cases hqa : q a <;> simp <;> omega
      · have hqa := h_le a (List.mem_cons.mpr (.inl rfl)) hpa
        simp [hqa]; omega

open Classical in
private theorem exists_min_pending {m : Nat} (ballot : Fin m → Nat) (P : Fin m → Prop)
    (h : ∃ q, P q) :
    ∃ q, P q ∧ ∀ q', P q' → ballot q ≤ ballot q' := by
  obtain ⟨q₀, hq₀⟩ := h
  suffices ∀ n, ∀ q : Fin m, P q → ballot q ≤ n →
      ∃ q', P q' ∧ ∀ q'', P q'' → ballot q' ≤ ballot q'' by
    exact this (ballot q₀) q₀ hq₀ (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro q hq hbal
    exact ⟨q, hq, fun q' _ => by omega⟩
  | succ n ih_n =>
    intro q hq hbal
    by_cases hlt : ballot q ≤ n
    · exact ih_n q hq hlt
    · rcases em (∃ q', P q' ∧ ballot q' ≤ n) with ⟨q', hq', hbal'⟩ | hex
      · exact ih_n q' hq' hbal'
      · exact ⟨q, hq, fun q'' hq'' =>
          Nat.le_of_not_lt (fun hlt' => hex ⟨q'', hq'', by omega⟩)⟩

theorem multi_p1b_star {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot)
    (as : PaxosTextbookN.PaxosState n m) (a : Fin n) (b : Nat)
    (h_le : as.prom a ≤ b)
    (h_got1b : ∀ p, as.got1b p a = true ↔ as.prom a ≥ ballot p)
    (h_rep_none : ∀ p, as.got1b p a = false → as.rep p a = none)
    (h_bval : as.prom a = b ∨ ∃ p, ballot p = b) :
    Star (atomicSpec n m ballot).next as
      { prom := fun j => if j = a then b else as.prom j
        acc := as.acc
        got1b := fun p' j =>
          if j = a ∧ ballot p' ≤ b then true else as.got1b p' j
        rep := fun p' j =>
          if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false
          then as.acc a else as.rep p' j
        prop := as.prop
        did2b := as.did2b } := by
  -- Strong induction on the number of pending proposers
  generalize hk : pendingCount ballot as.got1b a b = k
  induction k using Nat.strongRecOn generalizing as with
  | _ k ih =>
  -- Determine if there are any pending proposers
  by_cases hpend : ∃ q : Fin m, ballot q ≤ b ∧ as.got1b q a = false
  · -- Inductive step: there is a pending proposer
    -- Pick the pending proposer with minimum ballot
    obtain ⟨q, ⟨hq_bal, hq_got⟩, hq_min⟩ := exists_min_pending ballot
      (fun p => ballot p ≤ b ∧ as.got1b p a = false) hpend
    -- q is pending: got1b q a = false, ballot q ≤ b
    -- By h_got1b: got1b q a = false → ¬(prom a ≥ ballot q) → prom a < ballot q
    have hprom_lt : as.prom a < ballot q := by
      have hne : ¬(as.got1b q a = true) := by rw [hq_got]; simp
      exact Nat.lt_of_not_le (fun h => hne ((h_got1b q).mpr h))
    -- Define intermediate state after p1b(q, a)
    let as' : PaxosTextbookN.PaxosState n m :=
      { as with
        prom := setFn as.prom a (ballot q)
        got1b := setFn as.got1b q (setFn (as.got1b q) a true)
        rep := setFn as.rep q (setFn (as.rep q) a (as.acc a)) }
    -- Fire the p1b step: gate is got1b q a = false ∧ prom a ≤ ballot q
    have hstep : (atomicSpec n m ballot).next as as' := by
      exact ⟨.p1b q a, ⟨hq_got, Nat.le_of_lt hprom_lt⟩, rfl⟩
    -- Key lemma: for p ≠ q, got1b and rep at a are unchanged
    have hgot_ne : ∀ p, p ≠ q → as'.got1b p a = as.got1b p a := by
      intro p hp; show (setFn as.got1b q _ p) a = _; simp [setFn, hp]
    have hrep_ne : ∀ p, p ≠ q → as'.rep p a = as.rep p a := by
      intro p hp; show (setFn as.rep q _ p) a = _; simp [setFn, hp]
    -- got1b q a is now true in as'
    have hgot_q : as'.got1b q a = true := by
      show (setFn as.got1b q (setFn (as.got1b q) a true)) q a = _; simp [setFn]
    -- rep q a = acc a in as'
    have hrep_q : as'.rep q a = as.acc a := by
      show (setFn as.rep q (setFn (as.rep q) a (as.acc a))) q a = _; simp [setFn]
    -- prom a = ballot q in as'
    have hprom' : as'.prom a = ballot q := by
      show setFn as.prom a (ballot q) a = _; simp [setFn]
    -- Prove h_got1b for as': got1b p a = true ↔ ballot q ≥ ballot p
    have hgot1b' : ∀ p, as'.got1b p a = true ↔ as'.prom a ≥ ballot p := by
      intro p
      rw [hprom']
      by_cases hpq : p = q
      · subst hpq; simp [hgot_q]
      · rw [hgot_ne p hpq, h_got1b]
        constructor
        · intro h; omega
        · intro h
          -- ballot q ≥ ballot p. Need: as.prom a ≥ ballot p
          -- If got1b p a = false: p is pending (ballot p ≤ ballot q ≤ b)
          -- By minimality of q: ballot q ≤ ballot p, so ballot p = ballot q
          -- By injectivity: p = q, contradiction
          cases hg : as.got1b p a with
          | true => exact (h_got1b p).mp hg
          | false =>
            exfalso
            have hpbal : ballot p ≤ b := by omega
            have := hq_min p ⟨hpbal, hg⟩
            have := h_inj (by omega : ballot q = ballot p)
            exact hpq this.symm
    -- Prove h_rep_none for as'
    have hrep_none' : ∀ p, as'.got1b p a = false → as'.rep p a = none := by
      intro p hgot
      by_cases hpq : p = q
      · subst hpq; simp [hgot_q] at hgot
      · rw [hgot_ne p hpq] at hgot; rw [hrep_ne p hpq]; exact h_rep_none p hgot
    -- h_bval carries over
    have hbval' : as'.prom a = b ∨ ∃ p, ballot p = b := by
      exact h_bval.imp (by omega) id
    -- prom a ≤ b
    have hle' : as'.prom a ≤ b := by rw [hprom']; omega
    -- pendingCount decreases
    have hpc_lt : pendingCount ballot as'.got1b a b < pendingCount ballot as.got1b a b := by
      unfold pendingCount
      apply List.countP_lt_of_strict
      · -- new predicate implies old predicate
        intro p _ hp
        simp only [decide_eq_true_eq] at hp ⊢
        obtain ⟨hbal, hgot⟩ := hp
        refine ⟨hbal, ?_⟩
        by_cases hpq : p = q
        · subst hpq; simp [hgot_q] at hgot
        · rwa [hgot_ne p hpq] at hgot
      · -- q is in finRange m
        exact List.mem_finRange q
      · -- new predicate is false at q (got1b q a = true in as')
        simp [hgot_q]
      · -- old predicate is true at q
        simp only [hq_bal, hq_got, and_self, decide_true]
    -- Now apply the inductive hypothesis to as'
    have hk' : pendingCount ballot as'.got1b a b < k := by omega
    have hrec := ih _ hk' as' hle' hgot1b' hrep_none' hbval' rfl
    -- Show the target state matches between as and as' formulations
    -- Key equalities for the target state expressed via as' vs as
    have hprom_eq : (fun j => if j = a then b else as'.prom j) =
        (fun j => if j = a then b else as.prom j) := by
      funext j; split
      · rfl
      · next h =>
        change setFn as.prom a (ballot q) j = as.prom j
        simp only [setFn, h, ↓reduceIte]
    have hgot1b_eq : (fun p' j => if j = a ∧ ballot p' ≤ b then true else as'.got1b p' j) =
        (fun p' j => if j = a ∧ ballot p' ≤ b then true else as.got1b p' j) := by
      funext p' j; split
      · rfl
      · next h =>
        change (setFn as.got1b q (setFn (as.got1b q) a true) p') j = as.got1b p' j
        by_cases hpq : p' = q
        · subst hpq
          simp only [setFn_same]
          by_cases hja : j = a
          · subst hja; exfalso; exact h ⟨rfl, hq_bal⟩
          · simp only [setFn, hja, ↓reduceIte]
        · simp only [setFn, hpq, ↓reduceIte]
    -- Helper: as'.rep p' j = as.rep p' j when p' ≠ q OR j ≠ a
    have hrep_pj : ∀ p' j, (p' ≠ q ∨ j ≠ a) → as'.rep p' j = as.rep p' j := by
      intro p' j h
      change (setFn as.rep q (setFn (as.rep q) a (as.acc a)) p') j = as.rep p' j
      by_cases hpq : p' = q
      · rw [hpq, setFn_same, setFn_ne _ _ (by rcases h with h | h; exact absurd hpq h; exact h)]
      · rw [setFn_ne _ _ hpq]
    have hrep_eq : (fun p' j => if j = a ∧ ballot p' ≤ b ∧ as'.got1b p' a = false
        then as'.acc a else as'.rep p' j) =
        (fun p' j => if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false
        then as.acc a else as.rep p' j) := by
      funext p' j
      by_cases hja : j = a
      · -- j = a
        rw [hja]
        by_cases hpq : p' = q
        · -- p' = q
          rw [hpq]
          by_cases hbal : ballot q ≤ b
          · simp only [hgot_q, hq_got, true_and, hbal, and_true, ↓reduceIte]
            exact hrep_q
          · exfalso; omega
        · -- p' ≠ q
          rw [hgot_ne p' hpq]
          by_cases hbal : ballot p' ≤ b
          · split
            · rfl
            · exact hrep_pj p' a (.inl hpq)
          · have h1 : ¬(True ∧ ballot p' ≤ b ∧ as'.got1b p' a = false) := by
              intro ⟨_, h, _⟩; exact hbal h
            have h2 : ¬(True ∧ ballot p' ≤ b ∧ as.got1b p' a = false) := by
              intro ⟨_, h, _⟩; exact hbal h
            simp only [h2, ↓reduceIte]
            exact hrep_pj p' a (.inl hpq)
      · -- j ≠ a: both conditions false
        simp only [hja, false_and, ↓reduceIte]
        exact hrep_pj p' j (.inr hja)
    -- Now construct the Star chain
    have h_eq : (⟨fun j => if j = a then b else as.prom j, as.acc,
        fun p' j => if j = a ∧ ballot p' ≤ b then true else as.got1b p' j,
        fun p' j => if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false then as.acc a else as.rep p' j,
        as.prop, as.did2b⟩ : PaxosTextbookN.PaxosState n m) =
      ⟨fun j => if j = a then b else as'.prom j, as'.acc,
        fun p' j => if j = a ∧ ballot p' ≤ b then true else as'.got1b p' j,
        fun p' j => if j = a ∧ ballot p' ≤ b ∧ as'.got1b p' a = false then as'.acc a else as'.rep p' j,
        as'.prop, as'.did2b⟩ := by
      apply PaxosTextbookN.PaxosState.ext <;> [exact hprom_eq.symm; rfl; exact hgot1b_eq.symm;
        exact hrep_eq.symm; rfl; rfl]
    rw [h_eq]
    exact Star.step hstep hrec
  · -- Base case: no pending proposers, target = as
    -- hpend : ¬∃ q, ballot q ≤ b ∧ as.got1b q a = false
    -- Derive: for all q, ballot q ≤ b → got1b q a = true
    have hgot_true : ∀ p', ballot p' ≤ b → as.got1b p' a = true := by
      intro p' hp'
      cases hg : as.got1b p' a with
      | false => exact absurd ⟨p', hp', hg⟩ hpend
      | true => rfl
    -- First show prom a = b
    have hprom_eq : as.prom a = b := by
      rcases h_bval with rfl | ⟨p, hp⟩
      · rfl
      · have := (h_got1b p).mp (hgot_true p (hp ▸ Nat.le_refl _)); omega
    -- Now show target state = as
    have h_eq : (⟨fun j => if j = a then b else as.prom j,
        as.acc,
        fun p' j => if j = a ∧ ballot p' ≤ b then true else as.got1b p' j,
        fun p' j => if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false
          then as.acc a else as.rep p' j,
        as.prop,
        as.did2b⟩ : PaxosTextbookN.PaxosState n m) = as := by
      apply PaxosTextbookN.PaxosState.ext
      · -- prom
        funext j; simp only; split
        · next h => subst h; exact hprom_eq.symm
        · rfl
      · rfl  -- acc
      · -- got1b
        funext p' j; simp only; split
        · next h =>
          obtain ⟨rfl, hbal⟩ := h
          exact (hgot_true p' hbal).symm
        · rfl
      · -- rep
        funext p' j; simp only; split
        · next h =>
          obtain ⟨_, hbal, hgot⟩ := h
          exact absurd ⟨p', hbal, hgot⟩ hpend
        · rfl
      · rfl  -- prop
      · rfl  -- did2b
    rw [h_eq]; exact Star.refl

/-- Full `Star` for the B2 case of `recvAccept`: multi-p1b + p2a + p2b.
    Requires `prop p = none` (first vote at this ballot by any acceptor),
    `did2b p a = false`, and `prom a ≤ ballot p`.  The p2a step needs
    `majority(got1b p)` and the value-choice constraint, which must be
    supplied by the caller (typically derived from the message model's
    safeAt invariant). -/
theorem multi_p1b_p2a_p2b_star {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot)
    (_h_pos : ∀ p, ballot p > 0)
    (as : PaxosTextbookN.PaxosState n m) (a : Fin n) (p : Fin m) (b : Nat)
    (v : PaxosTextbookN.Value)
    (h_le : as.prom a ≤ ballot p)
    (h_ballot : ballot p = b)
    (h_prop_none : as.prop p = none)
    (h_did2b_false : as.did2b p a = false)
    (h_got1b : ∀ q, as.got1b q a = true ↔ as.prom a ≥ ballot q)
    (h_rep_none : ∀ q, as.got1b q a = false → as.rep q a = none)
    -- After raising prom[a] to b, a majority of acceptors have got1b p = true.
    (h_majority : PaxosTextbookN.majority
      (fun j => if j = a then true else as.got1b p j) = true)
    -- The value v is safe at ballot p (Lamport's safeAt predicate).
    -- This replaces the old max-vote constraint: safeAt is the specification-level
    -- requirement, while max-vote is one implementation that implies safeAt.
    (h_safe_v : PaxosTextbookN.safeAt ballot as v (ballot p)) :
    Star (atomicSpec n m ballot).next as
      { prom := setFn as.prom a (ballot p)
        acc := setFn as.acc a (some (ballot p, v))
        got1b := fun p' j =>
          if j = a ∧ ballot p' ≤ b then true else as.got1b p' j
        rep := fun p' j =>
          if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false
          then as.acc a else as.rep p' j
        prop := setFn as.prop p (some v)
        did2b := setFn as.did2b p (setFn (as.did2b p) a true) } := by
  -- Phase 1: multi_p1b_star raises prom[a] to b and sets got1b/rep
  have h_p1b := multi_p1b_star h_inj as a b (h_ballot ▸ h_le) h_got1b h_rep_none
    (.inr ⟨p, h_ballot⟩)
  -- Intermediate state after multi_p1b
  let S1 : PaxosTextbookN.PaxosState n m :=
    ⟨fun j => if j = a then b else as.prom j,
     as.acc,
     fun p' j => if j = a ∧ ballot p' ≤ b then true else as.got1b p' j,
     fun p' j => if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false then as.acc a else as.rep p' j,
     as.prop,
     as.did2b⟩
  -- Intermediate state after p2a
  let S2 : PaxosTextbookN.PaxosState n m :=
    ⟨S1.prom, S1.acc, S1.got1b, S1.rep, setFn S1.prop p (some v), S1.did2b⟩
  -- Final state after p2b
  let S3 : PaxosTextbookN.PaxosState n m :=
    ⟨setFn as.prom a (ballot p),
     setFn as.acc a (some (ballot p, v)),
     fun p' j => if j = a ∧ ballot p' ≤ b then true else as.got1b p' j,
     fun p' j => if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false then as.acc a else as.rep p' j,
     setFn as.prop p (some v),
     setFn as.did2b p (setFn (as.did2b p) a true)⟩
  -- Useful equalities
  have hgot1b_conv : (fun j => if j = a ∧ ballot p ≤ b then true else as.got1b p j) =
      (fun j => if j = a then true else as.got1b p j) := by
    funext j; by_cases hja : j = a
    · simp [hja, h_ballot]
    · simp [hja]
  -- Phase 2: p2a step on S1
  have h_p2a_gate1 : S1.prop p = none := h_prop_none
  have h_p2a_gate2 : PaxosTextbookN.majority (S1.got1b p) = true := by
    show PaxosTextbookN.majority (fun j => if j = a ∧ ballot p ≤ b then true else as.got1b p j) = true
    rw [hgot1b_conv]; exact h_majority
  -- Helper: convert between (x = a ∧ ballot p ≤ b ∧ P) and (x = a ∧ P)
  have hbpb : ballot p ≤ b := h_ballot ▸ Nat.le_refl _
  -- safeAt in the pre-state transfers to S1 (multi_p1b only changes prom/got1b/rep, not did2b/prop/acc)
  -- and safeAt depends on votedFor (did2b, prop) and wontVoteAt (did2b, prom).
  -- prom only increased (from as.prom a to b); wontVoteAt is monotone in prom.
  -- votedFor is unchanged (did2b, prop unchanged by multi_p1b).
  -- So safeAt in as implies safeAt in S1.
  have h_p2a_safe_S1 : PaxosTextbookN.safeAt ballot S1 v (ballot p) := by
    intro c hc
    obtain ⟨Q, hQmaj, hQprop⟩ := h_safe_v c hc
    refine ⟨Q, hQmaj, fun j hj => ?_⟩
    rcases hQprop j hj with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
    · exact Or.inl ⟨r, hrb, hdr, hrv⟩  -- votedFor: did2b/prop unchanged in S1
    · -- wontVoteAt: prom only increased, so prom > c still holds
      right; refine ⟨hnv, ?_⟩
      show S1.prom j > c
      by_cases hja : j = a
      · simp [S1, hja]; omega
      · simp [S1, hja]; exact hprom
  -- (h_p2a_constraint removed — p2a now uses safeAt instead of max-vote)
  have h_p2a : (atomicSpec n m ballot).next S1 S2 :=
    ⟨.p2a p, ⟨h_p2a_gate1, h_p2a_gate2⟩, v, rfl, h_p2a_safe_S1⟩
  -- Phase 3: p2b step on S2
  have h_p2b_gate1 : S2.did2b p a = false := h_did2b_false
  have h_p2b_gate2 : S2.prom a ≤ ballot p := by
    show (if a = a then b else as.prom a) ≤ ballot p; simp [h_ballot]
  have h_p2b_prop : S2.prop p = some v := by show setFn as.prop p (some v) p = some v; simp [setFn]
  have h_p2b : (atomicSpec n m ballot).next S2 S3 := by
    refine ⟨.p2b p a, ⟨h_p2b_gate1, h_p2b_gate2⟩, v, h_p2b_prop, ?_⟩
    -- S3 = { S2 with prom := setFn S2.prom a (ballot p), acc := setFn S2.acc a (some (ballot p, v)),
    --        did2b := setFn S2.did2b p (setFn (S2.did2b p) a true) }
    apply PaxosTextbookN.PaxosState.ext
    · -- prom: S3.prom = setFn S2.prom a (ballot p)
      funext j
      show setFn as.prom a (ballot p) j = setFn (fun j => if j = a then b else as.prom j) a (ballot p) j
      simp only [setFn]; split <;> simp_all
    · -- acc: S3.acc = setFn S2.acc a (some (ballot p, v))
      funext j
      show setFn as.acc a (some (ballot p, v)) j = setFn as.acc a (some (ballot p, v)) j
      rfl
    · rfl -- got1b
    · rfl -- rep
    · rfl -- prop
    · rfl -- did2b
  exact Star.trans h_p1b (Star.step h_p2a (Star.step h_p2b Star.refl))

/-! ### Main theorem -/

noncomputable def paxosSimulation {n m : Nat} (ballot : Fin m → Nat)
    (h_inj : Function.Injective ballot)
    (h_pos : ∀ p, ballot p > 0) :
    SimulationRelInv
      (MessagePaxos.MsgPaxosState n m)
      (PaxosTextbookN.PaxosState n m) where
  concrete := msgSpec n m ballot
  abstract := atomicSpec n m ballot
  R := SimRel ballot
  inv := fun ms => MessagePaxos.Reachable ballot ms
  inv_init := by intro s hs; subst hs; exact MessagePaxos.Reachable.init
  inv_next := by intro s s' hinv ⟨act, hstep⟩; exact MessagePaxos.Reachable.step hinv hstep
  init_sim := by
    intro s hs; subst hs
    refine ⟨{ prom := fun _ => 0, acc := fun _ => none, got1b := fun _ _ => false,
              rep := fun _ _ => none, prop := fun _ => none, did2b := fun _ _ => false },
            ?_, ?_⟩
    · exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
             fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
    · constructor
      · intro i; simp [MessagePaxos.initialMsgPaxos, MessagePaxos.initAcceptor]
      · intro i; simp [MessagePaxos.initialMsgPaxos, MessagePaxos.initAcceptor, vmapPair]
      · intro p i; simp [MessagePaxos.initialMsgPaxos]
      · intro p _; rfl
      · intro p a v h; simp [MessagePaxos.initialMsgPaxos] at h
      · intro p i; constructor
        · intro h; simp at h
        · intro h
          simp [MessagePaxos.initialMsgPaxos, MessagePaxos.initAcceptor] at h
          have := h_pos p; omega
      · intro p i _; rfl
      · intro p i bv bv' h; simp at h
      · intro p i h; simp at h
      · intro p i bw w h; simp at h
  step_sim := by
    intro ms ms' as hinv hR ⟨act, hstep⟩
    have hinvI := MessagePaxos.msg_paxos_inv_reachable h_inj hinv
    cases hstep with
    -- ── Stutter cases (acceptors/sentAccept unchanged) ─────────
    | sendPrepare p =>
      exact ⟨as, .refl, ⟨hR.prom_eq, hR.acc_eq, hR.did2b_eq, hR.prop_none,
        hR.prop_some, hR.got1b_iff, hR.rep_none, hR.rep_dom, hR.rep_acc, hR.rep_sent⟩⟩
    | recvPromise p a b prior idx hMem =>
      exact ⟨as, .refl, ⟨hR.prom_eq, hR.acc_eq, hR.did2b_eq, hR.prop_none,
        hR.prop_some, hR.got1b_iff, hR.rep_none, hR.rep_dom, hR.rep_acc, hR.rep_sent⟩⟩
    | decidePropose p v _ _ _ _ =>
      exact ⟨as, .refl, ⟨hR.prom_eq, hR.acc_eq, hR.did2b_eq, hR.prop_none,
        hR.prop_some, hR.got1b_iff, hR.rep_none, hR.rep_dom, hR.rep_acc, hR.rep_sent⟩⟩
    | dropMsg idx =>
      exact ⟨as, .refl, ⟨hR.prom_eq, hR.acc_eq, hR.did2b_eq, hR.prop_none,
        hR.prop_some, hR.got1b_iff, hR.rep_none, hR.rep_dom, hR.rep_acc, hR.rep_sent⟩⟩
    | crashProposer p =>
      exact ⟨as, .refl, ⟨hR.prom_eq, hR.acc_eq, hR.did2b_eq, hR.prop_none,
        hR.prop_some, hR.got1b_iff, hR.rep_none, hR.rep_dom, hR.rep_acc, hR.rep_sent⟩⟩
    | crashAcceptor a =>
      exact ⟨as, .refl, ⟨hR.prom_eq, hR.acc_eq, hR.did2b_eq, hR.prop_none,
        hR.prop_some, hR.got1b_iff, hR.rep_none, hR.rep_dom, hR.rep_acc, hR.rep_sent⟩⟩
    | sendAccept p b v hbp hProposed =>
      exact ⟨as, .refl, ⟨hR.prom_eq, hR.acc_eq, hR.did2b_eq, hR.prop_none,
        hR.prop_some, hR.got1b_iff, hR.rep_none, hR.rep_dom, hR.rep_acc, hR.rep_sent⟩⟩
    -- ── Non-stutter cases ──────────────────────────────────────
    | recvPrepare a p b idx hMem hProm =>
      -- b = ballot p from network invariant
      have hbp : ballot p = b := hinvI.hNetPrepare p b _ hMem
      -- Key: setAcceptor lemmas
      have hprom' : ∀ i, (MessagePaxos.setAcceptor ms.acceptors a
          { (ms.acceptors a) with prom := b } i).prom =
          if i = a then b else (ms.acceptors i).prom := by
        intro i; simp [MessagePaxos.setAcceptor]
        by_cases h : a = i
        · subst h; simp
        · simp [h]; intro h'; exfalso; exact h h'.symm
      have hacc' : ∀ i, (MessagePaxos.setAcceptor ms.acceptors a
          { (ms.acceptors a) with prom := b } i).acc = (ms.acceptors i).acc := by
        intro i; simp [MessagePaxos.setAcceptor]
        by_cases h : a = i
        · subst h; simp
        · simp [h]
      -- Define the abstract post-state
      refine ⟨{ prom := fun i => if i = a then b else as.prom i
                acc := as.acc
                got1b := fun p' i =>
                  if i = a ∧ ballot p' ≤ b then true else as.got1b p' i
                rep := fun p' i =>
                  if i = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false
                  then as.acc a else as.rep p' i
                prop := as.prop
                did2b := as.did2b }, ?star, ?simrel⟩
      case star =>
        exact multi_p1b_star h_inj as a b
          (by rw [hR.prom_eq]; omega)
          (fun p' => by rw [show as.prom a = (ms.acceptors a).prom from hR.prom_eq a]; exact hR.got1b_iff _ a)
          (fun p' h => hR.rep_none p' a h)
          (.inr ⟨p, hbp⟩)
      case simrel =>
        constructor
        · -- prom_eq
          intro i; simp only [hprom']
          by_cases h : i = a
          · subst h; simp
          · simp [h]; exact hR.prom_eq i
        · -- acc_eq
          intro i; rw [hacc']; exact hR.acc_eq i
        · -- did2b_eq (sentAccept unchanged)
          exact hR.did2b_eq
        · -- prop_none (sentAccept unchanged)
          exact hR.prop_none
        · -- prop_some (sentAccept unchanged)
          exact hR.prop_some
        · -- got1b_iff
          intro p' i; simp only [hprom']
          by_cases hia : i = a
          · subst hia
            simp only [ite_true, ge_iff_le]
            constructor
            · intro h; split at h
              · exact (‹_ ∧ _›).2
              · -- got1b true but ¬(ballot p' ≤ b): contradiction
                -- got1b true → prom i ≥ ballot p' (from SimRel on old state)
                -- but prom i < b (from hProm), and ¬(ballot p' ≤ b) → ballot p' > b
                have hpge := (hR.got1b_iff p' i).mp h
                omega
            · intro h; simp [h]
          · simp only [hia, false_and, ite_false, ge_iff_le]
            exact hR.got1b_iff p' i
        · -- rep_none: got1b false -> rep = none
          intro q j hgot
          -- hgot : (if j = a ... then true else as.got1b q j) = false
          -- If j = a and ballot q <= b, then got1b = true, contradiction.
          -- So NOT (j = a and ballot q <= b), meaning as.got1b q j = false.
          simp only at hgot
          split at hgot
          · simp at hgot
          · rename_i hc
            simp only
            have hc2 : ¬(j = a ∧ ballot q ≤ b ∧ as.got1b q a = false) :=
              fun ⟨h1, h2, _⟩ => hc ⟨h1, h2⟩
            rw [if_neg hc2]
            exact hR.rep_none q j hgot
        · -- rep_dom: got1b true -> rep = some bv -> acc = some bv' -> bv.1 <= bv'.1
          intro q j bv bv' hgot hrep hacc
          simp only at hgot hrep hacc
          split at hrep
          · rename_i hc
            -- rep = as.acc a = some bv (since j = a from hc)
            obtain ⟨hja, _, _⟩ := hc; subst hja
            -- hacc : as.acc a = some bv', so bv = bv' since hrep = as.acc a = some bv
            rw [hrep] at hacc; cases hacc; omega
          · rename_i hc
            -- rep = as.rep q j
            split at hgot
            · rename_i hc2
              -- j = a and ballot q <= b, but rep branch not taken
              obtain ⟨hja, hle⟩ := hc2; subst hja
              -- After subst, a is replaced by j everywhere
              -- hc : NOT (j = j AND ballot q <= b AND got1b q j = false)
              -- Since j = j and ballot q <= b, must have got1b q j = true
              have hgot_old : as.got1b q j = true := by
                by_contra h
                exact hc ⟨rfl, hle, Bool.not_eq_true _ |>.mp h⟩
              exact hR.rep_dom q j bv bv' hgot_old hrep hacc
            · exact hR.rep_dom q j bv bv' hgot hrep hacc
        · -- rep_acc: got1b true -> acc = none -> rep = none
          intro q j hgot hacc
          simp only at hgot hacc
          -- Need to avoid using `a` after potential subst
          by_cases hja : j = a
          · subst hja
            -- Now a is replaced by j; goal has j everywhere
            show (if j = j ∧ ballot q ≤ b ∧ as.got1b q j = false
                  then as.acc j else as.rep q j) = none
            split
            · rename_i hc
              exact hacc
            · rename_i hc
              split at hgot
              · rename_i hc2
                obtain ⟨_, hle⟩ := hc2
                have hgot_old : as.got1b q j = true := by
                  by_contra h
                  exact hc ⟨rfl, hle, Bool.not_eq_true _ |>.mp h⟩
                exact hR.rep_acc q j hgot_old hacc
              · exact hR.rep_acc q j hgot hacc
          · show (if j = a ∧ ballot q ≤ b ∧ as.got1b q a = false
                  then as.acc a else as.rep q j) = none
            have hc : ¬(j = a ∧ ballot q ≤ b ∧ as.got1b q a = false) :=
              fun ⟨h, _, _⟩ => hja h
            rw [if_neg hc]
            split at hgot
            · rename_i hc2; exfalso; exact hja hc2.1
            · exact hR.rep_acc q j hgot hacc
        · -- rep_sent: rep values linked to sentAccept (sentAccept unchanged in recvPrepare)
          -- Helper: extract sentAccept info from acc via vmapPair
          have acc_to_sent := acc_to_sent_lemma hR hinvI
          intro q j bw w hgot hrep
          simp only at hgot hrep
          split at hrep
          · -- rep was set to as.acc a (j = a, ballot q ≤ b, old got1b q a = false)
            rename_i hc; obtain ⟨hja, _, _⟩ := hc; subst hja
            exact acc_to_sent j bw w hrep
          · -- rep unchanged: as.rep q j
            split at hgot
            · rename_i hc2; obtain ⟨hja, hle⟩ := hc2; subst hja
              rename_i hc
              have hgot_old : as.got1b q j = true := by
                by_contra h; exact hc ⟨rfl, hle, Bool.not_eq_true _ |>.mp h⟩
              exact hR.rep_sent q j bw w hgot_old hrep
            · exact hR.rep_sent q j bw w hgot hrep
    | recvAccept a p b v idx hMem hProm hBallot =>
      -- hBallot : ballot p = b
      -- Concrete ms' has:
      --   acceptors[a].prom := b, acceptors[a].acc := some (b, v)
      --   sentAccept := setSent ms.sentAccept a b v
      -- Key helper lemmas for setAcceptor
      have hprom' : ∀ j, (MessagePaxos.setAcceptor ms.acceptors a
          { prom := b, acc := some (b, v) } j).prom =
          if j = a then b else (ms.acceptors j).prom := by
        intro j; simp [MessagePaxos.setAcceptor]
        by_cases h : a = j
        · subst h; simp
        · simp [h]; intro h'; exfalso; exact h h'.symm
      have hacc_new : ∀ j, (MessagePaxos.setAcceptor ms.acceptors a
          { prom := b, acc := some (b, v) } j).acc =
          if j = a then some (b, v) else (ms.acceptors j).acc := by
        intro j; simp [MessagePaxos.setAcceptor]
        by_cases h : a = j
        · subst h; simp
        · simp [h]; intro h'; exfalso; exact h h'.symm
      have hsent' : ∀ j c, MessagePaxos.setSent ms.sentAccept a b v j c =
          if j = a ∧ c = b then some v else ms.sentAccept j c := by
        intro j c; simp [MessagePaxos.setSent]
      -- Case split: was sentAccept a b already set?
      by_cases hSentOld : ms.sentAccept a b = some v
      · -- Subcase A: sentAccept a b was already some v → stutter
        have hprom_eq : (ms.acceptors a).prom = b := by
          have := hinvI.hSentProm a b v hSentOld; omega
        have hacc_old : (ms.acceptors a).acc = some (b, v) := by
          obtain ⟨b', v', hacc_some, hge⟩ := hinvI.hAccMax a b v hSentOld
          have hpge := hinvI.hAccProm a b' v' hacc_some
          have hbeq : b' = b := by omega
          have hacc_some' : (ms.acceptors a).acc = some (b, v') := by rw [← hbeq]; exact hacc_some
          have hsent_v' := hinvI.hAccSent a b v' hacc_some'
          have hveq := hinvI.hSentUnique a a b v v' hSentOld hsent_v'
          subst hveq; exact hacc_some'
        have hsent_eq : ∀ j c, MessagePaxos.setSent ms.sentAccept a b v j c = ms.sentAccept j c := by
          intro j c; simp only [MessagePaxos.setSent]
          by_cases hc : j = a ∧ c = b
          · rw [if_pos hc]; obtain ⟨hj, hcb⟩ := hc; subst hj; subst hcb; exact hSentOld.symm
          · rw [if_neg hc]
        -- Stutter: as' = as
        refine ⟨as, .refl, ?_⟩
        constructor
        · -- prom_eq
          intro j; rw [hprom']
          by_cases h : j = a
          · rw [if_pos h, h, ← hprom_eq]; exact hR.prom_eq a
          · rw [if_neg h]; exact hR.prom_eq j
        · -- acc_eq
          intro j; rw [hacc_new]
          by_cases h : j = a
          · rw [if_pos h, h, hR.acc_eq, hacc_old]
          · rw [if_neg h]; exact hR.acc_eq j
        · -- did2b_eq
          intro p' j
          show as.did2b p' j = (MessagePaxos.setSent ms.sentAccept a b v j (ballot p')).isSome
          rw [hsent_eq]; exact hR.did2b_eq p' j
        · -- prop_none
          intro p' h
          show as.prop p' = none
          apply hR.prop_none p'
          intro a'
          have : MessagePaxos.setSent ms.sentAccept a b v a' (ballot p') = none := h a'
          rw [hsent_eq] at this; exact this
        · -- prop_some
          intro p' a' v' h
          show as.prop p' = some (vmap v')
          have : MessagePaxos.setSent ms.sentAccept a b v a' (ballot p') = some v' := h
          rw [hsent_eq] at this
          exact hR.prop_some p' a' v' this
        · -- got1b_iff
          intro p' j; rw [hprom']
          by_cases h : j = a
          · rw [if_pos h, h, ← hprom_eq]; exact hR.got1b_iff p' a
          · rw [if_neg h]; exact hR.got1b_iff p' j
        · exact hR.rep_none
        · exact hR.rep_dom
        · exact hR.rep_acc
        · -- rep_sent: sentAccept is unchanged (hsent_eq), so hR.rep_sent works
          intro p' i bw w hgot hrep
          obtain ⟨w', hsent_old, hw⟩ := hR.rep_sent p' i bw w hgot hrep
          exact ⟨w', by show MessagePaxos.setSent ms.sentAccept a b v i bw = some w'
                        rw [hsent_eq]; exact hsent_old, hw⟩
      · -- Subcase B: sentAccept a b ≠ some v → first vote
        have hSentNone : ms.sentAccept a b = none := by
          rcases hsa : ms.sentAccept a b with _ | w
          · rfl
          · exfalso
            have := hinvI.hSentAcceptNet a b w hsa p v _ hMem
            subst this; exact hSentOld hsa
        -- Abstract: need to fire p2b(p, a), possibly preceded by p2a(p)
        -- p2b gate: did2b p a = false ∧ prom a ≤ ballot p
        -- did2b p a = false because sentAccept a (ballot p) = none (from did2b_eq)
        have hdid2b_false : as.did2b p a = false := by
          rw [hR.did2b_eq]; simp [hSentNone, hBallot]
        -- prom a ≤ ballot p: from prom_eq and hProm
        have hprom_le : as.prom a ≤ ballot p := by
          rw [hR.prom_eq]; omega
        -- We also need prop p to exist for p2b.
        -- Subcase B1: some other acceptor already voted → prop p exists
        -- Subcase B2: no acceptor voted → need p2a first
        -- For now, construct the post-state and sorry the Star
        -- The abstract post-state after p2b(p, a):
        -- prom[a] := ballot p = b, acc[a] := some (ballot p, vmap v)
        -- did2b[p][a] := true
        -- And possibly prop[p] := some (vmap v) from p2a
        --
        -- Key: after the step, prop p = some (vmap v) must hold for SimRel.
        -- This is because sentAccept a (ballot p) = some v in ms'.
        -- By prop_some: as'.prop p = some (vmap v).
        --
        -- If prop p was already some w: w = vmap v (from existing sentAccept entries).
        -- If prop p was none: need to fire p2a(p) first.
        by_cases hPropOld : as.prop p = none
        · -- Subcase B2: prop p = none, need p2a(p) then p2b(p, a)
          refine ⟨{ prom := setFn as.prom a (ballot p)
                    acc := setFn as.acc a (some (ballot p, vmap v))
                    got1b := fun p' j =>
                      if j = a ∧ ballot p' ≤ b then true else as.got1b p' j
                    rep := fun p' j =>
                      if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false
                      then as.acc a else as.rep p' j
                    prop := setFn as.prop p (some (vmap v))
                    did2b := setFn as.did2b p (setFn (as.did2b p) a true) }, ?star, ?simrel⟩
          case star =>
            exact multi_p1b_p2a_p2b_star h_inj h_pos as a p b (vmap v)
              (by rw [hR.prom_eq]; omega)
              hBallot hPropOld hdid2b_false
              (fun q => by
                have hpe := hR.prom_eq a
                rw [show as.prom a = (ms.acceptors a).prom from hpe]
                exact hR.got1b_iff _ a)
              (fun q h => hR.rep_none q a h)
              (by -- h_majority: majority of {a} ∪ {j | prom j ≥ ballot p}
                have hmaj := hinvI.hNetAcceptProm p b v (MessagePaxos.Target.acc a) hMem
                have hmono : ∀ j, decide ((ms.acceptors j).prom ≥ b) = true →
                    (if j = a then true else as.got1b p j) = true := by
                  intro j hj; simp only [decide_eq_true_eq] at hj
                  by_cases hja : j = a
                  · simp [hja]
                  · rw [if_neg hja]; exact (hR.got1b_iff p j).mpr (hBallot ▸ hj)
                show PaxosTextbookN.majority _ = true
                change MessagePaxos.majority _ = true
                exact MessagePaxos.majority_mono_prom hmaj hmono)
              (by -- h_safe_v: derive atomic safeAt from message-level ProposedSafeInv
                -- Get message-level safeAt from MsgPaxosInv.hNetSafe
                have hmsg_safe : MessagePaxos.safeAt ms v b :=
                  hinvI.hNetSafe p b v _ hMem
                -- Translate to atomic safeAt
                intro c hc
                obtain ⟨Q, hQmaj, hQprop⟩ := hmsg_safe c (hBallot ▸ hc)
                refine ⟨Q, ?_, fun j hj => ?_⟩
                · -- majority: MessagePaxos.majority = PaxosTextbookN.majority
                  change MessagePaxos.majority Q = true; exact hQmaj
                · rcases hQprop j hj with hvoted | ⟨hnone, hprom⟩
                  · -- sentAccept j c = some v → votedFor
                    left
                    obtain ⟨r, hrb⟩ := hinvI.hSentBallot j c v hvoted
                    refine ⟨r, hrb, ?_, ?_⟩
                    · -- did2b r j = true
                      rw [hR.did2b_eq]; simp [hrb, hvoted]
                    · -- prop r = some (vmap v)
                      exact hR.prop_some r j v (hrb ▸ hvoted)
                  · -- sentAccept j c = none ∧ prom > c → wontVoteAt
                    right
                    constructor
                    · -- ∀ r, ballot r = c → did2b r j ≠ true
                      intro r hrb hdid
                      rw [hR.did2b_eq] at hdid
                      simp [hrb, hnone] at hdid
                    · -- prom j > c
                      rw [hR.prom_eq]; exact hprom)
          case simrel =>
            -- SimRel for the B2 case: abstract state has multi_p1b + p2a + p2b updates
            constructor
            · -- prom_eq
              intro j; simp only [setFn]; rw [hprom']
              by_cases h : j = a
              · simp [h, hBallot]
              · simp [h]; exact hR.prom_eq j
            · -- acc_eq
              intro j; simp only [setFn]; rw [hacc_new]
              by_cases h : j = a
              · simp [h, vmapPair, hBallot]
              · simp [h]; exact hR.acc_eq j
            · -- did2b_eq
              intro p' j
              show setFn as.did2b p (setFn (as.did2b p) a true) p' j =
                (MessagePaxos.setSent ms.sentAccept a b v j (ballot p')).isSome
              simp only [setFn, hsent']
              by_cases hpj : p' = p
              · subst hpj
                by_cases hja : j = a
                · subst hja; simp [hBallot]
                · simp [hja]
                  show as.did2b p' j = (ms.sentAccept j (ballot p')).isSome
                  exact hR.did2b_eq p' j
              · simp [hpj]
                show as.did2b p' j = (if j = a ∧ ballot p' = b then some v
                  else ms.sentAccept j (ballot p')).isSome
                by_cases hja : j = a
                · subst hja
                  by_cases hbb : ballot p' = b
                  · simp [hbb]
                    -- ballot p' = b = ballot p and p' ≠ p contradicts injectivity
                    exfalso; exact hpj (h_inj (hbb.trans hBallot.symm))
                  · simp [hbb]; exact hR.did2b_eq p' j
                · simp [hja]; exact hR.did2b_eq p' j
            · -- prop_none
              intro p' h_all
              show setFn as.prop p (some (vmap v)) p' = none
              simp only [setFn]
              by_cases hpp : p' = p
              · -- p' = p: some acceptor voted (a voted), so h_all is impossible
                subst hpp
                exfalso
                have h1 := h_all a
                simp only at h1
                rw [hsent'] at h1
                simp [hBallot] at h1
              · simp [hpp]
                apply hR.prop_none p'
                intro a'
                have h1 := h_all a'
                simp only at h1
                rw [hsent'] at h1
                by_cases hc : a' = a ∧ ballot p' = b
                · simp [hc] at h1
                · simp [hc] at h1; exact h1
            · -- prop_some
              intro p' a' v' h
              show setFn as.prop p (some (vmap v)) p' = some (vmap v')
              simp only [setFn]
              simp only at h; rw [hsent'] at h
              by_cases hpp : p' = p
              · rw [if_pos hpp]
                by_cases hc : a' = a ∧ ballot p' = b
                · obtain ⟨ha', hb'⟩ := hc; simp [ha', hb'] at h; subst h; rfl
                · simp [hc] at h
                  -- sentAccept a' (ballot p') = some v' where ballot p' = b (from hpp, hBallot)
                  have hbp : ballot p' = b := hpp ▸ hBallot
                  have := hinvI.hSentAcceptNet a' b v' (hbp ▸ h) p v (MessagePaxos.Target.acc a) hMem
                  subst this; rfl
              · rw [if_neg hpp]
                have hc : ¬(a' = a ∧ ballot p' = b) := by
                  intro ⟨_, hb'⟩; exact hpp (h_inj (hb'.trans hBallot.symm))
                simp [hc] at h
                exact hR.prop_some p' a' v' h
            · -- got1b_iff
              intro p' j
              by_cases hja : j = a
              · subst hja
                -- got1b p' a in new state: if True ∧ ballot p' ≤ b then true else as.got1b p' a
                -- prom a in new ms': b
                -- Need: (if ballot p' ≤ b then true else as.got1b p' a) = true ↔ b ≥ ballot p'
                simp only [true_and]
                rw [hprom']; simp only [ite_true]
                constructor
                · intro h
                  by_cases hle : ballot p' ≤ b
                  · exact hle
                  · -- got1b p' j = true from the else branch: as.got1b p' j = true
                    simp [hle] at h
                    have hpge := (hR.got1b_iff p' j).mp h
                    -- prom_eq: as.prom j = (ms.acceptors j).prom
                    -- hProm: (ms.acceptors j).prom ≤ b
                    have := hR.prom_eq j; omega
                · intro h; simp [h]
              · simp only [hja, false_and, ite_false, ge_iff_le]
                rw [hprom']; rw [if_neg hja]
                exact hR.got1b_iff p' j
            · -- rep_none
              intro q j hgot
              simp only at hgot
              split at hgot
              · simp at hgot
              · rename_i hc
                simp only
                have hc2 : ¬(j = a ∧ ballot q ≤ b ∧ as.got1b q a = false) :=
                  fun ⟨h1, h2, _⟩ => hc ⟨h1, h2⟩
                rw [if_neg hc2]
                exact hR.rep_none q j hgot
            · -- rep_dom
              intro q j bv bv' hgot hrep hacc
              simp only at hgot hrep hacc
              simp only [setFn] at hacc
              -- Helper: bv from as.acc a has bv.1 ≤ ballot p
              have acc_le_ballot : ∀ bv0, as.acc a = some bv0 → bv0.1 ≤ ballot p := by
                intro bv0 h0
                have hacc_a := hR.acc_eq a
                rw [h0] at hacc_a
                rcases hacc_ms : (ms.acceptors a).acc with _ | ⟨b', v'⟩
                · rw [hacc_ms, vmapPair] at hacc_a; simp at hacc_a
                · rw [hacc_ms, vmapPair] at hacc_a
                  simp at hacc_a; subst hacc_a
                  have := hinvI.hAccProm a b' v' hacc_ms; omega
              -- Helper: old rep at (q, j) with got1b true also has .1 ≤ ballot p when j = a
              have rep_le_ballot : as.got1b q a = true → ∀ bv0, as.rep q a = some bv0 →
                  bv0.1 ≤ ballot p := by
                intro hg bv0 hr
                rcases hacc_old : as.acc a with _ | bv1
                · have := hR.rep_acc q a hg hacc_old; rw [this] at hr; simp at hr
                · exact Nat.le_trans (hR.rep_dom q a bv0 bv1 hg hr hacc_old) (acc_le_ballot bv1 hacc_old)
              split at hrep
              · rename_i hc
                -- rep = as.acc a = some bv (since j = a from hc)
                obtain ⟨hja, _, _⟩ := hc; subst hja
                simp at hacc; cases hacc
                -- bv' = (ballot p, vmap v), need bv.1 ≤ ballot p
                exact acc_le_ballot bv hrep
              · rename_i hc
                -- rep = as.rep q j
                split at hgot
                · rename_i hc2
                  obtain ⟨hja, hle⟩ := hc2; subst hja
                  have hgot_old : as.got1b q j = true := by
                    by_contra h
                    exact hc ⟨rfl, hle, Bool.not_eq_true _ |>.mp h⟩
                  simp at hacc; cases hacc
                  -- bv' = (ballot p, vmap v), need bv.1 ≤ ballot p
                  exact rep_le_ballot hgot_old bv hrep
                · -- ¬(j = a ∧ ballot q ≤ b): either j ≠ a or ballot q > b
                  rename_i hc2
                  by_cases hja : j = a
                  · subst hja
                    -- j = a, so ballot q > b (from hc2)
                    have hbq : ¬(ballot q ≤ b) := fun h => hc2 ⟨rfl, h⟩
                    -- got1b q j = true, got1b_iff: ↔ (ms.acceptors j).prom ≥ ballot q
                    -- But (ms.acceptors j).prom ≤ b < ballot q: contradiction
                    have hpge := (hR.got1b_iff q j).mp hgot
                    omega
                  · simp [hja] at hacc
                    exact hR.rep_dom q j bv bv' hgot hrep hacc
            · -- rep_acc
              intro q j hgot hacc
              simp only at hgot hacc
              simp only [setFn] at hacc
              by_cases hja : j = a
              · subst hja
                -- hacc : some (ballot p, vmap v) = none, contradiction
                simp at hacc
              · show (if j = a ∧ ballot q ≤ b ∧ as.got1b q a = false
                      then as.acc a else as.rep q j) = none
                have hc : ¬(j = a ∧ ballot q ≤ b ∧ as.got1b q a = false) :=
                  fun ⟨h, _, _⟩ => hja h
                rw [if_neg hc]
                simp [hja] at hacc
                split at hgot
                · rename_i hc2; exfalso; exact hja hc2.1
                · exact hR.rep_acc q j hgot hacc
            · -- rep_sent: rep values linked to sentAccept (new ms' has setSent)
              have acc_to_sent := acc_to_sent_lemma hR hinvI
              -- Helper: old sentAccept entries survive in setSent
              have hsent_lift : ∀ j' c w', ms.sentAccept j' c = some w' →
                  MessagePaxos.setSent ms.sentAccept a b v j' c = some w' := by
                intro j' c w' h'; simp only [MessagePaxos.setSent]
                by_cases hc : j' = a ∧ c = b
                · obtain ⟨hj', hcb⟩ := hc; subst hj'; subst hcb
                  rw [if_pos ⟨rfl, rfl⟩]; rw [hSentNone] at h'; simp at h'
                · rw [if_neg hc]; exact h'
              intro q j bw w hgot hrep
              simp only at hgot hrep
              split at hrep
              · -- rep was set to as.acc a (j = a)
                rename_i hc; obtain ⟨hja, _, _⟩ := hc
                obtain ⟨vv, hsent_old, hw⟩ := acc_to_sent a bw w hrep
                refine ⟨vv, ?_, hw⟩; rw [hja]
                show MessagePaxos.setSent ms.sentAccept a b v a bw = _
                exact hsent_lift a bw vv hsent_old
              · -- rep unchanged
                split at hgot
                · rename_i hc2; obtain ⟨hja, hle⟩ := hc2
                  rename_i hc
                  have hgot_old : as.got1b q a = true := by
                    rw [hja] at hc
                    by_contra h; exact hc ⟨rfl, hle, Bool.not_eq_true _ |>.mp h⟩
                  obtain ⟨w', hsent_old, hw⟩ := hR.rep_sent q j bw w (hja ▸ hgot_old) hrep
                  refine ⟨w', ?_, hw⟩
                  show MessagePaxos.setSent ms.sentAccept a b v j bw = _
                  exact hsent_lift j bw w' hsent_old
                · obtain ⟨w', hsent_old, hw⟩ := hR.rep_sent q j bw w hgot hrep
                  refine ⟨w', ?_, hw⟩
                  show MessagePaxos.setSent ms.sentAccept a b v j bw = _
                  exact hsent_lift j bw w' hsent_old
        · -- Subcase B1: prop p ≠ none → prop p = some (vmap v)
          have hprop_v : as.prop p = some (vmap v) := by
            -- prop p ≠ none means ∃ a' with sentAccept a' (ballot p) ≠ none
            -- Then prop_some gives prop p = some (vmap v') and v' = v from hSentAcceptNet
            by_contra h_neq
            -- Get a witness: some acceptor must have voted at ballot p
            have h_all : ∀ a', ms.sentAccept a' (ballot p) = none := by
              intro a'
              rcases hsa : ms.sentAccept a' (ballot p) with _ | v'
              · rfl
              · exfalso
                have hsa' : ms.sentAccept a' b = some v' := hBallot ▸ hsa
                have hprop := hR.prop_some p a' v' (by rw [hBallot]; exact hsa')
                have hveq := hinvI.hSentAcceptNet a' b v' hsa' p v _ hMem
                subst hveq; exact h_neq hprop
            exact absurd (hR.prop_none p h_all) hPropOld
          -- After recvAccept, concrete prom[a] increases to b. The abstract p2b
          -- only updates prom/acc/did2b. But got1b_iff requires got1b p' a ↔ prom a ≥ ballot p'.
          -- So we must also fire p1b for all proposers p' with ballot p' ≤ b
          -- and got1b p' a = false (same pattern as recvPrepare), THEN fire p2b.
          -- Define the abstract post-state with got1b/rep extended:
          refine ⟨{ prom := setFn as.prom a (ballot p)
                    acc := setFn as.acc a (some (ballot p, vmap v))
                    got1b := fun p' j =>
                      if j = a ∧ ballot p' ≤ b then true else as.got1b p' j
                    rep := fun p' j =>
                      if j = a ∧ ballot p' ≤ b ∧ as.got1b p' a = false
                      then as.acc a else as.rep p' j
                    prop := as.prop
                    did2b := setFn as.did2b p (setFn (as.did2b p) a true) }, ?star, ?simrel⟩
          case star =>
            -- Phase 1: multi_p1b_star raises prom[a] to b and sets got1b/rep
            have h_p1b := multi_p1b_star h_inj as a b
              (by rw [hR.prom_eq]; omega)
              (fun p' => by
                have hpe := hR.prom_eq a
                rw [show as.prom a = (ms.acceptors a).prom from hpe]
                exact hR.got1b_iff _ a)
              (fun p' h => hR.rep_none p' a h)
              (.inr ⟨p, hBallot⟩)
            -- Phase 2: p2b(p, a) step from the intermediate state
            apply Star.trans h_p1b
            apply Star.step _ Star.refl
            -- Show (atomicSpec).next fires p2b(p, a)
            show ∃ act, ((PaxosTextbookN.paxos n m ballot).actions act).fires _ _
            refine ⟨.p2b p a, ?gate, ?trans⟩
            case gate =>
              -- did2b p a = false (unchanged by p1b) and prom a = b ≥ ballot p
              exact ⟨hdid2b_false, by simp [hBallot]⟩
            case trans =>
              refine ⟨vmap v, hprop_v, ?_⟩
              simp only [PaxosTextbookN.paxos, hBallot]
              apply PaxosTextbookN.PaxosState.ext
              · -- prom: setFn as.prom a b = setFn (if · = a then b else as.prom ·) a b
                ext j; simp only [setFn]; split <;> rfl
              all_goals rfl
          case simrel =>
            constructor
            · -- prom_eq
              intro j; simp only [setFn, hprom']
              by_cases h : j = a
              · subst h; simp [hBallot]
              · simp [h]; exact hR.prom_eq j
            · -- acc_eq
              intro j; simp only [setFn, hacc_new]
              by_cases h : j = a
              · subst h; simp [vmapPair, hBallot]
              · simp [h]; exact hR.acc_eq j
            · -- did2b_eq
              intro p' j
              show setFn as.did2b p (setFn (as.did2b p) a true) p' j =
                (MessagePaxos.setSent ms.sentAccept a b v j (ballot p')).isSome
              simp only [setFn, hsent']
              by_cases hpj : p' = p
              · subst hpj
                by_cases hja : j = a
                · subst hja; simp [hBallot]
                · simp [hja]
                  show as.did2b p' j = (ms.sentAccept j (ballot p')).isSome
                  exact hR.did2b_eq p' j
              · simp [hpj]
                show as.did2b p' j = (if j = a ∧ ballot p' = b then some v
                  else ms.sentAccept j (ballot p')).isSome
                by_cases hja : j = a
                · subst hja
                  by_cases hbb : ballot p' = b
                  · simp [hbb]
                    -- ballot p' = b = ballot p and p' ≠ p contradicts injectivity
                    exfalso; exact hpj (h_inj (hbb.trans hBallot.symm))
                  · simp [hbb]; exact hR.did2b_eq p' j
                · simp [hja]; exact hR.did2b_eq p' j
            · -- prop_none
              intro p' h_all
              show as.prop p' = none
              apply hR.prop_none p'
              intro a'
              have h1 := h_all a'
              simp only at h1
              rw [hsent'] at h1
              by_cases hc : a' = a ∧ ballot p' = b
              · simp [hc] at h1
              · simp [hc] at h1; exact h1
            · -- prop_some
              intro p' a' v' h
              show as.prop p' = some (vmap v')
              simp only at h
              rw [hsent'] at h
              by_cases hc : a' = a ∧ ballot p' = b
              · obtain ⟨ha', hb'⟩ := hc
                simp [ha', hb'] at h; subst h
                have hp' : p' = p := h_inj (hb'.trans hBallot.symm)
                subst hp'; exact hprop_v
              · simp [hc] at h
                exact hR.prop_some p' a' v' h
            · -- got1b_iff
              intro p' j; simp only [hprom']
              by_cases hja : j = a
              · subst hja
                simp only [ite_true, ge_iff_le, setFn, ite_true, hBallot]
                constructor
                · intro h; split at h
                  · exact (‹_ ∧ _›).2
                  · have hpge := (hR.got1b_iff p' j).mp h
                    omega
                · intro h; simp [h]
              · simp only [hja, false_and, ite_false, ge_iff_le, setFn, hja, ite_false]
                exact hR.got1b_iff p' j
            · -- rep_none
              intro q j hgot
              simp only at hgot
              split at hgot
              · simp at hgot
              · rename_i hc
                simp only
                have hc2 : ¬(j = a ∧ ballot q ≤ b ∧ as.got1b q a = false) :=
                  fun ⟨h1, h2, _⟩ => hc ⟨h1, h2⟩
                rw [if_neg hc2]
                exact hR.rep_none q j hgot
            · -- rep_dom
              intro q j bv bv' hgot hrep hacc
              simp only at hgot hrep hacc
              simp only [setFn] at hacc
              -- Helper: bv from as.acc a has bv.1 ≤ ballot p
              have acc_le_ballot : ∀ bv0, as.acc a = some bv0 → bv0.1 ≤ ballot p := by
                intro bv0 h0
                have hacc_a := hR.acc_eq a
                rw [h0] at hacc_a
                rcases hacc_ms : (ms.acceptors a).acc with _ | ⟨b', v'⟩
                · rw [hacc_ms, vmapPair] at hacc_a; simp at hacc_a
                · rw [hacc_ms, vmapPair] at hacc_a
                  simp at hacc_a; subst hacc_a
                  have := hinvI.hAccProm a b' v' hacc_ms; omega
              -- Helper: old rep at (q, j) with got1b true also has .1 ≤ ballot p when j = a
              have rep_le_ballot : as.got1b q a = true → ∀ bv0, as.rep q a = some bv0 →
                  bv0.1 ≤ ballot p := by
                intro hg bv0 hr
                rcases hacc_old : as.acc a with _ | bv1
                · have := hR.rep_acc q a hg hacc_old; rw [this] at hr; simp at hr
                · exact Nat.le_trans (hR.rep_dom q a bv0 bv1 hg hr hacc_old) (acc_le_ballot bv1 hacc_old)
              split at hrep
              · rename_i hc
                -- rep = as.acc a = some bv (since j = a from hc)
                obtain ⟨hja, _, _⟩ := hc; subst hja
                simp at hacc; cases hacc
                -- bv' = (ballot p, vmap v), need bv.1 ≤ ballot p
                exact acc_le_ballot bv hrep
              · rename_i hc
                -- rep = as.rep q j
                split at hgot
                · rename_i hc2
                  obtain ⟨hja, hle⟩ := hc2; subst hja
                  have hgot_old : as.got1b q j = true := by
                    by_contra h
                    exact hc ⟨rfl, hle, Bool.not_eq_true _ |>.mp h⟩
                  simp at hacc; cases hacc
                  -- bv' = (ballot p, vmap v), need bv.1 ≤ ballot p
                  exact rep_le_ballot hgot_old bv hrep
                · -- ¬(j = a ∧ ballot q ≤ b): either j ≠ a or ballot q > b
                  rename_i hc2
                  by_cases hja : j = a
                  · subst hja
                    -- j = a (now j everywhere), so ballot q > b (from hc2)
                    have hbq : ¬(ballot q ≤ b) := fun h => hc2 ⟨rfl, h⟩
                    -- got1b q j = true, got1b_iff: ↔ (ms.acceptors j).prom ≥ ballot q
                    -- But (ms.acceptors j).prom ≤ b < ballot q: contradiction
                    have hpge := (hR.got1b_iff q j).mp hgot
                    omega
                  · simp [hja] at hacc
                    exact hR.rep_dom q j bv bv' hgot hrep hacc
            · -- rep_acc
              intro q j hgot hacc
              simp only at hgot hacc
              simp only [setFn] at hacc
              by_cases hja : j = a
              · subst hja
                -- hacc : some (ballot p, vmap v) = none, contradiction
                simp at hacc
              · show (if j = a ∧ ballot q ≤ b ∧ as.got1b q a = false
                      then as.acc a else as.rep q j) = none
                have hc : ¬(j = a ∧ ballot q ≤ b ∧ as.got1b q a = false) :=
                  fun ⟨h, _, _⟩ => hja h
                rw [if_neg hc]
                simp [hja] at hacc
                split at hgot
                · rename_i hc2; exfalso; exact hja hc2.1
                · exact hR.rep_acc q j hgot hacc
            · -- rep_sent
              have acc_to_sent := acc_to_sent_lemma hR hinvI
              have hsent_lift : ∀ j' c w', ms.sentAccept j' c = some w' →
                  MessagePaxos.setSent ms.sentAccept a b v j' c = some w' := by
                intro j' c w' h'; simp only [MessagePaxos.setSent]
                by_cases hc : j' = a ∧ c = b
                · obtain ⟨hj', hcb⟩ := hc; subst hj'; subst hcb
                  rw [if_pos ⟨rfl, rfl⟩]; rw [hSentNone] at h'; simp at h'
                · rw [if_neg hc]; exact h'
              intro q j bw w hgot hrep
              simp only at hgot hrep
              split at hrep
              · rename_i hc; obtain ⟨hja, _, _⟩ := hc
                obtain ⟨vv, hsent_old, hw⟩ := acc_to_sent a bw w hrep
                refine ⟨vv, ?_, hw⟩; rw [hja]
                show MessagePaxos.setSent ms.sentAccept a b v a bw = _
                exact hsent_lift a bw vv hsent_old
              · split at hgot
                · rename_i hc2; obtain ⟨hja, hle⟩ := hc2
                  rename_i hc
                  have hgot_old : as.got1b q a = true := by
                    rw [hja] at hc
                    by_contra h; exact hc ⟨rfl, hle, Bool.not_eq_true _ |>.mp h⟩
                  obtain ⟨w', hsent_old, hw⟩ := hR.rep_sent q j bw w (hja ▸ hgot_old) hrep
                  refine ⟨w', ?_, hw⟩
                  show MessagePaxos.setSent ms.sentAccept a b v j bw = _
                  exact hsent_lift j bw w' hsent_old
                · obtain ⟨w', hsent_old, hw⟩ := hR.rep_sent q j bw w hgot hrep
                  refine ⟨w', ?_, hw⟩
                  show MessagePaxos.setSent ms.sentAccept a b v j bw = _
                  exact hsent_lift j bw w' hsent_old

end PaxosRefinement
