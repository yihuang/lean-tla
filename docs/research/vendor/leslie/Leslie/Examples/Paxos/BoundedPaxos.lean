import Leslie.Examples.Paxos
import Leslie.Examples.Combinators.PhaseCounting

/-! # Faithful m-proposer single-decree Paxos bounded unrolling

    Wraps `Leslie/Examples/Paxos.lean`'s real quorum-gated Paxos model in a
    `PhaseCountingSystem` and derives a bounded-unrolling theorem at trace
    depth `2·m·n + m`.

    The phase counter counts fired actions:
    - each `p1b p i` flips one `got1b p i` bit (`m·n` such bits),
    - each `p2a p` sets one `prop p` slot from `none` to `some` (`m` slots),
    - each `p2b p i` flips one `did2b p i` bit (`m·n` such bits).

    Total capacity `2·m·n + m`. Each step strictly increases the counter by
    one, so the counter is monotone and bounded, giving the abstract
    bounded-unrolling theorem for free.

    This file replaces the earlier `BoundedTwoProposer.lean` /
    `BoundedMProposer.lean` defer-rule shortcut models. Those were sound but
    forced the safety invariant to reference proposer volatile state, which
    precluded any fault-model extension. This wrapper inherits its safety
    proof directly from the existing `PaxosTextbookN.agreement` theorem.

    No Mathlib. No sorries.
-/

open TLA

namespace PaxosTextbookN.Bounded

open PaxosTextbookN

/-! ## Section 1: Counting primitives -/

/-- Count of `some` entries in a `Fin k → Option α` function. -/
def countSome {α : Type} {k : Nat} (f : Fin k → Option α) : Nat :=
  ((List.finRange k).filter fun i => (f i).isSome).length

theorem countSome_le {α : Type} {k : Nat} (f : Fin k → Option α) :
    countSome f ≤ k := by
  unfold countSome
  have := List.length_filter_le (fun i => (f i).isSome) (List.finRange k)
  simpa [List.length_finRange] using this

theorem countTrue_le {n : Nat} (f : Fin n → Bool) : countTrue f ≤ n := by
  unfold countTrue
  have := List.length_filter_le (fun i => f i) (List.finRange n)
  simpa [List.length_finRange] using this

/-! ### Delta lemma: flipping one bit from false to true -/

/-- Generic helper: if `f` and `g` are boolean functions agreeing off of
    `i`, with `f i = false` and `g i = true`, then on any Nodup list `L`,
    `(L.filter g).length = (L.filter f).length + (if i ∈ L then 1 else 0)`. -/
private theorem filter_flip_one_aux {n : Nat} (f g : Fin n → Bool) (i : Fin n)
    (hne : ∀ j, j ≠ i → f j = g j) (hfi : f i = false) (hgi : g i = true) :
    ∀ (L : List (Fin n)), L.Nodup →
      (L.filter g).length =
        (L.filter f).length + (if i ∈ L then 1 else 0) := by
  intro L hnd
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
    have ih' := ih hnd'
    by_cases hxi : x = i
    · -- x = i: can't subst (i is a free var); derive everything from hxi
      have hxieq : x = i := hxi
      have hnotin : i ∉ xs := hxi ▸ hxnot
      have ih'' : (List.filter g xs).length = (List.filter f xs).length := by
        have := ih hnd'
        simp [hnotin] at this
        exact this
      have hmemcons : i ∈ (x :: xs) := hxieq ▸ (List.mem_cons_self (a := i) (l := xs))
      have hfx : f x = false := hxieq ▸ hfi
      have hgx : g x = true := hxieq ▸ hgi
      have hlenF : (List.filter f (x :: xs)).length = (List.filter f xs).length := by
        rw [List.filter_cons, hfx]; simp
      have hlenG : (List.filter g (x :: xs)).length = (List.filter g xs).length + 1 := by
        rw [List.filter_cons, hgx]; simp
      rw [hlenF, hlenG, ih'']
      simp [hmemcons]
    · have hagx : f x = g x := hne x hxi
      have hne' : i ≠ x := fun h => hxi h.symm
      have hmem_iff : (i ∈ x :: xs) ↔ i ∈ xs := by
        constructor
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact absurd h hne'
          · exact h
        · exact fun h => List.mem_cons_of_mem _ h
      by_cases hfx : f x = true
      · have hgx : g x = true := hagx ▸ hfx
        have : (if f x = true then x :: List.filter f xs else List.filter f xs).length
             = (List.filter f xs).length + 1 := by rw [hfx]; simp
        have hG : (if g x = true then x :: List.filter g xs else List.filter g xs).length
             = (List.filter g xs).length + 1 := by rw [hgx]; simp
        simp only [List.filter_cons]
        rw [this, hG, ih']
        by_cases hmem : i ∈ xs
        · have hmc : (i ∈ x :: xs) := hmem_iff.mpr hmem
          simp [hmc, hmem]
        · have hnmc : ¬ (i ∈ x :: xs) := fun h => hmem (hmem_iff.mp h)
          simp [hnmc, hmem]
      · have hfx' : f x = false := by cases h : f x <;> simp_all
        have hgx' : g x = false := hagx ▸ hfx'
        have : (if f x = true then x :: List.filter f xs else List.filter f xs).length
             = (List.filter f xs).length := by rw [hfx']; simp
        have hG : (if g x = true then x :: List.filter g xs else List.filter g xs).length
             = (List.filter g xs).length := by rw [hgx']; simp
        simp only [List.filter_cons]
        rw [this, hG, ih']
        by_cases hmem : i ∈ xs
        · have hmc : (i ∈ x :: xs) := hmem_iff.mpr hmem
          simp [hmc, hmem]
        · have hnmc : ¬ (i ∈ x :: xs) := fun h => hmem (hmem_iff.mp h)
          simp [hnmc, hmem]

/-- If `f j = g j` for all `j ≠ i`, `f i = false`, and `g i = true`, then
    `countTrue g = countTrue f + 1`. -/
theorem countTrue_flip_one {n : Nat} (f g : Fin n → Bool) (i : Fin n)
    (hne : ∀ j, j ≠ i → f j = g j) (hfi : f i = false) (hgi : g i = true) :
    countTrue g = countTrue f + 1 := by
  unfold countTrue
  have hh := filter_flip_one_aux f g i hne hfi hgi (List.finRange n)
    (List.nodup_finRange n)
  have hmem : i ∈ List.finRange n := List.mem_finRange i
  simpa [hmem] using hh

/-- Specialized form: `setFn f i true` where `f i = false` adds exactly one
    to `countTrue`. -/
theorem countTrue_setFn_true {n : Nat} (f : Fin n → Bool) (i : Fin n)
    (h : f i = false) :
    countTrue (setFn f i true) = countTrue f + 1 := by
  apply countTrue_flip_one f (setFn f i true) i
  · intro j hj; simp [setFn, hj]
  · exact h
  · simp [setFn]

/-! ### Sum of a `Nat`-valued function over `Fin m` -/

/-- Sum `f 0 + f 1 + ... + f (m-1)`. -/
def finSumN {m : Nat} (f : Fin m → Nat) : Nat :=
  ((List.finRange m).map f).foldr (· + ·) 0

theorem finSumN_le_mul {m : Nat} (f : Fin m → Nat) (k : Nat)
    (h : ∀ p, f p ≤ k) : finSumN f ≤ m * k := by
  unfold finSumN
  suffices h' : ∀ (L : List (Fin m)), (L.map f).foldr (· + ·) 0 ≤ L.length * k by
    have := h' (List.finRange m); simpa [List.length_finRange] using this
  intro L
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons, List.length_cons]
    have hx : f x ≤ k := h x
    have hmul : (xs.length + 1) * k = xs.length * k + k := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- If `f` and `g` agree off of `i`, and `g i = f i + 1`, then their sums
    differ by 1. -/
theorem finSumN_update_plus_one {m : Nat} (f g : Fin m → Nat) (i : Fin m)
    (hagree : ∀ j, j ≠ i → f j = g j) (hstep : g i = f i + 1) :
    finSumN g = finSumN f + 1 := by
  unfold finSumN
  suffices h : ∀ (L : List (Fin m)), L.Nodup →
      (L.map g).foldr (· + ·) 0 =
        (L.map f).foldr (· + ·) 0 + (if i ∈ L then 1 else 0) by
    have hh := h (List.finRange m) (List.nodup_finRange m)
    have hmem : i ∈ List.finRange m := List.mem_finRange i
    simpa [hmem] using hh
  intro L hnd
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
    have ih' := ih hnd'
    simp only [List.map_cons, List.foldr_cons]
    by_cases hxi : x = i
    · have hxieq : x = i := hxi
      have hnotin : i ∉ xs := hxi ▸ hxnot
      have ih'' :
          (List.map g xs).foldr (· + ·) 0 = (List.map f xs).foldr (· + ·) 0 := by
        have := ih hnd'
        simp [hnotin] at this
        exact this
      have hmemcons : (i ∈ (x :: xs)) := hxieq ▸ (List.mem_cons_self (a := i) (l := xs))
      rw [show (if i ∈ x :: xs then (1 : Nat) else 0) = 1 from by simp [hmemcons]]
      rw [ih'', hxieq, hstep]; omega
    · have hagx : f x = g x := hagree x hxi
      have hne' : i ≠ x := fun h => hxi h.symm
      have hmem_iff : (i ∈ x :: xs) ↔ i ∈ xs := by
        constructor
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact absurd h hne'
          · exact h
        · exact fun h => List.mem_cons_of_mem _ h
      by_cases hmem : i ∈ xs
      · have hmem_cons : i ∈ x :: xs := hmem_iff.mpr hmem
        rw [ih', ← hagx]
        simp [hmem_cons, hmem]; omega
      · have hnmem_cons : ¬ (i ∈ x :: xs) := fun h => hmem (hmem_iff.mp h)
        rw [ih', ← hagx]
        simp [hnmem_cons, hmem]

/-! ## Section 2: The phase counter -/

/-- Phase counter for `PaxosState n m`: total number of `got1b` bits set,
    plus total number of `did2b` bits set, plus number of filled `prop`
    slots. Each step flips exactly one of these on. -/
def phaseCounter {n m : Nat} (s : PaxosState n m) : Nat :=
  finSumN (fun p => countTrue (s.got1b p)) +
  finSumN (fun p => countTrue (s.did2b p)) +
  countSome s.prop

/-- Canonical initial state used as the start of all bounded traces. -/
def initialPaxos (n m : Nat) : PaxosState n m where
  prom  := fun _ => 0
  acc   := fun _ => none
  got1b := fun _ _ => false
  rep   := fun _ _ => none
  prop  := fun _ => none
  did2b := fun _ _ => false
  voted := fun _ _ => none

theorem initialPaxos_isInit {n m : Nat} (ballot : Fin m → Nat) :
    (paxos n m ballot).init (initialPaxos n m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem finSumN_const_zero {m : Nat} :
    finSumN (fun _ : Fin m => (0 : Nat)) = 0 := by
  unfold finSumN
  induction List.finRange m with
  | nil => simp
  | cons x xs ih => simpa using ih

theorem countTrue_allFalse {n : Nat} : countTrue (fun _ : Fin n => false) = 0 := by
  unfold countTrue; simp

theorem phaseCounter_init (n m : Nat) :
    phaseCounter (initialPaxos n m) = 0 := by
  unfold phaseCounter initialPaxos countSome
  simp only [countTrue_allFalse]
  rw [finSumN_const_zero]
  simp

theorem phaseCounter_le (n m : Nat) (s : PaxosState n m) :
    phaseCounter s ≤ 2 * m * n + m := by
  unfold phaseCounter
  have h1 : finSumN (fun p => countTrue (s.got1b p)) ≤ m * n :=
    finSumN_le_mul _ n (fun _ => countTrue_le _)
  have h2 : finSumN (fun p => countTrue (s.did2b p)) ≤ m * n :=
    finSumN_le_mul _ n (fun _ => countTrue_le _)
  have h3 : countSome s.prop ≤ m := countSome_le _
  have hmn : 2 * m * n = m * n + m * n := by
    rw [Nat.mul_assoc, Nat.two_mul]
  omega

/-! ## Section 3: Counter monotonicity along each action -/

/-- A `p1b p i` step, with shape matching the transition in `Paxos.lean`,
    increases the counter by exactly one. -/
theorem phaseCounter_step_p1b {n m : Nat} (ballot : Fin m → Nat)
    (s : PaxosState n m) (p : Fin m) (i : Fin n)
    (hg : s.got1b p i = false) :
    phaseCounter ({ s with
        prom := setFn s.prom i (ballot p)
        got1b := setFn s.got1b p (setFn (s.got1b p) i true)
        rep := setFn s.rep p (setFn (s.rep p) i (s.acc i)) }) =
      phaseCounter s + 1 := by
  unfold phaseCounter
  have hgot_sum :
      finSumN (fun q => countTrue (setFn s.got1b p (setFn (s.got1b p) i true) q)) =
      finSumN (fun q => countTrue (s.got1b q)) + 1 := by
    apply finSumN_update_plus_one
      (fun q => countTrue (s.got1b q))
      (fun q => countTrue (setFn s.got1b p (setFn (s.got1b p) i true) q))
      p
    · intro q hq; simp [setFn, hq]
    · have : setFn s.got1b p (setFn (s.got1b p) i true) p = setFn (s.got1b p) i true := by
        simp [setFn]
      rw [this]
      exact countTrue_setFn_true (s.got1b p) i hg
  show
    finSumN (fun q => countTrue (setFn s.got1b p (setFn (s.got1b p) i true) q)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop =
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop + 1
  rw [hgot_sum]; omega

theorem phaseCounter_step_p2b {n m : Nat} (ballot : Fin m → Nat)
    (s : PaxosState n m) (p : Fin m) (i : Fin n) (v : Value)
    (hd : s.did2b p i = false) :
    phaseCounter ({ s with
        prom := setFn s.prom i (ballot p)
        acc := setFn s.acc i (some (ballot p, v))
        did2b := setFn s.did2b p (setFn (s.did2b p) i true)
        voted := updateVoted s.voted i (ballot p) v }) =
      phaseCounter s + 1 := by
  unfold phaseCounter
  have hdid_sum :
      finSumN (fun q => countTrue (setFn s.did2b p (setFn (s.did2b p) i true) q)) =
      finSumN (fun q => countTrue (s.did2b q)) + 1 := by
    apply finSumN_update_plus_one
      (fun q => countTrue (s.did2b q))
      (fun q => countTrue (setFn s.did2b p (setFn (s.did2b p) i true) q))
      p
    · intro q hq; simp [setFn, hq]
    · have : setFn s.did2b p (setFn (s.did2b p) i true) p = setFn (s.did2b p) i true := by
        simp [setFn]
      rw [this]
      exact countTrue_setFn_true (s.did2b p) i hd
  show
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun q => countTrue (setFn s.did2b p (setFn (s.did2b p) i true) q)) +
      countSome s.prop =
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop + 1
  rw [hdid_sum]; omega

theorem phaseCounter_step_p2a {n m : Nat}
    (s : PaxosState n m) (p : Fin m) (v : Value)
    (hp : s.prop p = none) :
    phaseCounter ({ s with prop := setFn s.prop p (some v) }) =
      phaseCounter s + 1 := by
  unfold phaseCounter
  have hcs : countSome (setFn s.prop p (some v)) = countSome s.prop + 1 := by
    unfold countSome
    have hnone : (s.prop p).isSome = false := by simp [hp]
    have hnew : (setFn s.prop p (some v) p).isSome = true := by simp [setFn]
    have :=
      countTrue_flip_one
        (f := fun q : Fin m => (s.prop q).isSome)
        (g := fun q : Fin m => (setFn s.prop p (some v) q).isSome)
        p
        (by intro j hj; simp [setFn, hj])
        hnone
        hnew
    unfold countTrue at this
    exact this
  show
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome (setFn s.prop p (some v)) =
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop + 1
  rw [hcs]; omega

/-! ## Section 4: The PhaseCountingSystem instantiation -/

/-- Step relation lifted from `paxos n m ballot`. -/
def paxosStep {n m : Nat} (ballot : Fin m → Nat)
    (s s' : PaxosState n m) (a : PaxosAction n m) : Prop :=
  ((paxos n m ballot).actions a).fires s s'

/-- Every step of `paxosStep` increases `phaseCounter` by exactly one. -/
theorem phaseCounter_step {n m : Nat} (ballot : Fin m → Nat)
    (s s' : PaxosState n m) (a : PaxosAction n m)
    (h : paxosStep ballot s s' a) :
    phaseCounter s' = phaseCounter s + 1 := by
  cases a with
  | p1b p i =>
    simp only [paxosStep, GatedAction.fires] at h
    dsimp only [paxos] at h
    obtain ⟨⟨hg1, _⟩, rfl⟩ := h
    exact phaseCounter_step_p1b ballot s p i hg1
  | p2a p =>
    simp only [paxosStep, GatedAction.fires] at h
    dsimp only [paxos] at h
    obtain ⟨⟨hg1, _⟩, v, rfl, _⟩ := h
    exact phaseCounter_step_p2a s p v hg1
  | p2b p i =>
    simp only [paxosStep, GatedAction.fires] at h
    dsimp only [paxos] at h
    obtain ⟨⟨hg1, _⟩, v, _, rfl⟩ := h
    exact phaseCounter_step_p2b ballot s p i v hg1

/-- The bounded-unrolling system wrapping real Paxos. -/
def boundedPaxos (n m : Nat) (ballot : Fin m → Nat) : PhaseCounting.PhaseCountingSystem where
  State        := PaxosState n m
  Action       := PaxosAction n m
  step         := paxosStep ballot
  init         := initialPaxos n m
  phaseCounter := phaseCounter
  bound        := 2 * m * n + m
  init_zero    := phaseCounter_init n m
  step_mono    := by
    intro s s' a h
    have := phaseCounter_step ballot s s' a h
    omega
  step_bounded := by
    intro s s' _ _
    exact phaseCounter_le n m s'

/-! ## Section 5: Safety via PaxosInv -/

/-- Framework-reachability in `boundedPaxos` implies `PaxosInv`. Uses
    term-mode structural recursion (mirroring `Reachable.of_refined`)
    because `Reachable` takes its `PhaseCountingSystem` as a parameter,
    not an index, making `induction`'s motive awkward. -/
theorem paxosInv_of_reachable {n m : Nat} (ballot : Fin m → Nat)
    (h_inj : Function.Injective ballot) :
    ∀ {s : PaxosState n m},
      PhaseCounting.Reachable (boundedPaxos n m ballot) s → PaxosInv ballot s
  | _, .init => paxos_inv_init ballot _ (initialPaxos_isInit ballot)
  | _, .step a hr hstep =>
      paxos_inv_next h_inj _ _ (paxosInv_of_reachable ballot h_inj hr) ⟨a, hstep⟩

/-- The safety target: any two proposers that reach a `did2b` majority
    propose the same value. This is the conclusion of
    `PaxosTextbookN.agreement`. -/
def Safe {n m : Nat} (s : PaxosState n m) : Prop :=
  ∀ p q, majority (s.did2b p) = true → majority (s.did2b q) = true →
         s.prop p = s.prop q

/-- **Main agreement theorem.** Every framework-reachable state of
    `boundedPaxos` satisfies `Safe`. Delegates to the existing
    `PaxosTextbookN.agreement` theorem via `PaxosInv` preservation. -/
theorem boundedPaxos_agreement {n m : Nat} (ballot : Fin m → Nat)
    (h_inj : Function.Injective ballot)
    (s : PaxosState n m)
    (h : PhaseCounting.Reachable (boundedPaxos n m ballot) s) :
    Safe s := by
  intro p q hmp hmq
  exact agreement h_inj (paxosInv_of_reachable ballot h_inj h) p q hmp hmq

/-- Bounded-unrolling corollary: `Safe` holds at every framework-reachable
    state iff it holds along every trace of length `≤ 2·m·n + m`. -/
theorem boundedPaxos_bounded_unrolling {n m : Nat} (ballot : Fin m → Nat) :
    PhaseCounting.safeAll (boundedPaxos n m ballot) Safe ↔
    PhaseCounting.safeUpTo (boundedPaxos n m ballot) Safe (2 * m * n + m) :=
  PhaseCounting.phase_counting_bounded_unrolling (boundedPaxos n m ballot) Safe

/-! ## Section 6: Counter-tightness along any valid trace

    The phase counter `phaseCounter` is structured so that every step of
    `paxosStep` increases it by **exactly** one (not merely strictly).
    This means that *if* a valid trace of length `L` exists starting
    from `initialPaxos`, then the final state automatically has
    `phaseCounter = L`. In particular, any maximally-long valid trace
    witnesses tightness of the `2·m·n + m` bound.

    The sketch of such a schedule — for each proposer `p` in order,
    run `p1b p i` for every acceptor, then `p2a p`, then `p2b p i`
    for every acceptor — is described in an informal comment below.
    A fully formal witness construction is left as future work
    (see `docs/rust-verification-plan-v2.md` note on Phase X1(b)).
    The abstract tightness theorem below reduces the remaining work
    to the schedule-existence obligation.
-/

/-! ## Section 6 (continued): Reachability of the `2·m·n + m` bound

    We show the `2·m·n + m` bound is tight: there exists a reachable
    state whose phase counter equals `2·m·n + m`. The proof exhibits
    an explicit schedule: for each proposer `p` in order, run `p1b p i`
    for every acceptor, then `p2a p`, then `p2b p i` for every
    acceptor. Each proposer contributes `2n + 1` actions; `m` proposers
    contribute `m · (2n + 1) = 2·m·n + m`.

    Feasibility requires ballot-monotone proposers and `n ≥ 1` (so a
    unanimous quorum is a majority). Under these hypotheses, each
    proposer's `p2a` sees a fully-reported quorum whose highest-ballot
    vote is the previous proposer's proposal, forcing every proposer
    to adopt the same value (the one freely chosen at proposer 0).

    Since `phaseCounter_step` is an exact `+1` equality (not just
    strict), once we have a trace of length `L` from a state with
    counter `C`, the final state automatically has counter `C + L`.
    We therefore only prove that the schedule is a **valid trace**;
    the final counter follows by arithmetic.
-/

open PhaseCounting

/-- The free initial value carried through the schedule. -/
def initialValue : Value := .v1

/-- Counter equality along any `StepsFrom` trace in `boundedPaxos`,
    strengthening `phaseCounter_after_steps` from `≤` to `=`. Each step
    increases the counter by **exactly** one. -/
theorem phaseCounter_after_steps_eq {n m : Nat} (ballot : Fin m → Nat) :
    ∀ {s s' : PaxosState n m} {acts : List (PaxosAction n m)},
      StepsFrom (boundedPaxos n m ballot) s acts s' →
      phaseCounter s' = phaseCounter s + acts.length
  | _, _, _, .nil _ => by simp
  | _, _, _, .cons act acts hstep hrest => by
    have hab := phaseCounter_step ballot _ _ act hstep
    have ih := phaseCounter_after_steps_eq ballot hrest
    simp [ih, hab, List.length_cons]; omega

/-- `StepsFrom_append` helper (concatenation of multi-step traces). -/
theorem stepsFrom_append {P : PhaseCountingSystem}
    {s₁ s₂ s₃ : P.State} {as bs : List P.Action}
    (h1 : StepsFrom P s₁ as s₂) (h2 : StepsFrom P s₂ bs s₃) :
    StepsFrom P s₁ (as ++ bs) s₃ := by
  induction h1 with
  | nil _ => simpa using h2
  | @cons a b c act acts hstep _ ih =>
    simp only [List.cons_append]
    exact StepsFrom.cons act (acts ++ bs) hstep (ih h2)

/-! ### Abstract tightness: any valid trace reaches its length in counter

    A future construction completing unconditional tightness would
    define a per-`k` schedule invariant on `PaxosState n m` capturing
    "all proposers with index `< k` have fully run". The base case is
    `initialPaxos` at `k = 0`; the inductive step extends the trace by
    `2n + 1` more actions for proposer `k`, all of whose gates are
    satisfied by the invariant. The `p2a k` hconstr forces the new
    proposal to equal the previous proposer's value, so every proposer
    ends up with the same value and the schedule carries it forward.
    Estimated budget: 400–700 additional lines. -/

/-- **Trace-to-counter tightness.** If a valid trace of length `L`
    exists from `initialPaxos`, then the final state has
    `phaseCounter = L`. Combined with `phaseCounter_le`, this
    shows `L ≤ 2·m·n + m`, and any trace of maximal length `2·m·n + m`
    witnesses tightness of the bound.

    This is the abstract kernel of the tightness argument: it reduces
    the tightness question to schedule existence. -/
theorem boundedPaxos_trace_counter {n m : Nat} (ballot : Fin m → Nat)
    {s : PaxosState n m} {acts : List (PaxosAction n m)}
    (h : StepsFrom (boundedPaxos n m ballot) (initialPaxos n m) acts s) :
    phaseCounter s = acts.length := by
  have hinit : phaseCounter (initialPaxos n m) = 0 := phaseCounter_init n m
  have := phaseCounter_after_steps_eq ballot h
  omega

/-- **Tightness witness (m = 0 case).** When there are no proposers
    the bound is `0` and the empty trace witnesses it trivially. -/
theorem boundedPaxos_bound_tight_zero (n : Nat) (ballot : Fin 0 → Nat) :
    ∃ s, StepsFrom (boundedPaxos n 0 ballot) (initialPaxos n 0) [] s ∧
         phaseCounter s = 2 * 0 * n + 0 := by
  refine ⟨initialPaxos n 0, StepsFrom.nil _, ?_⟩
  rw [phaseCounter_init]; omega

/-- **Tightness, assuming a schedule.** If for the given parameters any
    trace of length `2·m·n + m` exists from `initialPaxos`, then the
    bound is witnessed: the final state has counter equal to the bound.

    The remaining obligation — constructing an explicit schedule — is
    left to future work. The schedule runs, for each proposer `p` in
    order, `p1b p i` for each acceptor `i`, then `p2a p`, then
    `p2b p i` for each acceptor `i`. Feasibility requires ballot
    monotonicity (`ballot i < ballot j` when `i.val < j.val`) and
    `n ≥ 1`. The intended witness value at every `p2a` is the same
    `initialValue : Value`. -/
theorem boundedPaxos_bound_tight_of_schedule {n m : Nat} (ballot : Fin m → Nat)
    {s : PaxosState n m} {acts : List (PaxosAction n m)}
    (h : StepsFrom (boundedPaxos n m ballot) (initialPaxos n m) acts s)
    (hlen : acts.length = 2 * m * n + m) :
    phaseCounter s = 2 * m * n + m := by
  have := boundedPaxos_trace_counter ballot h
  omega

/-! ## Section 7: Explicit tightness schedule

    We construct an explicit trace of length `2·m·n + m` from
    `initialPaxos`. The schedule runs, for each proposer `k` (in ballot
    order), the block `p1b k 0; p1b k 1; ...; p1b k (n-1); p2a k;
    p2b k 0; ...; p2b k (n-1)`, contributing `2n + 1` steps per round.

    For feasibility we need:
    - `ballot` strictly monotone in the index (so each round's `p1b`
      promises exceed all previously set promises, satisfying the
      `prom i ≤ ballot k` gate);
    - `n ≥ 1` (so the single-acceptor "majority" threshold is met after
      the first `p1b`, enabling `p2a`);
    - all rounds propose the same `initialValue`, chosen freely in round 0
      and forced in subsequent rounds by the highest-vote constraint.
-/

/-- Previous-round acc payload threaded through the schedule. At the
    start of round `k`, every acceptor has `acc i = prevAcc k`. -/
def prevAcc (m : Nat) (ballot : Fin m → Nat) (k : Nat) : Option (Nat × Value) :=
  match k with
  | 0 => none
  | k' + 1 => if h : k' < m then some (ballot ⟨k', h⟩, initialValue) else none

/-- Previous-round prom value threaded through the schedule. -/
def prevProm (m : Nat) (ballot : Fin m → Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 => if h : k' < m then ballot ⟨k', h⟩ else 0

/-- Voted-history at the start of round `k`: `some initialValue` iff some
    proposer with index `< k` has ballot equal to `b`. -/
def prevVoted (m : Nat) (ballot : Fin m → Nat) (k : Nat) (_i : Nat) (b : Nat) :
    Option Value :=
  if ∃ q : Fin m, q.val < k ∧ ballot q = b then some initialValue else none

/-- The quiescent state reached after fully executing proposers
    `0, 1, ..., k-1` in the tight schedule. -/
def stateAfter (n m : Nat) (ballot : Fin m → Nat) (k : Nat) : PaxosState n m where
  prom  := fun _ => prevProm m ballot k
  acc   := fun _ => prevAcc m ballot k
  got1b := fun q _ => decide (q.val < k)
  did2b := fun q _ => decide (q.val < k)
  rep   := fun q _ => if q.val < k then prevAcc m ballot q.val else none
  prop  := fun q => if q.val < k then some initialValue else none
  voted := fun i b => prevVoted m ballot k i.val b

/-- At `k = 0`, the quiescent schedule state is literally `initialPaxos`. -/
theorem stateAfter_zero (n m : Nat) (ballot : Fin m → Nat) :
    stateAfter n m ballot 0 = initialPaxos n m := by
  unfold stateAfter initialPaxos prevAcc prevProm prevVoted
  ext <;> simp

/-- State reached after running `p1b k ⟨0,_⟩, ..., p1b k ⟨j-1,_⟩`
    starting from `stateAfter k`. Generalises `stateAfter k` with `j`
    bits flipped in row `k` of `got1b`, `j` entries of `rep k`, and
    `j` entries of `prom`. -/
def afterP1bJ (n m : Nat) (ballot : Fin m → Nat) (k : Fin m) (j : Nat) :
    PaxosState n m where
  prom  := fun i => if i.val < j then ballot k else prevProm m ballot k.val
  acc   := fun _ => prevAcc m ballot k.val
  got1b := fun q i =>
    if q = k then decide (i.val < j) else decide (q.val < k.val)
  did2b := fun q _ => decide (q.val < k.val)
  rep   := fun q i =>
    if q = k then (if i.val < j then prevAcc m ballot k.val else none)
    else if q.val < k.val then prevAcc m ballot q.val else none
  prop  := fun q => if q.val < k.val then some initialValue else none
  voted := fun i b => prevVoted m ballot k.val i.val b

/-- At `j = 0`, the p1b-loop intermediate state coincides with
    `stateAfter k.val`. -/
theorem afterP1bJ_zero (n m : Nat) (ballot : Fin m → Nat) (k : Fin m) :
    afterP1bJ n m ballot k 0 = stateAfter n m ballot k.val := by
  unfold afterP1bJ stateAfter
  ext i <;> simp <;> (intros; rintro rfl; omega)

/-- At `j = n`, after all `n` p1b actions from proposer `k`, the loop
    state has all acceptors promised and reported to `k`. This is the
    starting state for `p2a k`. -/
def afterP1b (n m : Nat) (ballot : Fin m → Nat) (k : Fin m) : PaxosState n m :=
  afterP1bJ n m ballot k n

/-- State reached after running `p2a k` on `afterP1b k`, i.e. after the
    proposer has written its choice of `initialValue`. -/
def afterP2a (n m : Nat) (ballot : Fin m → Nat) (k : Fin m) : PaxosState n m :=
  { afterP1b n m ballot k with prop := setFn (afterP1b n m ballot k).prop k (some initialValue) }

/-- State reached after running `j` p2b actions from proposer `k`, on
    top of `afterP2a k`. -/
def afterP2bJ (n m : Nat) (ballot : Fin m → Nat) (k : Fin m) (j : Nat) :
    PaxosState n m where
  prom  := fun _ => ballot k
  acc   := fun i =>
    if i.val < j then some (ballot k, initialValue) else prevAcc m ballot k.val
  got1b := fun q _ =>
    if q = k then true else decide (q.val < k.val)
  did2b := fun q i =>
    if q = k then decide (i.val < j) else decide (q.val < k.val)
  rep   := fun q i =>
    if q = k then prevAcc m ballot k.val
    else if q.val < k.val then prevAcc m ballot q.val else none
  prop  := fun q =>
    if q = k then some initialValue
    else if q.val < k.val then some initialValue else none
  voted := fun i b =>
    if (i.val < j ∧ b = ballot k) then some initialValue
    else prevVoted m ballot k.val i.val b

/-- Alias: the state after `p2a k`, expressed with all p1b-loop state
    already materialised, matches `afterP2bJ k 0`. -/
theorem afterP2a_eq_afterP2bJ_zero (n m : Nat) (ballot : Fin m → Nat)
    (k : Fin m) :
    afterP2a n m ballot k = afterP2bJ n m ballot k 0 := by
  apply PaxosState.ext
  · -- prom: both ballot k (n is irrelevant since (x:Nat) < n always)
    funext x
    show (if (x : Nat) < n then ballot k else prevProm m ballot k.val) = ballot k
    simp [x.isLt]
  · -- acc
    funext x
    show prevAcc m ballot k.val =
         (if (x : Nat) < 0 then some (ballot k, initialValue) else prevAcc m ballot k.val)
    simp
  · -- got1b
    funext q i
    show (if q = k then decide ((i : Nat) < n) else decide (q.val < k.val)) =
         (if q = k then true else decide (q.val < k.val))
    by_cases hqk : q = k
    · subst hqk; simp [i.isLt]
    · simp [hqk]
  · -- rep
    funext q i
    show (if q = k then (if (i : Nat) < n then prevAcc m ballot k.val else none)
          else if q.val < k.val then prevAcc m ballot q.val else none) =
         (if q = k then prevAcc m ballot k.val
          else if q.val < k.val then prevAcc m ballot q.val else none)
    by_cases hqk : q = k
    · subst hqk; simp [i.isLt]
    · simp [hqk]
  · -- prop
    funext q
    show (setFn (fun q : Fin m => if q.val < k.val then some initialValue else none) k
            (some initialValue)) q =
         (if q = k then some initialValue
          else if q.val < k.val then some initialValue else none)
    simp only [setFn]
  · -- did2b
    funext q i
    show decide (q.val < k.val) =
         (if q = k then decide ((i : Nat) < 0) else decide (q.val < k.val))
    by_cases hqk : q = k
    · subst hqk; simp
    · simp [hqk]
  · -- voted: afterP2a only modifies prop; both sides use prevVoted k.val
    funext i b
    show prevVoted m ballot k.val i.val b =
         (if (i.val < 0 ∧ b = ballot k) then some initialValue
          else prevVoted m ballot k.val i.val b)
    simp

/-- Helper: `prevProm m ballot (k.val + 1) = ballot k`. -/
private theorem prevProm_succ {m : Nat} (ballot : Fin m → Nat) (k : Fin m) :
    prevProm m ballot (k.val + 1) = ballot k := by
  show (if h : k.val < m then ballot ⟨k.val, h⟩ else 0) = ballot k
  simp [k.isLt]

/-- Helper: `prevAcc m ballot (k.val + 1) = some (ballot k, initialValue)`. -/
private theorem prevAcc_succ {m : Nat} (ballot : Fin m → Nat) (k : Fin m) :
    prevAcc m ballot (k.val + 1) = some (ballot k, initialValue) := by
  show (if h : k.val < m then some (ballot ⟨k.val, h⟩, initialValue) else none)
       = some (ballot k, initialValue)
  simp [k.isLt]

/-- A proposer `q ≠ k` with `q.val < k.val + 1` must satisfy `q.val < k.val`. -/
private theorem lt_of_lt_succ_ne {m : Nat} {q k : Fin m}
    (hlt : q.val < k.val + 1) (hqk : q ≠ k) : q.val < k.val := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
  · exact h
  · exact absurd (Fin.ext h) hqk

theorem afterP2bJ_n_eq_stateAfter_succ (n m : Nat) (ballot : Fin m → Nat)
    (k : Fin m) :
    afterP2bJ n m ballot k n = stateAfter n m ballot (k.val + 1) := by
  apply PaxosState.ext
  · funext x
    show ballot k = prevProm m ballot (k.val + 1)
    rw [prevProm_succ]
  · funext x
    show (if (x : Nat) < n then some (ballot k, initialValue) else prevAcc m ballot k.val)
         = prevAcc m ballot (k.val + 1)
    rw [prevAcc_succ]
    simp [x.isLt]
  · funext q i
    show (if q = k then true else decide (q.val < k.val)) = decide (q.val < k.val + 1)
    by_cases hqk : q = k
    · subst hqk; simp
    · simp [hqk]
      constructor
      · intro h; exact Nat.lt_succ_of_lt h
      · intro h; exact lt_of_lt_succ_ne h hqk
  · funext q i
    show (if q = k then prevAcc m ballot k.val
          else if q.val < k.val then prevAcc m ballot q.val else none)
         = (if q.val < k.val + 1 then prevAcc m ballot q.val else none)
    by_cases hqk : q = k
    · subst hqk
      simp [Nat.lt_succ_self]
    · simp [hqk]
      by_cases hlt : q.val < k.val
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have hnlt : ¬ q.val < k.val + 1 := fun h => hlt (lt_of_lt_succ_ne h hqk)
        simp [hlt, hnlt]
  · funext q
    show (if q = k then some initialValue
          else if q.val < k.val then some initialValue else none)
         = (if q.val < k.val + 1 then some initialValue else none)
    by_cases hqk : q = k
    · subst hqk
      simp [Nat.lt_succ_self]
    · simp [hqk]
      by_cases hlt : q.val < k.val
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have hnlt : ¬ q.val < k.val + 1 := fun h => hlt (lt_of_lt_succ_ne h hqk)
        simp [hlt, hnlt]
  · funext q i
    show (if q = k then decide ((i : Nat) < n) else decide (q.val < k.val))
         = decide (q.val < k.val + 1)
    by_cases hqk : q = k
    · subst hqk; simp [i.isLt, Nat.lt_succ_self]
    · simp [hqk]
      constructor
      · intro h; exact Nat.lt_succ_of_lt h
      · intro h; exact lt_of_lt_succ_ne h hqk
  · -- voted: lhs is afterP2bJ k n; rhs is stateAfter (k.val + 1)
    funext i b
    show (if (i.val < n ∧ b = ballot k) then some initialValue
          else prevVoted m ballot k.val i.val b)
         = prevVoted m ballot (k.val + 1) i.val b
    unfold prevVoted
    by_cases hbk : b = ballot k
    · subst hbk
      have hkin : ∃ q : Fin m, q.val < k.val + 1 ∧ ballot q = ballot k :=
        ⟨k, Nat.lt_succ_self _, rfl⟩
      simp [i.isLt, hkin]
    · by_cases hex : ∃ q : Fin m, q.val < k.val ∧ ballot q = b
      · obtain ⟨q, hq1, hq2⟩ := hex
        have hex' : ∃ q : Fin m, q.val < k.val + 1 ∧ ballot q = b :=
          ⟨q, Nat.lt_succ_of_lt hq1, hq2⟩
        have hex0 : ∃ q : Fin m, q.val < k.val ∧ ballot q = b := ⟨q, hq1, hq2⟩
        simp [hbk, hex', hex0]
      · have hex' : ¬ ∃ q : Fin m, q.val < k.val + 1 ∧ ballot q = b := by
          rintro ⟨q, hq1, hq2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq1 with h | h
          · exact hex ⟨q, h, hq2⟩
          · apply hbk
            rw [← hq2]; congr 1; exact Fin.ext h
        simp [hbk, hex, hex']

/-! ### Single-step lemmas: each action extends the schedule state -/

/-- Monotonicity consequence: `prevProm m ballot k.val ≤ ballot k`. -/
private theorem prevProm_le_ballot {m : Nat} (ballot : Fin m → Nat)
    (h_mono : ∀ i j : Fin m, i.val < j.val → ballot i < ballot j) (k : Fin m) :
    prevProm m ballot k.val ≤ ballot k := by
  unfold prevProm
  cases hk : k.val with
  | zero => simp
  | succ k' =>
    have hk'lt : k' < m := by
      have : k.val < m := k.isLt
      omega
    simp [hk'lt]
    have hlt : (⟨k', hk'lt⟩ : Fin m).val < k.val := by
      show k' < k.val; omega
    exact Nat.le_of_lt (h_mono _ _ hlt)

/-- Step lemma: applying `p1b k ⟨j, hj⟩` at `afterP1bJ k j` produces
    `afterP1bJ k (j + 1)`, provided `j < n`. -/
theorem afterP1bJ_step {n m : Nat} (ballot : Fin m → Nat)
    (h_mono : ∀ i j : Fin m, i.val < j.val → ballot i < ballot j)
    (k : Fin m) (j : Nat) (hj : j < n) :
    paxosStep ballot (afterP1bJ n m ballot k j) (afterP1bJ n m ballot k (j + 1))
      (PaxosAction.p1b k ⟨j, hj⟩) := by
  unfold paxosStep
  simp only [GatedAction.fires]
  dsimp only [paxos]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- gate: got1b k ⟨j, hj⟩ = false
    show (if k = k then decide (j < j) else _) = false
    simp [Nat.lt_irrefl]
  · -- gate: prom ⟨j, hj⟩ ≤ ballot k
    show (if j < j then ballot k else prevProm m ballot k.val) ≤ ballot k
    simp [Nat.lt_irrefl]
    exact prevProm_le_ballot ballot h_mono k
  · -- transition: afterP1bJ k (j+1) = { afterP1bJ k j with prom := ..., got1b := ..., rep := ... }
    -- We prove this by PaxosState.ext, showing each field matches.
    -- Fields acc, prop, did2b are unchanged and match definitionally.
    show afterP1bJ n m ballot k (j + 1) =
      { afterP1bJ n m ballot k j with
          prom := setFn (afterP1bJ n m ballot k j).prom ⟨j, hj⟩ (ballot k)
          got1b := setFn (afterP1bJ n m ballot k j).got1b k
            (setFn ((afterP1bJ n m ballot k j).got1b k) ⟨j, hj⟩ true)
          rep := setFn (afterP1bJ n m ballot k j).rep k
            (setFn ((afterP1bJ n m ballot k j).rep k) ⟨j, hj⟩
              ((afterP1bJ n m ballot k j).acc ⟨j, hj⟩)) }
    apply PaxosState.ext
    · -- prom
      funext i
      show (if (i : Nat) < j + 1 then ballot k else prevProm m ballot k.val)
           = setFn (fun i : Fin n => if i.val < j then ballot k else prevProm m ballot k.val)
               ⟨j, hj⟩ (ballot k) i
      simp only [setFn]
      by_cases hij : i = ⟨j, hj⟩
      · subst hij; simp [Nat.lt_succ_self]
      · have hne : i.val ≠ j := fun h => hij (Fin.ext h)
        by_cases hlt : i.val < j
        · simp [hij, hlt, Nat.lt_succ_of_lt hlt]
        · have hnlt : ¬ i.val < j + 1 := fun h => hne (Nat.eq_of_lt_succ_of_not_lt h hlt)
          simp [hij, hlt, hnlt]
    · rfl
    · -- got1b
      funext q i
      simp only [setFn, afterP1bJ]
      by_cases hqk : q = k
      · subst hqk
        simp
        by_cases hij : i = ⟨j, hj⟩
        · subst hij; simp [Nat.lt_succ_self]
        · have hne : i.val ≠ j := fun h => hij (Fin.ext h)
          by_cases hlt : i.val < j
          · simp [hij, hlt, Nat.lt_succ_of_lt hlt]
          · have hnlt : ¬ i.val < j + 1 := fun h => hne (Nat.eq_of_lt_succ_of_not_lt h hlt)
            simp [hij, hlt, hnlt]
      · simp [hqk]
    · -- rep
      funext q i
      simp only [setFn, afterP1bJ]
      by_cases hqk : q = k
      · subst hqk
        simp
        by_cases hij : i = ⟨j, hj⟩
        · subst hij; simp [Nat.lt_succ_self]
        · have hne : i.val ≠ j := fun h => hij (Fin.ext h)
          by_cases hlt : i.val < j
          · simp [hij, hlt, Nat.lt_succ_of_lt hlt]
          · have hnlt : ¬ i.val < j + 1 := fun h => hne (Nat.eq_of_lt_succ_of_not_lt h hlt)
            simp [hij, hlt, hnlt]
      · simp [hqk]
    · rfl
    · rfl
    · rfl

/-- `majority` of the constant `true` function holds when `n ≥ 1`. -/
private theorem majority_all_true {n : Nat} (hn : 1 ≤ n) :
    majority (fun _ : Fin n => true) = true := by
  unfold majority countTrue
  have hlen : ((List.finRange n).filter (fun _ : Fin n => true)).length = n := by
    have : (List.finRange n).filter (fun _ : Fin n => true) = List.finRange n := by
      induction List.finRange n with
      | nil => rfl
      | cons x xs ih => simp [ih]
    rw [this, List.length_finRange]
  simp [hlen, decide_eq_true_eq]
  omega

/-- Step lemma for p2a: applying `p2a k` at `afterP1b k = afterP1bJ k n`
    produces `afterP2a k`. -/
theorem afterP1b_step_p2a {n m : Nat} (ballot : Fin m → Nat) (hn : 1 ≤ n) (k : Fin m) :
    paxosStep ballot (afterP1b n m ballot k) (afterP2a n m ballot k)
      (PaxosAction.p2a k) := by
  unfold paxosStep
  simp only [GatedAction.fires]
  dsimp only [paxos]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- gate: prop k = none
    show (if k.val < k.val then some initialValue else none) = none
    simp
  · -- gate: majority (got1b k) = true
    show majority (fun i : Fin n =>
      if k = k then decide ((i : Nat) < n) else decide (k.val < k.val)) = true
    have hsimp : (fun i : Fin n =>
        if k = k then decide ((i : Nat) < n) else decide (k.val < k.val))
        = (fun _ : Fin n => true) := by
      funext i; simp [i.isLt]
    rw [hsimp]
    exact majority_all_true hn
  · -- transition: ∃ v, s' = setFn-prop ∧ safeAt ballot s v (ballot k).
    -- Pick v = initialValue. State equality is rfl (afterP2a is exactly this setFn).
    -- safeAt: pick the full quorum (everyone), then for each acceptor, case-split on
    -- whether some earlier proposer (round < k) used ballot c.
    refine ⟨initialValue, rfl, ?_⟩
    intro c hc
    refine ⟨fun _ => true, majority_all_true hn, ?_⟩
    intro a _
    -- did2b q a = decide (q.val < k.val) at afterP1b
    -- prop q   = some initialValue iff q.val < k.val
    -- prom a   = ballot k (afterP1b sets prom for all i.val < n; i.val < n always)
    have hpromA : (afterP1b n m ballot k).prom a = ballot k := by
      show (if a.val < n then ballot k else _) = ballot k
      simp [a.isLt]
    by_cases hex : ∃ p : Fin m, ballot p = c ∧ p.val < k.val
    · -- votedFor: pick that p; did2b p a follows from p.val < k.val
      obtain ⟨p, hbp, hpk⟩ := hex
      left
      refine ⟨p, hbp, ?_, ?_⟩
      · show decide (p.val < k.val) = true
        exact decide_eq_true hpk
      · show (if p.val < k.val then some initialValue else none) = some initialValue
        simp [hpk]
    · -- wontVoteAt: no proposer with ballot c voted before k; prom a = ballot k > c
      right
      refine ⟨?_, ?_⟩
      · intro p hbp
        -- Goal: s.did2b p a ≠ true ⇔ decide (p.val < k.val) ≠ true
        -- From hex (negated): no p has ballot p = c ∧ p.val < k.val. Combined with
        -- hbp : ballot p = c, we get ¬ (p.val < k.val).
        intro hd
        have hpk : p.val < k.val := by
          show p.val < k.val; exact decide_eq_true_iff.mp hd
        exact hex ⟨p, hbp, hpk⟩
      · rw [hpromA]; exact hc

/-- Step lemma for p2b: applying `p2b k ⟨j, hj⟩` at `afterP2bJ k j`
    produces `afterP2bJ k (j + 1)`, provided `j < n`. -/
theorem afterP2bJ_step {n m : Nat} (ballot : Fin m → Nat)
    (k : Fin m) (j : Nat) (hj : j < n) :
    paxosStep ballot (afterP2bJ n m ballot k j) (afterP2bJ n m ballot k (j + 1))
      (PaxosAction.p2b k ⟨j, hj⟩) := by
  unfold paxosStep
  simp only [GatedAction.fires]
  dsimp only [paxos]
  refine ⟨⟨?_, ?_⟩, initialValue, ?_, ?_⟩
  · -- gate: did2b k ⟨j, hj⟩ = false
    show (if k = k then decide (j < j) else _) = false
    simp [Nat.lt_irrefl]
  · -- gate: prom ⟨j, hj⟩ ≤ ballot k
    show ballot k ≤ ballot k
    exact Nat.le_refl _
  · -- prop k = some initialValue
    show (if k = k then some initialValue else _) = some initialValue
    simp
  · -- transition: afterP2bJ k (j+1) = { afterP2bJ k j with prom, acc, did2b, voted updated }
    show afterP2bJ n m ballot k (j + 1) =
      { afterP2bJ n m ballot k j with
          prom := setFn (afterP2bJ n m ballot k j).prom ⟨j, hj⟩ (ballot k)
          acc := setFn (afterP2bJ n m ballot k j).acc ⟨j, hj⟩ (some (ballot k, initialValue))
          did2b := setFn (afterP2bJ n m ballot k j).did2b k
            (setFn ((afterP2bJ n m ballot k j).did2b k) ⟨j, hj⟩ true)
          voted := updateVoted (afterP2bJ n m ballot k j).voted ⟨j, hj⟩ (ballot k) initialValue }
    apply PaxosState.ext
    · -- prom: both ballot k
      funext i
      show ballot k = setFn (fun _ : Fin n => ballot k) ⟨j, hj⟩ (ballot k) i
      simp [setFn]
    · -- acc
      funext i
      show (if (i : Nat) < j + 1 then some (ballot k, initialValue)
            else prevAcc m ballot k.val)
           = setFn (fun i : Fin n =>
               if (i : Nat) < j then some (ballot k, initialValue)
               else prevAcc m ballot k.val)
             ⟨j, hj⟩ (some (ballot k, initialValue)) i
      simp only [setFn]
      by_cases hij : i = ⟨j, hj⟩
      · subst hij; simp [Nat.lt_succ_self]
      · have hne : i.val ≠ j := fun h => hij (Fin.ext h)
        by_cases hlt : i.val < j
        · simp [hij, hlt, Nat.lt_succ_of_lt hlt]
        · have hnlt : ¬ i.val < j + 1 := fun h => hne (Nat.eq_of_lt_succ_of_not_lt h hlt)
          simp [hij, hlt, hnlt]
    · rfl
    · rfl
    · rfl
    · -- did2b
      funext q i
      simp only [setFn, afterP2bJ]
      by_cases hqk : q = k
      · subst hqk
        simp
        by_cases hij : i = ⟨j, hj⟩
        · subst hij; simp [Nat.lt_succ_self]
        · have hne : i.val ≠ j := fun h => hij (Fin.ext h)
          by_cases hlt : i.val < j
          · simp [hij, hlt, Nat.lt_succ_of_lt hlt]
          · have hnlt : ¬ i.val < j + 1 := fun h => hne (Nat.eq_of_lt_succ_of_not_lt h hlt)
            simp [hij, hlt, hnlt]
      · simp [hqk]
    · -- voted
      funext x b
      show (if (x.val < j + 1 ∧ b = ballot k) then some initialValue
            else prevVoted m ballot k.val x.val b) =
           updateVoted (fun y c => if (y.val < j ∧ c = ballot k) then some initialValue
                                    else prevVoted m ballot k.val y.val c)
             ⟨j, hj⟩ (ballot k) initialValue x b
      simp only [updateVoted]
      by_cases hib : x = ⟨j, hj⟩ ∧ b = ballot k
      · obtain ⟨rfl, rfl⟩ := hib
        simp [Nat.lt_succ_self]
      · rw [if_neg hib]
        by_cases hbk : b = ballot k
        · subst hbk
          have hij : x ≠ ⟨j, hj⟩ := fun h => hib ⟨h, rfl⟩
          have hne : x.val ≠ j := fun h => hij (Fin.ext h)
          by_cases hlt : x.val < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have hnlt : ¬ x.val < j + 1 := fun h => hne (Nat.eq_of_lt_succ_of_not_lt h hlt)
            simp [hlt, hnlt]
        · simp [hbk]

/-! ### Loop lemmas: bundling inner p1b and p2b loops -/

/-- The list `[p1b k ⟨j, hj⟩, p1b k ⟨j+1, _⟩, ..., p1b k ⟨n-1, _⟩]`. -/
def p1bTail {n m : Nat} (k : Fin m) : (j : Nat) → j ≤ n → List (PaxosAction n m)
  | j, hjn =>
    if hlt : j < n then
      PaxosAction.p1b k ⟨j, hlt⟩ :: p1bTail k (j + 1) hlt
    else
      []
  termination_by j _ => n - j

/-- The list `[p2b k ⟨j, hj⟩, ..., p2b k ⟨n-1, _⟩]`. -/
def p2bTail {n m : Nat} (k : Fin m) : (j : Nat) → j ≤ n → List (PaxosAction n m)
  | j, hjn =>
    if hlt : j < n then
      PaxosAction.p2b k ⟨j, hlt⟩ :: p2bTail k (j + 1) hlt
    else
      []
  termination_by j _ => n - j

theorem p1bTail_length {n m : Nat} (k : Fin m) :
    ∀ (j : Nat) (hjn : j ≤ n), (p1bTail k j hjn).length = n - j
  | j, hjn => by
    unfold p1bTail
    by_cases hlt : j < n
    · simp [hlt, p1bTail_length k (j + 1) hlt]
      omega
    · simp [hlt]
      omega
  termination_by j _ => n - j

theorem p2bTail_length {n m : Nat} (k : Fin m) :
    ∀ (j : Nat) (hjn : j ≤ n), (p2bTail k j hjn).length = n - j
  | j, hjn => by
    unfold p2bTail
    by_cases hlt : j < n
    · simp [hlt, p2bTail_length k (j + 1) hlt]
      omega
    · simp [hlt]
      omega
  termination_by j _ => n - j

/-- Loop lemma: running `p1bTail k j` from `afterP1bJ k j` reaches `afterP1bJ k n`. -/
theorem stepsFrom_p1bTail {n m : Nat} (ballot : Fin m → Nat)
    (h_mono : ∀ i j : Fin m, i.val < j.val → ballot i < ballot j)
    (k : Fin m) :
    ∀ (j : Nat) (hjn : j ≤ n),
      PhaseCounting.StepsFrom (boundedPaxos n m ballot)
        (afterP1bJ n m ballot k j) (p1bTail k j hjn) (afterP1bJ n m ballot k n)
  | j, hjn => by
    unfold p1bTail
    by_cases hlt : j < n
    · simp only [hlt, dif_pos]
      have hstep := afterP1bJ_step ballot h_mono k j hlt
      have hrest := stepsFrom_p1bTail ballot h_mono k (j + 1) hlt
      exact PhaseCounting.StepsFrom.cons _ _ hstep hrest
    · simp only [hlt, dif_neg, not_false_eq_true]
      have hjn' : j = n := by omega
      subst hjn'
      exact PhaseCounting.StepsFrom.nil _
  termination_by j _ => n - j

/-- Loop lemma: running `p2bTail k j` from `afterP2bJ k j` reaches `afterP2bJ k n`. -/
theorem stepsFrom_p2bTail {n m : Nat} (ballot : Fin m → Nat) (k : Fin m) :
    ∀ (j : Nat) (hjn : j ≤ n),
      PhaseCounting.StepsFrom (boundedPaxos n m ballot)
        (afterP2bJ n m ballot k j) (p2bTail k j hjn) (afterP2bJ n m ballot k n)
  | j, hjn => by
    unfold p2bTail
    by_cases hlt : j < n
    · simp only [hlt, dif_pos]
      have hstep := afterP2bJ_step ballot k j hlt
      have hrest := stepsFrom_p2bTail ballot k (j + 1) hlt
      exact PhaseCounting.StepsFrom.cons _ _ hstep hrest
    · simp only [hlt, dif_neg, not_false_eq_true]
      have hjn' : j = n := by omega
      subst hjn'
      exact PhaseCounting.StepsFrom.nil _
  termination_by j _ => n - j

/-! ### Round schedule: `2n + 1` actions for one proposer -/

/-- Schedule of actions for one full round of proposer `k`. -/
def roundSchedule {n m : Nat} (k : Fin m) : List (PaxosAction n m) :=
  p1bTail (n := n) k 0 (Nat.zero_le _) ++
  [PaxosAction.p2a k] ++
  p2bTail (n := n) k 0 (Nat.zero_le _)

theorem roundSchedule_length {n m : Nat} (k : Fin m) :
    (@roundSchedule n m k).length = 2 * n + 1 := by
  unfold roundSchedule
  rw [List.length_append, List.length_append, List.length_singleton]
  rw [p1bTail_length, p2bTail_length]
  omega

/-- Round lemma: running `roundSchedule k` from `stateAfter k.val` reaches
    `stateAfter (k.val + 1)`. -/
theorem stepsFrom_round {n m : Nat} (ballot : Fin m → Nat)
    (h_mono : ∀ i j : Fin m, i.val < j.val → ballot i < ballot j)
    (hn : 1 ≤ n) (k : Fin m) :
    PhaseCounting.StepsFrom (boundedPaxos n m ballot)
      (stateAfter n m ballot k.val) (@roundSchedule n m k)
      (stateAfter n m ballot (k.val + 1)) := by
  unfold roundSchedule
  have h1 : PhaseCounting.StepsFrom (boundedPaxos n m ballot)
      (stateAfter n m ballot k.val) (p1bTail (n := n) k 0 (Nat.zero_le _))
      (afterP1b n m ballot k) := by
    rw [← afterP1bJ_zero n m ballot k]
    exact stepsFrom_p1bTail ballot h_mono k 0 (Nat.zero_le _)
  have h2 : PhaseCounting.StepsFrom (boundedPaxos n m ballot)
      (afterP1b n m ballot k) [PaxosAction.p2a k] (afterP2a n m ballot k) :=
    PhaseCounting.StepsFrom.cons _ _ (afterP1b_step_p2a ballot hn k)
      (PhaseCounting.StepsFrom.nil _)
  have h3 : PhaseCounting.StepsFrom (boundedPaxos n m ballot)
      (afterP2a n m ballot k) (p2bTail (n := n) k 0 (Nat.zero_le _))
      (stateAfter n m ballot (k.val + 1)) := by
    rw [afterP2a_eq_afterP2bJ_zero n m ballot k, ← afterP2bJ_n_eq_stateAfter_succ n m ballot k]
    exact stepsFrom_p2bTail ballot k 0 (Nat.zero_le _)
  exact stepsFrom_append (stepsFrom_append h1 h2) h3

/-! ### Outer induction: full schedule -/

/-- Schedule of actions for the first `k` proposers (for `k ≤ m`). -/
def tightSchedulePrefix (n m : Nat) : (k : Nat) → k ≤ m → List (PaxosAction n m)
  | 0, _ => []
  | k + 1, hk =>
    tightSchedulePrefix n m k (Nat.le_of_succ_le hk) ++
    @roundSchedule n m ⟨k, hk⟩

theorem tightSchedulePrefix_length (n m : Nat) :
    ∀ (k : Nat) (hk : k ≤ m),
      (tightSchedulePrefix n m k hk).length = k * (2 * n + 1)
  | 0, _ => by simp [tightSchedulePrefix]
  | k + 1, hk => by
    unfold tightSchedulePrefix
    rw [List.length_append, tightSchedulePrefix_length n m k (Nat.le_of_succ_le hk),
        roundSchedule_length, ← Nat.succ_mul]

/-- Outer induction: running the first `k` round schedules from
    `initialPaxos` reaches `stateAfter k`. -/
theorem stepsFrom_tightSchedulePrefix {n m : Nat} (ballot : Fin m → Nat)
    (h_mono : ∀ i j : Fin m, i.val < j.val → ballot i < ballot j) (hn : 1 ≤ n) :
    ∀ (k : Nat) (hk : k ≤ m),
      PhaseCounting.StepsFrom (boundedPaxos n m ballot)
        (initialPaxos n m) (tightSchedulePrefix n m k hk) (stateAfter n m ballot k)
  | 0, _ => by
    unfold tightSchedulePrefix
    rw [stateAfter_zero]
    exact PhaseCounting.StepsFrom.nil _
  | k + 1, hk => by
    unfold tightSchedulePrefix
    have hprev := stepsFrom_tightSchedulePrefix ballot h_mono hn k (Nat.le_of_succ_le hk)
    have hround := stepsFrom_round ballot h_mono hn (⟨k, hk⟩ : Fin m)
    exact stepsFrom_append hprev hround

/-- The full tightness schedule: concatenation of all `m` round schedules. -/
def tightSchedule (n m : Nat) : List (PaxosAction n m) :=
  tightSchedulePrefix n m m (Nat.le_refl _)

theorem tightSchedule_length (n m : Nat) :
    (tightSchedule n m).length = 2 * m * n + m := by
  unfold tightSchedule
  rw [tightSchedulePrefix_length]
  rw [Nat.mul_add, Nat.mul_one]
  rw [show m * (2 * n) = 2 * m * n from by
    rw [Nat.mul_comm m (2 * n), Nat.mul_assoc, Nat.mul_comm n m, ← Nat.mul_assoc]]

/-- **Tightness schedule validity.** -/
theorem tightSchedule_valid {n m : Nat} (ballot : Fin m → Nat)
    (h_mono : ∀ i j : Fin m, i.val < j.val → ballot i < ballot j) (hn : 1 ≤ n) :
    PhaseCounting.StepsFrom (boundedPaxos n m ballot)
      (initialPaxos n m) (tightSchedule n m) (stateAfter n m ballot m) :=
  stepsFrom_tightSchedulePrefix ballot h_mono hn m (Nat.le_refl _)

/-- **Unconditional tightness of the phase-counter bound.** For every
    strictly monotone `ballot` and `n ≥ 1`, there exists a reachable
    state whose phase counter equals `2·m·n + m`. -/
theorem boundedPaxos_bound_tight {n m : Nat} (ballot : Fin m → Nat)
    (h_mono : ∀ i j : Fin m, i.val < j.val → ballot i < ballot j)
    (hn : 1 ≤ n) :
    ∃ s acts,
      PhaseCounting.StepsFrom (boundedPaxos n m ballot) (initialPaxos n m) acts s ∧
      acts.length = 2 * m * n + m ∧
      phaseCounter s = 2 * m * n + m := by
  refine ⟨stateAfter n m ballot m, tightSchedule n m, ?_, ?_, ?_⟩
  · exact tightSchedule_valid ballot h_mono hn
  · exact tightSchedule_length n m
  · exact boundedPaxos_bound_tight_of_schedule ballot
      (tightSchedule_valid ballot h_mono hn) (tightSchedule_length n m)
/-! # Proposer crash/recover for atomic single-decree Paxos

    This file adds a **proposer crash** action to the atomic Paxos model
    (`Leslie.Examples.Paxos`) and proves that safety (agreement) is preserved.

    ## Crash action

    A proposer `c` may crash provided `prop c = none` — i.e., it has not yet
    committed to a value (Phase 2a has not fired). The crash resets the
    proposer's volatile Phase 1 state:

      - `got1b c` is reset to all-false,
      - `rep c` is reset to all-none.

    All other state (acceptor fields `prom`, `acc`; other proposers' fields;
    the crashed proposer's `prop` and `did2b`) is left unchanged.

    ## Why this guard is necessary

    The invariant field `hJ : ∀ q, prop q ≠ none → majority (got1b q)` links
    `prop` to `got1b`. Resetting `got1b c` while `prop c ≠ none` would break
    `hJ`. And resetting `prop c` to `none` (to dodge `hJ`) would break `hB`
    and `hSafe`, whose existential conclusions witness proposers with matching
    `prop`. The guard `prop c = none` is thus the strongest crash that
    preserves the 10-field `PaxosInv`.

    Under this guard, the invariant implies `did2b c i = false` for all `i`
    (by `hA`), so all fields referencing `did2b c` are vacuously preserved.

    ## What this models

    A proposer that crashes during Phase 1 — after collecting some Phase 1b
    responses but before choosing a value. On recovery it can restart Phase 1
    from scratch. This is a standard failure mode in Paxos deployments.

    No Mathlib. No sorries.
-/

open TLA

namespace PaxosTextbookN.Crash

open PaxosTextbookN

/-! ## Section 1: Crash action definition -/

/-- The post-crash state for proposer `c`: `got1b c` and `rep c` are reset;
    everything else is unchanged. -/
def crashState {n m : Nat} (c : Fin m) (s : PaxosState n m) : PaxosState n m :=
  { s with
    got1b := setFn s.got1b c (fun _ => false)
    rep := setFn s.rep c (fun _ => none) }

/-- A proposer crash fires when the proposer has not yet proposed. -/
def crashFires {n m : Nat} (c : Fin m) (s s' : PaxosState n m) : Prop :=
  s.prop c = none ∧ s' = crashState c s

/-! ## Section 2: Invariant preservation under crash -/

/-- Key observation: under the invariant with `prop c = none`, the proposer `c`
    has `did2b c i = false` for all acceptors `i`. -/
theorem did2b_false_of_prop_none {n m : Nat} {ballot : Fin m → Nat}
    {s : PaxosState n m} (hinv : PaxosInv ballot s) (c : Fin m)
    (hprop : s.prop c = none) : ∀ i, s.did2b c i = false := by
  intro i
  by_contra h
  have h' : s.did2b c i = true := by
    cases hb : s.did2b c i <;> simp_all
  have := hinv.hA c i h'
  exact this hprop

/-- Crash preserves the Paxos invariant. -/
theorem paxos_inv_crash {n m : Nat} {ballot : Fin m → Nat}
    (s : PaxosState n m) (c : Fin m)
    (hinv : PaxosInv ballot s)
    (hprop : s.prop c = none) :
    PaxosInv ballot (crashState c s) := by
  have hdid : ∀ i, s.did2b c i = false := did2b_false_of_prop_none hinv c hprop
  unfold crashState
  exact {
    hA := by
      intro p i hdi
      simp only at hdi
      exact hinv.hA p i hdi
    hB := by
      intro i b v hacc
      simp only at hacc
      exact hinv.hB i b v hacc
    hC := by
      intro q i b v hrep
      simp only at hrep
      by_cases hqc : q = c
      · subst hqc; simp [setFn] at hrep
      · have : setFn s.rep c (fun _ => none) q = s.rep q := by simp [setFn, hqc]
        rw [this] at hrep
        exact hinv.hC q i b v hrep
    hD := by
      intro p i hgot
      simp only at hgot
      by_cases hpc : p = c
      · subst hpc; simp [setFn] at hgot
      · have : setFn s.got1b c (fun _ => false) p = s.got1b p := by simp [setFn, hpc]
        rw [this] at hgot
        exact hinv.hD p i hgot
    hE := by
      intro i b v hacc
      simp only at hacc
      exact hinv.hE i b v hacc
    hG := by
      intro p q i hdi hgot hlt
      simp only at hdi hgot
      -- did2b is unchanged, so if p = c, did2b c i = false → contradiction
      by_cases hpc : p = c
      · subst hpc; simp [hdid i] at hdi
      · -- got1b: if q = c, got1b c is reset → false → contradiction
        by_cases hqc : q = c
        · subst hqc; simp [setFn] at hgot
        · have hg : s.got1b q i = true := by
            have : setFn s.got1b c (fun _ => false) q = s.got1b q := by simp [setFn, hqc]
            rw [this] at hgot; exact hgot
          obtain ⟨b, w, hrep, hge⟩ := hinv.hG p q i hdi hg hlt
          refine ⟨b, w, ?_, hge⟩
          show (setFn s.rep c (fun _ => none)) q i = some (b, w)
          simp [setFn, hqc]; exact hrep
    hH := by
      intro p i hdi
      simp only at hdi
      by_cases hpc : p = c
      · subst hpc; simp [hdid i] at hdi
      · exact hinv.hH p i hdi
    hJ := by
      intro q hq
      simp only at hq
      by_cases hqc : q = c
      · subst hqc; exact absurd hprop hq
      · have hmaj := hinv.hJ q hq
        -- majority (got1b q) where got1b is modified only at c ≠ q
        have : setFn s.got1b c (fun _ => false) q = s.got1b q := by simp [setFn, hqc]
        show majority (setFn s.got1b c (fun _ => false) q) = true
        rw [this]; exact hmaj
    hF := by
      intro q i b v hrep
      simp only at hrep
      by_cases hqc : q = c
      · subst hqc; simp [setFn] at hrep
      · have : setFn s.rep c (fun _ => none) q = s.rep q := by simp [setFn, hqc]
        rw [this] at hrep
        exact hinv.hF q i b v hrep
    hSafe := by
      intro q v hpq c' hc
      simp only at hpq
      exact hinv.hSafe q v hpq c' hc
    hL := by
      intro i b v hv; exact hinv.hL i b v hv
    hK := by
      intro i b v hv; exact hinv.hK i b v hv
    hN := by
      intro p i hdi; exact hinv.hN p i hdi
    hAcc := by
      intro i b v hacc; exact hinv.hAcc i b v hacc
    hM := by
      intro q i b v hrep
      by_cases hqc : q = c
      · subst hqc; simp [setFn] at hrep
      · simp only [setFn, hqc, ite_false] at hrep
        exact hinv.hM q i b v hrep
    hVotDid := by
      intro i b v hv; exact hinv.hVotDid i b v hv
  }

/-! ## Section 3: Extended reachability with crash -/

/-- Extended reachable states: normal Paxos steps or proposer crashes. -/
inductive ExtendedReachable {n m : Nat} (ballot : Fin m → Nat) :
    PaxosState n m → Prop where
  | init : ∀ s, (paxos n m ballot).init s → ExtendedReachable ballot s
  | step : ∀ {s s'}, ExtendedReachable ballot s →
      (∃ a, ((paxos n m ballot).actions a).fires s s') →
      ExtendedReachable ballot s'
  | crash : ∀ {s s'} (c : Fin m), ExtendedReachable ballot s →
      crashFires c s s' → ExtendedReachable ballot s'

/-- Every extended-reachable state satisfies the Paxos invariant. -/
theorem paxosInv_of_extendedReachable {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot) :
    ∀ {s : PaxosState n m}, ExtendedReachable ballot s → PaxosInv ballot s
  | _, .init s hinit => paxos_inv_init ballot s hinit
  | _, .step hr hstep =>
      paxos_inv_next h_inj _ _ (paxosInv_of_extendedReachable h_inj hr) hstep
  | _, .crash c hr ⟨hprop, rfl⟩ =>
      paxos_inv_crash _ c (paxosInv_of_extendedReachable h_inj hr) hprop

/-- Agreement holds for all extended-reachable states. -/
theorem extended_agreement {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot)
    {s : PaxosState n m} (hr : ExtendedReachable ballot s) :
    ∀ p q, majority (s.did2b p) = true → majority (s.did2b q) = true →
    s.prop p = s.prop q :=
  agreement h_inj (paxosInv_of_extendedReachable h_inj hr)

end PaxosTextbookN.Crash
