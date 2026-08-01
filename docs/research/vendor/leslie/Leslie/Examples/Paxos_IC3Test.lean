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

namespace PaxosIC3Test

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

/-! ### Paxos Specification -/

def paxos (n m : Nat) (ballot : Fin m → Nat) : ActionSpec (PaxosState n m) (PaxosAction n m) where
  init := fun s =>
    (∀ i, s.prom i = 0) ∧
    (∀ i, s.acc i = none) ∧
    (∀ p i, s.got1b p i = false) ∧
    (∀ p i, s.rep p i = none) ∧
    (∀ p, s.prop p = none) ∧
    (∀ p i, s.did2b p i = false)
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
            -- Paxos constraint: adopt value from highest-ballot report in quorum
            (∀ i b w, s.got1b p i = true → s.rep p i = some (b, w) →
              (∀ j b' w', s.got1b p j = true → s.rep p j = some (b', w') → b' ≤ b) →
              v = w)
      }
    | .p2b p i => {
        gate := fun s => s.did2b p i = false ∧ s.prom i ≤ ballot p
        transition := fun s s' =>
          ∃ v, s.prop p = some v ∧
            s' = { s with
              prom := setFn s.prom i (ballot p)
              acc := setFn s.acc i (some (ballot p, v))
              did2b := setFn s.did2b p (setFn (s.did2b p) i true) }
      }

/-! ### SafeAt predicate (Lamport)

    `votedFor a c v`: acceptor `a` voted for value `v` at ballot `c`.
    `wontVoteAt a c`: acceptor `a` has not voted at ballot `c` and never will
    (because its promise exceeds `c`).
    `safeAt v b`: for every ballot `c < b`, there is a quorum where each
    member either voted for `v` at `c`, or will never vote at `c`.

    SafeAt is monotone: votes and promises only increase, strengthening both
    disjuncts. This makes it an inductive invariant. -/

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
  hH : ∀ p i, s.did2b p i = true → ∃ b v, s.acc i = some (b, v) ∧ b ≥ ballot p
  hJ : ∀ q, s.prop q ≠ none → majority (s.got1b q) = true
  hSafe : ∀ q v, s.prop q = some v → safeAt ballot s v (ballot q)
  -- IC3-appended conjuncts:
  hG : ∀ q i p, ballot q > ballot p → s.got1b q i = true → s.did2b p i = true →
       ∃ b w, s.rep q i = some (b, w) ∧ b ≥ ballot p
  hK : ∀ q i b w, s.rep q i = some (b, w) → b ≤ ballot q

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
    -- k voted at ballot p', so WontVoteAt is false
    rcases hQprop k hQk with ⟨r, hrb, hdr, hrv⟩ | ⟨hnotvote, _⟩
    · -- VotedFor(k, ballot p', v): prop r = some v, ballot r = ballot p'
      have : r = p' := h_inj hrb
      subst this; rw [hrv, hv]
    · -- WontVoteAt(k, ballot p'): impossible since k voted at ballot p'
      have : ballot p' = ballot p' := rfl
      exact absurd hdk (hnotvote p' this)

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
  intro s ⟨_, hacc, hgot, hrep, hprop, hdid⟩
  exact {
    hA := by intro p i hi; simp [hdid p i] at hi
    hB := by intro i _ _ hi; simp [hacc i] at hi
    hC := by intro q i _ _ hi; simp [hrep q i] at hi
    hD := by intro p i hi; simp [hgot p i] at hi
    hE := by intro i _ _ hi; simp [hacc i] at hi
    hH := by intro p i hi; simp [hdid p i] at hi
    hJ := by intro q hq; simp [hprop q] at hq
    hSafe := by intro q _ hq; simp [hprop q] at hq
    hG := by intro q i _ _ hgi; simp [hgot q i] at hgi
    hK := by intro q i _ _ hri; simp [hrep q i] at hri
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
  · exact hinv.hH  -- hH: did2b/acc unchanged
  · -- hJ: got1b gains entries → majority preserved
    intro q hq
    by_cases hq' : q = p
    · subst hq'; simp [setFn]
      exact majority_setFn_true_of_majority _ i (hinv.hJ q hq)
    · simp [setFn, hq']; exact hinv.hJ q hq
  · -- hSafe: did2b/prop unchanged, prom ↑ → old Q still works
    intro q v hprop c hc
    obtain ⟨Q, hQmaj, hQprop⟩ := hinv.hSafe q v hprop c hc
    refine ⟨Q, hQmaj, fun a ha => ?_⟩
    rcases hQprop a ha with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
    · exact Or.inl ⟨r, hrb, hdr, hrv⟩
    · right; refine ⟨hnv, ?_⟩
      by_cases ha : a = i
      · subst ha; simp [setFn]; omega
      · simp [setFn, ha]; exact hprom
  · -- hG: new got1b p i and new rep p i = acc i. Use hH to get report bound.
    intro q' j r hgt hgot hd
    by_cases hq : q' = p
    · subst hq; by_cases hj : j = i
      · subst hj; simp [setFn] at hgot ⊢
        obtain ⟨b, v, hacc, hge⟩ := hinv.hH r j hd
        exact ⟨b, ⟨v, hacc⟩, hge⟩
      · simp [setFn, hj] at hgot ⊢
        obtain ⟨b, w, hrep, hge⟩ := hinv.hG q' j r hgt hgot hd
        exact ⟨b, ⟨w, hrep⟩, hge⟩
    · simp [setFn, hq] at hgot ⊢
      obtain ⟨b, w, hrep, hge⟩ := hinv.hG q' j r hgt hgot hd
      exact ⟨b, ⟨w, hrep⟩, hge⟩
  · -- hK: new rep p i = acc i; for (q,j) ≠ (p,i) unchanged.
    intro q' j b w hrep
    by_cases hq : q' = p
    · subst hq; by_cases hj : j = i
      · subst hj; simp [setFn] at hrep
        have := hinv.hE j b w hrep
        omega
      · simp [setFn, hj] at hrep
        exact hinv.hK q' j b w hrep
    · simp [setFn, hq] at hrep
      exact hinv.hK q' j b w hrep

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
    (h_inj : Function.Injective ballot)
    (s : PaxosState n m) (p : Fin m) (v : Value)
    (hinv : PaxosInv ballot s)
    (hg1 : s.prop p = none)
    (hg2 : majority (s.got1b p) = true)
    (hconstr : ∀ (i : Fin n) (b : Nat) (w : Value),
        s.got1b p i = true → s.rep p i = some (b, w) →
        (∀ (j : Fin n) (b' : Nat) (w' : Value), s.got1b p j = true → s.rep p j = some (b', w') → b' ≤ b) →
        v = w) :
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
  · exact hinv.hH  -- hH: did2b/acc unchanged
  · -- hJ: prop only gains at p (= some v ≠ none); got1b unchanged
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp [setFn] at hq; exact hg2
    · simp [setFn, hqp] at hq; exact hinv.hJ q hq
  · -- hSafe
    intro q w hprop c hc
    simp only [setFn] at hprop
    by_cases hqp : q = p
    · subst hqp
      simp only [ite_true] at hprop
      obtain ⟨rfl⟩ : w = v := Option.some.inj hprop.symm
      -- safeAt ballot (s with prop := setFn s.prop q (some v)) v (ballot q)
      -- For each c < ballot q, find a witness quorum
      -- Use classical reasoning to case-split on whether anyone in got1b q voted at c
      by_cases hexvote : ∃ a : Fin n, s.got1b q a = true ∧
          ∃ r : Fin m, ballot r = c ∧ s.did2b r a = true
      · -- Someone in the quorum voted at c; need max report ballot argument.
        -- Step 1: Extract witness from hexvote
        obtain ⟨a₀, hgot₀, r₀, hrbal₀, hdid₀⟩ := hexvote
        -- Step 2: hG gives a report at a₀ with ballot ≥ c
        have hgt₀ : ballot q > ballot r₀ := hrbal₀ ▸ hc
        obtain ⟨b₀, w₀, hrep₀, hge₀⟩ := hinv.hG q a₀ r₀ hgt₀ hgot₀ hdid₀
        -- Step 3: Find the max report in q's quorum
        -- Define: P j ≡ got1b q j = true ∧ ∃ b w, rep q j = some (b, w)
        -- f j = the ballot of the report at j (or 0)
        let f : Fin n → Nat := fun j => match s.rep q j with | some (b, _) => b | none => 0
        have hPa₀ : s.got1b q a₀ = true ∧ ∃ b w, s.rep q a₀ = some (b, w) :=
          ⟨hgot₀, b₀, w₀, hrep₀⟩
        have hfbound : ∀ j, (s.got1b q j = true ∧ ∃ b w, s.rep q j = some (b, w)) →
            f j ≤ ballot q := by
          intro j ⟨hgj, b, w, hrj⟩
          show f j ≤ ballot q
          simp only [f, hrj]
          exact hinv.hK q j b w hrj
        obtain ⟨amax, ⟨hgot_max, bmax, wmax, hrep_max⟩, hmax_all⟩ :=
          fin_exists_max f (fun j => s.got1b q j = true ∧ ∃ b w, s.rep q j = some (b, w))
            (ballot q) hfbound a₀ hPa₀
        -- Step 4: By hconstr, v = wmax
        have hv_eq : v = wmax := by
          apply hconstr amax bmax wmax hgot_max hrep_max
          intro j b' w' hgotj hrepj
          have := hmax_all j ⟨hgotj, b', w', hrepj⟩
          simp only [f, hrep_max, hrepj] at this
          exact this
        -- Step 5: By hC, there exists tmax with ballot tmax = bmax, prop tmax = some wmax
        obtain ⟨tmax, htbal, htprop⟩ := hinv.hC q amax bmax wmax hrep_max
        -- Step 6: bmax < ballot q
        have hbmax_lt : bmax < ballot q := by
          by_contra h
          have hbmax_ge : bmax ≥ ballot q := Nat.not_lt.mp h
          have hbmax_le : bmax ≤ ballot q := hinv.hK q amax bmax wmax hrep_max
          have hbmax_eq : bmax = ballot q := Nat.le_antisymm hbmax_le hbmax_ge
          have : tmax = q := h_inj (htbal ▸ hbmax_eq)
          subst this
          simp [hg1] at htprop
        -- bmax ≥ c (since bmax ≥ b₀ ≥ c)
        have hbmax_ge_b₀ : bmax ≥ b₀ := by
          have := hmax_all a₀ hPa₀
          simp only [f, hrep_max, hrep₀] at this
          omega
        have hbmax_ge_c : bmax ≥ c := by omega
        -- Step 7: Case split on bmax = c vs bmax > c
        by_cases hbc : bmax = c
        · -- Case bmax = c: tmax is the unique proposer at ballot c
          -- By injectivity: tmax = r₀ (since ballot tmax = bmax = c = ballot r₀)
          have htmax_eq : tmax = r₀ := h_inj (by omega)
          -- prop tmax = some wmax, so prop r₀ = some wmax
          rw [htmax_eq] at htprop
          -- Use Q = got1b q
          refine ⟨s.got1b q, hg2, fun a ha => ?_⟩
          -- For each a in got1b q: either voted at c or wontVoteAt
          by_cases hvoted : ∃ r, ballot r = c ∧ s.did2b r a = true
          · -- a voted at c: show votedFor a c v
            left
            obtain ⟨r, hrb, hdr⟩ := hvoted
            -- r is unique at ballot c: r = r₀
            have hr_eq : r = r₀ := h_inj (by omega)
            rw [hr_eq] at hdr
            refine ⟨r₀, hrbal₀, hdr, ?_⟩
            -- prop r₀ in post-state: setFn s.prop q (some v)
            -- r₀ ≠ q since ballot r₀ = c < ballot q
            have hr₀_ne_q : r₀ ≠ q := by intro heq; subst heq; omega
            simp [setFn, hr₀_ne_q]
            -- need s.prop r₀ = some v: htprop says some wmax, hv_eq says v = wmax
            rw [hv_eq]; exact htprop
          · -- a didn't vote at c: wontVoteAt
            right
            refine ⟨fun r hrb hdr => hvoted ⟨r, hrb, hdr⟩, ?_⟩
            exact Nat.lt_of_lt_of_le hc (hinv.hD q a ha)
        · -- Case bmax > c: c < bmax
          have hc_lt_bmax : c < bmax := by omega
          -- From pre-state hSafe for tmax: safeAt wmax bmax
          obtain ⟨Qt, hQtmaj, hQtprop⟩ := hinv.hSafe tmax wmax htprop c (htbal ▸ hc_lt_bmax)
          -- Qt works in post-state too; goal needs v not wmax, but hv_eq : v = wmax
          refine ⟨Qt, hQtmaj, fun a ha => ?_⟩
          rcases hQtprop a ha with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
          · -- votedFor wmax in pre-state → votedFor v in post-state
            -- prop only changed at q. For r with ballot r = c: r ≠ q (c < ballot q)
            left
            have hr_ne_q : r ≠ q := by intro heq; subst heq; omega
            -- hrv : s.prop r = some wmax, need setFn s.prop q (some v) r = some v
            refine ⟨r, hrb, hdr, ?_⟩
            simp [setFn, hr_ne_q]
            rw [hv_eq]; exact hrv
          · -- wontVoteAt: did2b/prom unchanged
            exact Or.inr ⟨hnv, hprom⟩
      · -- No one in got1b q voted at c: use Q = got1b q, all wontVoteAt
        refine ⟨s.got1b q, hg2, fun a ha => ?_⟩
        right
        exact ⟨fun r hrb hdid => hexvote ⟨a, ha, r, hrb, hdid⟩,
               Nat.lt_of_lt_of_le hc (hinv.hD q a ha)⟩
    · -- q ≠ p: prop q unchanged (setFn s.prop p (some v) q = s.prop q)
      simp only [hqp, ite_false] at hprop
      obtain ⟨Q, hQmaj, hQprop⟩ := hinv.hSafe q w hprop c hc
      refine ⟨Q, hQmaj, fun a ha => ?_⟩
      rcases hQprop a ha with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
      · -- votedFor: prop r was some w ≠ none, so r ≠ p (since old prop p = none)
        have hrp : r ≠ p := fun h => by subst h; simp [hg1] at hrv
        exact Or.inl ⟨r, hrb, hdr, by simp [setFn, hrp, hrv]⟩
      · exact Or.inr ⟨hnv, hprom⟩
  · exact hinv.hG  -- hG: got1b/did2b/rep unchanged
  · exact hinv.hK  -- hK: rep unchanged

private theorem paxos_inv_next_p2b {n m : Nat} {ballot : Fin m → Nat}
    (s : PaxosState n m) (p : Fin m) (i : Fin n)
    (hinv : PaxosInv ballot s)
    (hg1 : s.did2b p i = false)
    (hg2 : s.prom i ≤ ballot p)
    (v : Value)
    (hp : s.prop p = some v) :
    PaxosInv ballot { s with
      prom := setFn s.prom i (ballot p)
      acc := setFn s.acc i (some (ballot p, v))
      did2b := setFn s.did2b p (setFn (s.did2b p) i true) } := by
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
  · -- hSafe: old Q witnesses still work in new state.
    -- votedFor: did2b only gained (p,i). Old votes persist.
    -- wontVoteAt: prom ↑, and if a = i and ballot p = c: old prom i > c contradicts gate prom i ≤ ballot p = c.
    intro q w hprop c hc
    -- prop unchanged in new state
    obtain ⟨Q, hQmaj, hQprop⟩ := hinv.hSafe q w hprop c hc
    refine ⟨Q, hQmaj, fun a ha => ?_⟩
    rcases hQprop a ha with ⟨r, hrb, hdr, hrv⟩ | ⟨hnv, hprom⟩
    · -- votedFor in old state → votedFor in new state
      -- new did2b r a: setFn (setFn (s.did2b p)) only changes (p, i). Old entry preserved.
      apply Or.inl
      refine ⟨r, hrb, ?_, hrv⟩
      show setFn s.did2b p (setFn (s.did2b p) i true) r a = true
      simp only [setFn]
      by_cases hrp : r = p
      · subst hrp; simp only [ite_true]
        -- need setFn (s.did2b p) i true a = true
        -- old hdr : s.did2b r a = true = s.did2b p a = true
        simp only [setFn]
        by_cases hai : a = i
        · subst hai; simp only [ite_true]
        · simp only [hai, ite_false]; exact hdr
      · simp only [hrp, ite_false]; exact hdr
    · -- wontVoteAt in old state → wontVoteAt in new state
      right
      refine ⟨fun r hrb_eq => ?_, ?_⟩
      · -- no new vote at c for a
        show setFn s.did2b p (setFn (s.did2b p) i true) r a ≠ true
        simp only [setFn]
        by_cases hrp : r = p
        · subst hrp; simp only [ite_true]
          simp only [setFn]
          by_cases hai : a = i
          · subst hai; simp only [ite_true]
            -- ballot p = c, old wontVoteAt: prom i > c. Gate: prom i ≤ ballot p = c. Contradiction.
            exfalso; omega
          · simp only [hai, ite_false]; exact hnv r hrb_eq
        · simp only [hrp, ite_false]; exact hnv r hrb_eq
      · -- prom a > c: prom i ↑ (only helps)
        show setFn s.prom i (ballot p) a > c
        by_cases hai : a = i
        · subst hai; simp only [setFn, ite_true]; omega
        · simp only [setFn, hai, ite_false]; exact hprom
  · -- hG: got1b/rep unchanged; did2b gained (p,i).
    -- In the (r=p, j=i) case, ballot q > ballot p contradicts hD + p2b gate.
    intro q j r hgt hgot hd
    simp only [setFn] at hd
    by_cases hrp : r = p
    · subst hrp; simp only [ite_true] at hd
      by_cases hji : j = i
      · subst hji
        -- hD: got1b q i → prom i ≥ ballot q. Gate: prom i ≤ ballot p. So ballot q ≤ ballot p.
        have hprom_ge : s.prom j ≥ ballot q := hinv.hD q j hgot
        exact absurd (Nat.lt_of_lt_of_le hgt (Nat.le_trans hprom_ge hg2)) (Nat.lt_irrefl _)
      · simp only [setFn, hji, ite_false] at hd
        exact hinv.hG q j r hgt hgot hd
    · simp only [hrp, ite_false] at hd
      exact hinv.hG q j r hgt hgot hd
  · exact hinv.hK  -- hK: rep unchanged

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
    exact paxos_inv_next_p2b s p i hinv hg1 hg2 v hp

theorem paxos_init_preserved {n m : Nat} (ballot : Fin m → Nat) :
    ∀ s, (paxos n m ballot).init s → consensus.init (paxos_ref s) := by
  intro s ⟨_, _, _, _, hprop, hdid⟩
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
        did2b := setFn s.did2b p (setFn (s.did2b p) i true) }
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
    have hinv' : PaxosInv ballot s' := paxos_inv_next_p2b s p i hinv hg1 hg2 v hp
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

end PaxosIC3Test
