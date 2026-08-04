import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Minimmit abstract core: one-round Byzantine voting

The consensus skeleton of **Multimmit** (Lewis-Pye & O'Grady, *Multimmit:
Extending Blocks for Faster Finality*, arXiv:2607.21021) is **Minimmit**
(arXiv:2508.10862): a view-based Byzantine SMR in which a single round of
voting suffices for finality, assuming `n ≥ 5f + 1` processors of which at
most `f` are faulty. The paper's Section 3.1 states the safety core in terms
of notarisations — sets of messages actually sent, whether or not any
processor assembles the corresponding certificate:

* an **L-notarisation** for a view-`v` leader block `b` is a set of `n - f`
  votes for `b` (finality);
* a **V-notarisation** for `v` contains at least `2f + 1` votes for a common
  block (the "mini" licence to advance and build on that block);
* a **nullification** for `v` is `2f + 1` nullify shares.

This file formalises the *abstract message-history core* of that skeleton:
the Byzantine fault model, the one-vote-per-view and vote–novote exclusivity
invariants, and the two quorum-intersection safety theorems that carry all of
the one-round argument:

1. **Per-view agreement** (`Agree`, Lemma 4/consistency fragment): no two
   different blocks both receive `n - f` votes in the same view.
2. **Designation** (`Designation`): if a block receives `n - f` votes, no
   other block in the same view can receive `2f + 1` votes.

The remaining safety structure (no-nullification for a notarised view — Lemma
5, which needs message-send times; the leader-chain argument — Lemma 6, which
needs proposals/V-QCs and nullifications; and the Multimmit chain layer with
DA-certificates and the `Tips`/`Tips*` extraction functions) is discussed in
`docs/research/multimmit-exploration.md` as the natural next slices.

## Modelling choices

* Byzantine processors are a `Finset Proc` **constant** `Byz` (a TLA+
  `CONSTANT`), with `ValidParams n f Byz` the cardinality/range assumptions.
  Correct processors are those outside `Byz`.
* Message histories are represented per processor per view: `votes p v` is
  the set of blocks `p` voted for in view `v` (at most one for a correct
  processor), `novotes p v` and `nullifies p v` the one-shot messages.
* Faulty processors are free to rewrite their own vote history (`Byzantine`
  action); the invariants only constrain correct processors, so safety
  holds for *any* adversary behaviour.
-/

namespace TlaDsl.Examples.Minimmit

abbrev Proc := Nat
abbrev View := Nat
abbrev Block := Nat

/-- The local message histories: per-processor, per-view vote sets, novote
flags and nullify-share flags. -/
@[ext]
structure St where
  votes : Proc → View → Finset Block
  novotes : Proc → View → Prop
  nullifies : Proc → View → Prop

tla_var St votes novotes nullifies

/-- Parameter validity: at most `f` Byzantine processors among the first `n`,
with `n ≥ 5f + 1` (the one-round-finality threshold of Minimmit/Multimmit). -/
def ValidParams (n f : Nat) (Byz : Finset Proc) : Prop :=
  Byz ⊆ Finset.range n ∧ Byz.card ≤ f ∧ 5 * f + 1 ≤ n

/-! ## The message vocabulary -/

/-- Processor `p` voted for block `b` in view `v`. -/
@[simp] def Voted (s : St) (p : Proc) (v : View) (b : Block) : Prop :=
  b ∈ s.votes p v

/-- `b` receives an L-notarisation in view `v`: at least `n - f` processors
vote for it. -/
def LNotarised (s : St) (n f : Nat) (v : View) (b : Block) : Prop :=
  ∃ Q : Finset Proc, Q ⊆ Finset.range n ∧ n - f ≤ Q.card ∧
    ∀ p : Proc, p ∈ Q → Voted s p v b

/-- `b` receives at least `2f + 1` votes in view `v` — the vote part of a
V-notarisation. -/
def VNotarised (s : St) (n f : Nat) (v : View) (b : Block) : Prop :=
  ∃ Q : Finset Proc, Q ⊆ Finset.range n ∧ 2 * f + 1 ≤ Q.card ∧
    ∀ p : Proc, p ∈ Q → Voted s p v b

/-! ## The invariants -/

/-- Correct processors vote for at most one block per view. -/
@[simp] def OneVotePerView (s : St) (Byz : Finset Proc) : Prop :=
  ∀ p : Proc, p ∉ Byz → ∀ v : View, (s.votes p v).card ≤ 1

/-- Correct processors never both vote in and novote the same view. -/
@[simp] def VoteNovoteExcl (s : St) (Byz : Finset Proc) : Prop :=
  ∀ p : Proc, p ∉ Byz → ∀ v : View, s.novotes p v → s.votes p v = ∅

@[simp] def Inv (Byz : Finset Proc) : Tla.StatePred St :=
  fun s => OneVotePerView s Byz ∧ VoteNovoteExcl s Byz

/-! ## The protocol (in the DSL) -/

@[simp] def Init : Tla.StatePred St :=
  [p| (∀ p : Proc, ∀ v : View, (votes[p][v] : Finset Block) = ∅) ∧
      (∀ p : Proc, ∀ v : View, ¬ novotes[p][v]) ∧
      (∀ p : Proc, ∀ v : View, ¬ nullifies[p][v])]

/-- The state after correct processor `p` votes for `b` in view `v`. -/
def voteFor (s : St) (p : Proc) (v : View) (b : Block) : St :=
  { s with votes := Function.update s.votes p (Function.update (s.votes p) v {b}) }

/-- The state after `p` sends a novote for view `v`. -/
def novote (s : St) (p : Proc) (v : View) : St :=
  { s with novotes := Function.update s.novotes p (fun w : View => s.novotes p w ∨ w = v) }

/-- The state after `p` sends a nullify share for view `v`. -/
def nullify (s : St) (p : Proc) (v : View) : St :=
  { s with nullifies := Function.update s.nullifies p (fun w : View => s.nullifies p w ∨ w = v) }

/-- The state after Byzantine `p` rewrites its votes in view `v` arbitrarily. -/
def byz (s : St) (p : Proc) (v : View) (B : Finset Block) : St :=
  { s with votes := Function.update s.votes p (Function.update (s.votes p) v B) }

/-- A correct processor votes for `b` in view `v`: not Byzantine, has not yet
voted or novoted in that view. -/
@[simp] def Vote (Byz : Finset Proc) (p : Proc) (v : View) (b : Block) : Tla.Action St :=
  [c| Byz, p | (votes[p][v] : Finset Block) = ∅ ∧ ¬ novotes[p][v] ∧
      votes' = Function.update votes p (Function.update (votes p) v ({b} : Finset Block)) ∧
      novotes' = novotes ∧ nullifies' = nullifies]

/-- A correct processor that times out in view `v` without voting sends a
novote. -/
@[simp] def Novote (Byz : Finset Proc) (p : Proc) (v : View) : Tla.Action St :=
  [c| Byz, p | (votes[p][v] : Finset Block) = ∅ ∧ ¬ novotes[p][v] ∧
      novotes' = Function.update novotes p (fun w : View => novotes[p][w] ∨ w = v) ∧
      votes' = votes ∧ nullifies' = nullifies]

/-- A correct processor sends a nullify share for view `v` (at most once). -/
@[simp] def Nullify (Byz : Finset Proc) (p : Proc) (v : View) : Tla.Action St :=
  [c| Byz, p | ¬ nullifies[p][v] ∧
      nullifies' = Function.update nullifies p (fun w : View => nullifies[p][w] ∨ w = v) ∧
      votes' = votes ∧ novotes' = novotes]

/-- A Byzantine processor may rewrite its own votes in a view arbitrarily.
The invariants constrain only correct processors, so this needs no guard
beyond membership in `Byz`. -/
@[simp] def Byzantine (Byz : Finset Proc) (p : Proc) (v : View) (B : Finset Block) : Tla.Action St :=
  [a| p ∈ Byz ∧
      votes' = Function.update votes p (Function.update (votes p) v B) ∧
      novotes' = novotes ∧ nullifies' = nullifies]

@[simp] def Next (_n _f : Nat) (Byz : Finset Proc) : Tla.Action St :=
  [a| ∃ p : Proc, ∃ v : View,
      (∃ b : Block, Vote Byz p v b) ∨ Novote Byz p v ∨ Nullify Byz p v ∨
      ∃ B : Finset Block, Byzantine Byz p v B]

def Spec (n f : Nat) (Byz : Finset Proc) : Tla.Pred St :=
  [t| Init ∧ □[Next n f Byz]_vars]

/-! ## The quorum-intersection arguments -/

/-- If an intersection of two voter sets has more than `f` members, it
contains a correct processor. -/
lemma overlap_has_correct {f : Nat} {Byz Q1 Q2 : Finset Proc}
    (hByz : Byz.card ≤ f) (hgt : f < (Q1 ∩ Q2).card) :
    ∃ p : Proc, p ∈ Q1 ∩ Q2 ∧ p ∉ Byz := by
  by_contra h
  have hsub : Q1 ∩ Q2 ⊆ Byz := by
    intro p hp
    by_contra hpnot
    exact h ⟨p, hp, hpnot⟩
  have hle : (Q1 ∩ Q2).card ≤ Byz.card := Finset.card_le_card hsub
  omega

/-- An `(n - f)`-voter set and a `(2f + 1)`-voter set overlap in a correct
processor: `(n - f) + (2f + 1) - n = f + 1 > f`. -/
lemma mini_intersect {n f : Nat} {Byz Q1 Q2 : Finset Proc}
    (hQ1sub : Q1 ⊆ Finset.range n) (hQ1 : n - f ≤ Q1.card)
    (hQ2sub : Q2 ⊆ Finset.range n) (hQ2 : 2 * f + 1 ≤ Q2.card)
    (hByz : Byz.card ≤ f) :
    ∃ p : Proc, p ∈ Q1 ∩ Q2 ∧ p ∉ Byz := by
  apply overlap_has_correct hByz
  have hunion_sub : Q1 ∪ Q2 ⊆ Finset.range n := Finset.union_subset hQ1sub hQ2sub
  have hunion_le : (Q1 ∪ Q2).card ≤ n := by
    simpa [Finset.card_range] using Finset.card_le_card hunion_sub
  have hsum : (Q1 ∪ Q2).card + (Q1 ∩ Q2).card = Q1.card + Q2.card :=
    Finset.card_union_add_card_inter Q1 Q2
  omega

/-- Two `(n - f)`-voter sets overlap in a correct processor under
`n ≥ 5f + 1`: `2(n - f) - n = n - 2f ≥ 3f + 1 > f`. -/
lemma large_intersect {n f : Nat} {Byz Q1 Q2 : Finset Proc}
    (hQ1sub : Q1 ⊆ Finset.range n) (hQ1 : n - f ≤ Q1.card)
    (hQ2sub : Q2 ⊆ Finset.range n) (hQ2 : n - f ≤ Q2.card)
    (hByz : Byz.card ≤ f) (hn : 5 * f + 1 ≤ n) :
    ∃ p : Proc, p ∈ Q1 ∩ Q2 ∧ p ∉ Byz := by
  apply overlap_has_correct hByz
  have hunion_sub : Q1 ∪ Q2 ⊆ Finset.range n := Finset.union_subset hQ1sub hQ2sub
  have hunion_le : (Q1 ∪ Q2).card ≤ n := by
    simpa [Finset.card_range] using Finset.card_le_card hunion_sub
  have hsum : (Q1 ∪ Q2).card + (Q1 ∩ Q2).card = Q1.card + Q2.card :=
    Finset.card_union_add_card_inter Q1 Q2
  omega

/-! ## One-vote-per-view is inductive -/

lemma card_le_one_eq {s : St} {p : Proc} {v : View} {b b' : Block}
    (h : (s.votes p v).card ≤ 1) (hb : b ∈ s.votes p v) (hb' : b' ∈ s.votes p v) :
    b = b' := by
  exact (Finset.card_le_one.mp h) b hb b' hb'

theorem oneVote_vote {s : St} {p : Proc} {v : View} {b : Block} {Byz : Finset Proc}
    (hInv : OneVotePerView s Byz) : OneVotePerView (voteFor s p v b) Byz := by
  intro p' hp' v'
  by_cases hp : p' = p
  · subst p
    by_cases hv : v' = v
    · subst v
      simp [voteFor]
    · simpa [voteFor, hv] using hInv p' hp' v'
  · simpa [voteFor, hp] using hInv p' hp' v'

theorem oneVote_novote {s : St} {p : Proc} {v : View} {Byz : Finset Proc}
    (hInv : OneVotePerView s Byz) : OneVotePerView (novote s p v) Byz := by
  intro p' hp' v'
  simpa [novote] using hInv p' hp' v'

theorem oneVote_nullify {s : St} {p : Proc} {v : View} {Byz : Finset Proc}
    (hInv : OneVotePerView s Byz) : OneVotePerView (nullify s p v) Byz := by
  intro p' hp' v'
  simpa [nullify] using hInv p' hp' v'

theorem oneVote_byz {s : St} {p : Proc} {v : View} {B : Finset Block} {Byz : Finset Proc}
    (hByz : p ∈ Byz) (hInv : OneVotePerView s Byz) : OneVotePerView (byz s p v B) Byz := by
  intro p' hp' v'
  by_cases hp : p' = p
  · subst p
    exfalso
    exact hp' hByz
  · simpa [byz, hp] using hInv p' hp' v'

/-! ## Vote–novote exclusivity is inductive -/

theorem excl_vote {s : St} {p : Proc} {v : View} {b : Block} {Byz : Finset Proc}
    (hNoNovote : ¬ s.novotes p v) (hInv : VoteNovoteExcl s Byz) :
    VoteNovoteExcl (voteFor s p v b) Byz := by
  intro p' hp' v' hnov
  by_cases hp : p' = p
  · subst p
    by_cases hv : v' = v
    · subst v
      exfalso
      exact hNoNovote (by simpa [voteFor] using hnov)
    · simpa [voteFor, hv] using hInv p' hp' v' hnov
  · simpa [voteFor, hp] using hInv p' hp' v' hnov

theorem excl_novote {s : St} {p : Proc} {v : View} {Byz : Finset Proc}
    (hNoVote : s.votes p v = ∅) (hInv : VoteNovoteExcl s Byz) :
    VoteNovoteExcl (novote s p v) Byz := by
  intro p' hp' v' hnov
  by_cases hp : p' = p
  · subst p
    by_cases hv : v' = v
    · subst v
      simpa [novote] using hNoVote
    · have hnov' : s.novotes p' v' := by
        simpa [novote, hv] using hnov
      simpa [novote, hv] using hInv p' hp' v' hnov'
  · have hnov' : s.novotes p' v' := by
      simpa [novote, hp] using hnov
    simpa [novote, hp] using hInv p' hp' v' hnov'

theorem excl_nullify {s : St} {p : Proc} {v : View} {Byz : Finset Proc}
    (hInv : VoteNovoteExcl s Byz) : VoteNovoteExcl (nullify s p v) Byz := by
  intro p' hp' v' hnov
  simpa [nullify] using hInv p' hp' v' hnov

theorem excl_byz {s : St} {p : Proc} {v : View} {B : Finset Block} {Byz : Finset Proc}
    (hByz : p ∈ Byz) (hInv : VoteNovoteExcl s Byz) : VoteNovoteExcl (byz s p v B) Byz := by
  intro p' hp' v' hnov
  by_cases hp : p' = p
  · subst p
    exfalso
    exact hp' hByz
  · simpa [byz, hp] using hInv p' hp' v' hnov

/-! ## The invariant is inductive -/

theorem init_inv {Byz : Finset Proc} {s : St} (h : Init s) : Inv Byz s := by
  tla_unfold
  rcases h with ⟨hVotes, hNovotes, hNullifies⟩
  constructor
  · intro p hp v
    simp [hVotes p v]
  · intro p hp v hnov
    exfalso
    exact hNovotes p v hnov

theorem vote_inv {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View} {b : Block}
    (hstep : Vote Byz p v b s s') (hInv : Inv Byz s) : Inv Byz s' := by
  tla_unfold
  rcases hstep with ⟨hNotByz, hNoVote, hNoNovote, hVotes', hNovotes', hNullifies'⟩
  have hs' : s' = voteFor s p v b := by
    ext <;> simp [voteFor, hVotes', hNovotes', hNullifies']
  subst s'
  constructor
  · exact oneVote_vote hInv.1
  · exact excl_vote hNoNovote hInv.2

theorem novote_inv {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View}
    (hstep : Novote Byz p v s s') (hInv : Inv Byz s) : Inv Byz s' := by
  tla_unfold
  rcases hstep with ⟨hNotByz, hNoVote, hNoNovote, hNovotes', hVotes', hNullifies'⟩
  have hs' : s' = novote s p v := by
    ext <;> simp [novote, hVotes', hNovotes', hNullifies']
  subst s'
  constructor
  · exact oneVote_novote hInv.1
  · exact excl_novote hNoVote hInv.2

theorem nullify_inv {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View}
    (hstep : Nullify Byz p v s s') (hInv : Inv Byz s) : Inv Byz s' := by
  tla_unfold
  rcases hstep with ⟨hNotByz, hNoNullify, hNullifies', hVotes', hNovotes'⟩
  have hs' : s' = nullify s p v := by
    ext <;> simp [nullify, hVotes', hNovotes', hNullifies']
  subst s'
  constructor
  · exact oneVote_nullify hInv.1
  · exact excl_nullify hInv.2

theorem byz_inv {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View} {B : Finset Block}
    (hstep : Byzantine Byz p v B s s') (hInv : Inv Byz s) : Inv Byz s' := by
  tla_unfold
  rcases hstep with ⟨hByz, hVotes', hNovotes', hNullifies'⟩
  have hs' : s' = byz s p v B := by
    ext <;> simp [byz, hVotes', hNovotes', hNullifies']
  subst s'
  constructor
  · exact oneVote_byz hByz hInv.1
  · exact excl_byz hByz hInv.2

theorem next_inv (n f : Nat) (Byz : Finset Proc) :
    ∀ s s' : St, Next n f Byz s s' → Inv Byz s → Inv Byz s' := by
  intro s s' hstep hInv
  unfold Next at hstep
  rcases hstep with ⟨p, v, hstep⟩
  rcases hstep with hvote | hnov | hnull | hbyz
  · rcases hvote with ⟨b, hvote⟩
    exact vote_inv hvote hInv
  · exact novote_inv hnov hInv
  · exact nullify_inv hnull hInv
  · rcases hbyz with ⟨B, hbyz⟩
    exact byz_inv hbyz hInv

theorem stutter_inv {Byz : Finset Proc} : ∀ s s' : St, vars s' = vars s → Inv Byz s → Inv Byz s' := by
  intro s s' hstut hInv
  tla_unfold
  cases hstut
  exact hInv

theorem spec_entails_inv (n f : Nat) (Byz : Finset Proc) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n f Byz) vars)) ⊢ □ ⌜ Inv Byz ⌝ := by
  apply Tla.init_invariant_stut
  · intro s hs
    exact init_inv hs
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact next_inv n f Byz s s' hnext hInv
    · exact stutter_inv s s' hstut hInv

/-! ## The safety theorems -/

/-- No two different blocks both receive `n - f` votes in the same view. -/
@[simp] def Agree (n f : Nat) : Tla.StatePred St :=
  [p| ∀ v : View, ∀ b : Block, ∀ b' : Block,
      LNotarised n f v b → LNotarised n f v b' → b = b']

/-- If a block receives `n - f` votes in a view, no other block in that view
receives `2f + 1` votes. -/
@[simp] def Designation (n f : Nat) : Tla.StatePred St :=
  [p| ∀ v : View, ∀ b : Block, ∀ b' : Block,
      LNotarised n f v b → VNotarised n f v b' → b = b']

/-- Per-view agreement: two L-notarisations in the same view must be for the
same block. The two voter sets overlap in a correct processor (n ≥ 5f+1),
which by one-vote-per-view voted for both blocks. -/
theorem notarised_agree {n f : Nat} {Byz : Finset Proc} {s : St}
    (hInv : Inv Byz s) (hn : 5 * f + 1 ≤ n) (hByz : Byz.card ≤ f)
    {v : View} {b b' : Block}
    (hb : LNotarised s n f v b) (hb' : LNotarised s n f v b') : b = b' := by
  rcases hb with ⟨Q, hQsub, hQcard, hQvotes⟩
  rcases hb' with ⟨Q', hQ'sub, hQ'card, hQ'votes⟩
  rcases large_intersect hQsub hQcard hQ'sub hQ'card hByz hn with ⟨p, hp, hpbyz⟩
  have hv1 : b ∈ s.votes p v := hQvotes p (Finset.mem_inter.mp hp).1
  have hv2 : b' ∈ s.votes p v := hQ'votes p (Finset.mem_inter.mp hp).2
  exact card_le_one_eq (hInv.1 p hpbyz v) hv1 hv2

/-- Designation: the `(n - f)` and `(2f + 1)` voter sets overlap in a
correct processor, which voted for both blocks. -/
theorem designation_thm {n f : Nat} {Byz : Finset Proc} {s : St}
    (hInv : Inv Byz s) (hByz : Byz.card ≤ f)
    {v : View} {b b' : Block}
    (hb : LNotarised s n f v b) (hsmall : VNotarised s n f v b') : b = b' := by
  rcases hb with ⟨Q, hQsub, hQcard, hQvotes⟩
  rcases hsmall with ⟨Q', hQ'sub, hQ'card, hQ'votes⟩
  rcases mini_intersect hQsub hQcard hQ'sub hQ'card hByz with ⟨p, hp, hpbyz⟩
  have hv1 : b ∈ s.votes p v := hQvotes p (Finset.mem_inter.mp hp).1
  have hv2 : b' ∈ s.votes p v := hQ'votes p (Finset.mem_inter.mp hp).2
  exact card_le_one_eq (hInv.1 p hpbyz v) hv1 hv2

/-- The invariant implies per-view agreement. -/
theorem agree_of_inv (n f : Nat) (Byz : Finset Proc)
    (hn : 5 * f + 1 ≤ n) (hByz : Byz.card ≤ f) :
    ∀ s : St, Inv Byz s → Agree n f s := by
  intro s hInv v b b' hb hb'
  exact notarised_agree hInv hn hByz hb hb'

/-- The invariant implies designation. -/
theorem designation_of_inv (n f : Nat) (Byz : Finset Proc)
    (hByz : Byz.card ≤ f) :
    ∀ s : St, Inv Byz s → Designation n f s := by
  intro s hInv v b b' hb hsmall
  exact designation_thm hInv hByz hb hsmall

/-- The Minimmit/Multimmit one-round safety theorem: no two different blocks
are ever L-notarised in the same view. -/
theorem spec_entails_agree (n f : Nat) (Byz : Finset Proc) (hP : ValidParams n f Byz) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n f Byz) vars)) ⊢ □ ⌜ Agree n f ⌝ := by
  rcases hP with ⟨hByzSub, hByzCard, hn⟩
  intro e he
  have hInv : Tla.always (Tla.statePred (Inv Byz)) e := spec_entails_inv n f Byz e he
  intro k
  have hk : Inv Byz ((e.drop k) 0) := hInv k
  exact agree_of_inv n f Byz hn hByzCard ((e.drop k) 0) hk

/-- Designation holds throughout every execution. -/
theorem spec_entails_designation (n f : Nat) (Byz : Finset Proc) (hP : ValidParams n f Byz) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n f Byz) vars)) ⊢ □ ⌜ Designation n f ⌝ := by
  rcases hP with ⟨hByzSub, hByzCard, hn⟩
  intro e he
  have hInv : Tla.always (Tla.statePred (Inv Byz)) e := spec_entails_inv n f Byz e he
  intro k
  have hk : Inv Byz ((e.drop k) 0) := hInv k
  exact designation_of_inv n f Byz hByzCard ((e.drop k) 0) hk

end TlaDsl.Examples.Minimmit
