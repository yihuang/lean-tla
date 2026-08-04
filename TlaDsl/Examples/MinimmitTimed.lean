import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/- The `linter.unusedSimpArgs` heuristic misfires on nested `addMsg`-wrapper
unfolds (`addNullify`/`addNovote` need both themselves and `addMsg` in the
simp set); the proof genuinely needs the flagged argument. -/
set_option linter.unusedSimpArgs false

/-! # Minimmit with message send times: Lemma 5 (no nullification)

The paper's Lemma 5 is the one argument in the Minimmit/Multimmit safety
core that is *not* a plain inductive invariant: a correct processor that has
voted for the view's block may still nullify the view later (via the
evidence rule, lines 16-19 of Algorithm 4.2), so "voted ⟹ never nullifies"
is false as a static statement. The proof picks the **least timeslot** at
which a correct voter nullifies and uses that all `2f+1` of its evidence
messages were sent *strictly before* that time. This file adds the one thing
the pool-only model cannot express — message send times — and proves
`no_nullification` (Lemma 5).

## How time is modelled

* `Msg` is the set of protocol messages (a vote for a block, a novote, a
  nullify share).
* The state is a message log `sent : Msg → Option Nat` (the send time of
  each message, if ever sent) plus a clock `time : Nat`. Every action
  advances the clock by one (`time' = time + 1`) and stamps the message it
  sends with the new time. "Sent strictly before" is therefore literally
  `<` on the stamps.
* `SentLeTime` (`stamps ≤ now`), `OneVote`, and `Excl` are the ported
  invariants; `EvidenceBefore` is the *causal* invariant that makes the
  least-time argument go: if a correct processor voted for `b` in `v` and
  its nullify was sent at time `t`, then it holds a `2f+1`-member evidence
  set (nullifies, novotes, or votes for other blocks) all sent strictly
  before `t`, with the ordering enforced for correct evidence senders.

`no_nullification` then runs the paper's argument: given an L-notarisation
for `b` in `v`, strong induction on the nullify time shows no correct voter
for `b` ever nullifies (its evidence's correct senders must all be
non-voters, of which there are at most `f`, plus at most `f` faulty — fewer
than `2f+1`), so a nullification's `2f+1` shares cannot all exist.
-/

namespace TlaDsl.Examples.MinimmitTimed

abbrev Proc := Nat
abbrev View := Nat
abbrev Block := Nat

/-- A protocol message: a vote for a block, a novote, or a nullify share. -/
inductive Msg where
  | vote (p : Proc) (v : View) (b : Block)
  | novote (p : Proc) (v : View)
  | nullify (p : Proc) (v : View)
deriving DecidableEq

/-- The state: the message log with per-message send times, and the current
timeslot. -/
@[ext]
structure St where
  sent : Msg → Option Nat
  time : Nat

tla_var St sent time

/-- Parameter validity: at most `f` Byzantine among the first `n`
processors, with `n ≥ 5f + 1`. -/
def ValidParams (n f : Nat) (Byz : Finset Proc) : Prop :=
  Byz ⊆ Finset.range n ∧ Byz.card ≤ f ∧ 5 * f + 1 ≤ n

/-- Message `m` has been sent (at some time). -/
def Sent (s : St) (m : Msg) : Prop := ∃ t : Nat, s.sent m = some t

/-- `b` receives an L-notarisation in view `v`: at least `n - f`
processors voted for it. -/
def Notarised (s : St) (n f : Nat) (v : View) (b : Block) : Prop :=
  ∃ Q : Finset Proc, Q ⊆ Finset.range n ∧ n - f ≤ Q.card ∧
    ∀ p : Proc, p ∈ Q → Sent s (Msg.vote p v b)

/-- View `v` receives a nullification: at least `2f + 1` processors sent
nullify shares for it. -/
def Nullified (s : St) (n f : Nat) (v : View) : Prop :=
  ∃ Q : Finset Proc, Q ⊆ Finset.range n ∧ 2 * f + 1 ≤ Q.card ∧
    ∀ p : Proc, p ∈ Q → Sent s (Msg.nullify p v)

/-! ## The protocol -/

@[simp] def Init : Tla.StatePred St :=
  [p| (∀ m : Msg, sent[m] = none) ∧ time = 0]

/-- The state after adding message `m` at time `t`. -/
def addMsg (s : St) (m : Msg) (t : Nat) : St :=
  { s with sent := Function.update s.sent m (some t), time := t }

def addVote (s : St) (p : Proc) (v : View) (b : Block) (t : Nat) : St :=
  addMsg s (Msg.vote p v b) t

def addNovote (s : St) (p : Proc) (v : View) (t : Nat) : St :=
  addMsg s (Msg.novote p v) t

def addNullify (s : St) (p : Proc) (v : View) (t : Nat) : St :=
  addMsg s (Msg.nullify p v) t

/-- A correct processor votes for `b` in view `v`: not Byzantine, has not
voted, novoted or nullified in `v`. -/
@[simp] def Vote (Byz : Finset Proc) (p : Proc) (v : View) (b : Block) : Tla.Action St :=
  [a| p ∉ Byz ∧ sent (Msg.vote p v b) = none ∧
      (∀ b0 : Block, b0 ≠ b → sent (Msg.vote p v b0) = none) ∧
      ¬ Sent (Msg.novote p v) ∧ ¬ Sent (Msg.nullify p v) ∧
      time' = time + 1 ∧
      sent' = Function.update sent (Msg.vote p v b) (some time')]

/-- A correct processor that times out in view `v` without voting sends a
novote and a nullify share. -/
@[simp] def NullifyTimeout (Byz : Finset Proc) (p : Proc) (v : View) : Tla.Action St :=
  [a| p ∉ Byz ∧ (∀ b : Block, sent (Msg.vote p v b) = none) ∧
      sent (Msg.novote p v) = none ∧ sent (Msg.nullify p v) = none ∧
      time' = time + 1 ∧
      sent' = Function.update (Function.update sent (Msg.novote p v) (some time')) (Msg.nullify p v) (some time')]

/-- A correct processor that voted for `b` in `v` nullifies `v` upon
holding `2f+1` evidence messages by distinct processors: nullify shares,
novotes, or votes for blocks other than `b`. -/
@[simp] def NullifyEvidence (n f : Nat) (Byz : Finset Proc) (p : Proc) (v : View) (b : Block) : Tla.Action St :=
  [a| p ∉ Byz ∧ Sent (Msg.vote p v b) ∧ sent (Msg.nullify p v) = none ∧
      (∃ E : Finset Proc, E ⊆ Finset.range n ∧ 2 * f + 1 ≤ E.card ∧ p ∉ E ∧
        ∀ q : Proc, q ∈ E →
          Sent (Msg.nullify q v) ∨ Sent (Msg.novote q v) ∨
          ∃ b0 : Block, b0 ≠ b ∧ Sent (Msg.vote q v b0)) ∧
      time' = time + 1 ∧
      sent' = Function.update sent (Msg.nullify p v) (some time')]

/-- A Byzantine processor may send any of its own (not yet sent) messages
for view `v`. -/
@[simp] def Byzantine (Byz : Finset Proc) (p : Proc) (v : View) : Tla.Action St :=
  [a| p ∈ Byz ∧ time' = time + 1 ∧
      ∃ m : Msg,
        sent[m] = none ∧
        ((∃ b : Block, m = Msg.vote p v b) ∨ m = Msg.novote p v ∨ m = Msg.nullify p v) ∧
        sent' = Function.update sent m (some time')]

@[simp] def Next (n f : Nat) (Byz : Finset Proc) : Tla.Action St :=
  [a| ∃ p : Proc, ∃ v : View,
      (∃ b : Block, Vote Byz p v b) ∨ NullifyTimeout Byz p v ∨
      (∃ b : Block, NullifyEvidence n f Byz p v b) ∨ Byzantine Byz p v]

def Spec (n f : Nat) (Byz : Finset Proc) : Tla.Pred St :=
  [t| Init ∧ □[Next n f Byz]_vars]

/-! ## The invariants -/

/-- Every sent message is stamped no later than the current time. -/
@[simp] def SentLeTime (s : St) : Prop :=
  ∀ m : Msg, ∀ t : Nat, s.sent m = some t → t ≤ s.time

/-- A correct processor votes for at most one block per view. -/
@[simp] def OneVote (s : St) (Byz : Finset Proc) : Prop :=
  ∀ p : Proc, p ∉ Byz → ∀ v : View, ∀ b b' : Block,
    Sent s (Msg.vote p v b) → Sent s (Msg.vote p v b') → b = b'

/-- A correct processor never both novotes and votes in a view. -/
@[simp] def Excl (s : St) (Byz : Finset Proc) : Prop :=
  ∀ p : Proc, p ∉ Byz → ∀ v : View,
    Sent s (Msg.novote p v) → ∀ b : Block, ¬ Sent s (Msg.vote p v b)

/-- The causal invariant behind Lemma 5: if a correct processor voted for
`b` in `v` and its nullify was sent at time `t`, it holds a `2f+1`-member
evidence set whose messages were all sent strictly before `t` (for correct
evidence senders). -/
@[simp] def EvidenceBefore (s : St) (n f : Nat) (Byz : Finset Proc) : Prop :=
  ∀ p : Proc, p ∉ Byz → ∀ v : View, ∀ b : Block, ∀ t : Nat,
    Sent s (Msg.vote p v b) → s.sent (Msg.nullify p v) = some t →
    ∃ E : Finset Proc,
      E ⊆ Finset.range n ∧ 2 * f + 1 ≤ E.card ∧ p ∉ E ∧
      (∀ q : Proc, q ∈ E →
        (∃ tq : Nat, s.sent (Msg.nullify q v) = some tq ∧ tq < t) ∨
        Sent s (Msg.novote q v) ∨
          ∃ b' : Block, b' ≠ b ∧ Sent s (Msg.vote q v b'))

@[simp] def Inv (n f : Nat) (Byz : Finset Proc) : Tla.StatePred St :=
  fun s => SentLeTime s ∧ OneVote s Byz ∧ Excl s Byz ∧ EvidenceBefore s n f Byz

/-! ## Adding a message preserves the invariants -/

theorem addMsg_sentLeTime {s : St} {m : Msg} {t : Nat} (h : SentLeTime s) (hle : s.time ≤ t) :
    SentLeTime (addMsg s m t) := by
  intro m' t' hmt
  by_cases hmm : m' = m
  · subst m'
    simp [addMsg] at hmt ⊢
    omega
  · have h' : s.sent m' = some t' := by simpa [addMsg, hmm] using hmt
    have hle' : t' ≤ s.time := h m' t' h'
    simpa [addMsg] using le_trans hle' hle

/-- A message of processor `p` for view `v` (the Byzantine shape). -/
private def IsMsgOf (p : Proc) (v : View) (m : Msg) : Prop :=
  (∃ b : Block, m = Msg.vote p v b) ∨ m = Msg.novote p v ∨ m = Msg.nullify p v

private lemma vote_ne_of_msg {p p' : Proc} {v v' : View} {b : Block} {m : Msg}
    (hne : p' ≠ p) (hm : IsMsgOf p v m) : Msg.vote p' v' b ≠ m := by
  intro heq
  rcases hm with ⟨b0, hmb⟩ | hnov | hnull
  · exact hne (by injection (heq.trans hmb))
  · exact Msg.noConfusion (heq.trans hnov)
  · exact Msg.noConfusion (heq.trans hnull)

private lemma novote_ne_of_msg {p p' : Proc} {v v' : View} {m : Msg}
    (hne : p' ≠ p) (hm : IsMsgOf p v m) : Msg.novote p' v' ≠ m := by
  intro heq
  rcases hm with ⟨b0, hmb⟩ | hnov | hnull
  · exact Msg.noConfusion (heq.trans hmb)
  · exact hne (by injection (heq.trans hnov))
  · exact Msg.noConfusion (heq.trans hnull)

private lemma nullify_ne_of_msg {p p' : Proc} {v v' : View} {m : Msg}
    (hne : p' ≠ p) (hm : IsMsgOf p v m) : Msg.nullify p' v' ≠ m := by
  intro heq
  rcases hm with ⟨b0, hmb⟩ | hnov | hnull
  · exact Msg.noConfusion (heq.trans hmb)
  · exact Msg.noConfusion (heq.trans hnov)
  · exact hne (by injection (heq.trans hnull))

private lemma msg_unchanged {s : St} {m m' : Msg} {t : Nat} (hne : m' ≠ m) :
    (addMsg s m t).sent m' = s.sent m' := by
  simp [addMsg, hne]

private lemma vote_ne_of_block {p : Proc} {v : View} {b b' : Block} (hne : b' ≠ b) :
    Msg.vote p v b' ≠ Msg.vote p v b := by
  intro heq
  exact hne (by injection heq)

private lemma vote_ne_of_view {p : Proc} {v v' : View} {b b' : Block} (hne : v' ≠ v) :
    Msg.vote p v' b' ≠ Msg.vote p v b := by
  intro heq
  exact hne (by injection heq)

private lemma novote_ne_of_view {p : Proc} {v v' : View} (hne : v' ≠ v) :
    Msg.novote p v' ≠ Msg.novote p v := by
  intro heq
  exact hne (by injection heq)

private lemma nullify_ne_of_view {p : Proc} {v v' : View} (hne : v' ≠ v) :
    Msg.nullify p v' ≠ Msg.nullify p v := by
  intro heq
  exact hne (by injection heq)

private lemma vote_ne_any_novote {p q : Proc} {v v' : View} {b : Block} :
    Msg.vote q v' b ≠ Msg.novote p v := by
  intro heq
  exact Msg.noConfusion heq

private lemma vote_ne_any_nullify {p q : Proc} {v v' : View} {b : Block} :
    Msg.vote q v' b ≠ Msg.nullify p v := by
  intro heq
  exact Msg.noConfusion heq

/-- The evidence kinds for the nullify-evidence rule (paper's lines 16-19):
a nullify share sent strictly before `t`, a novote, or a vote for a block
other than `b`. -/
private def EvidenceKinds (s : St) (t : Nat) (q : Proc) (v : View) (b : Block) : Prop :=
  (∃ tq : Nat, s.sent (Msg.nullify q v) = some tq ∧ tq < t) ∨
  Sent s (Msg.novote q v) ∨
    ∃ b0 : Block, b0 ≠ b ∧ Sent s (Msg.vote q v b0)

/-- Adding a fresh message (`hUnsent`) preserves an evidence witness whose
evidence did not include the new message. -/
private lemma evidence_preserved {s : St} {m : Msg} {t : Nat}
    {t' : Nat} {v' : View} {b' : Block} {E : Finset Proc}
    (hEv : ∀ q : Proc, q ∈ E → EvidenceKinds s t' q v' b')
    (hUnsent : s.sent m = none) :
    ∀ q : Proc, q ∈ E → EvidenceKinds (addMsg s m t) t' q v' b' := by
  intro q hq
  rcases hEv q hq with hqnull | hqnov | ⟨b0, hb0ne, hqvote⟩
  · left
    rcases hqnull with ⟨tq, htq, hlt⟩
    by_cases hmn : Msg.nullify q v' = m
    · exfalso
      have hbad : s.sent m = some tq := by simpa [hmn] using htq
      have hbad' : none = some tq := hUnsent.symm.trans hbad
      cases hbad'
    · refine ⟨tq, ?_, hlt⟩
      have hunch : (addMsg s m t).sent (Msg.nullify q v') = s.sent (Msg.nullify q v') :=
        msg_unchanged hmn
      simpa [hunch] using htq
  · right; left
    rcases hqnov with ⟨tn, htn⟩
    by_cases hmn : Msg.novote q v' = m
    · exfalso
      have hbad : s.sent m = some tn := by simpa [hmn] using htn
      have hbad' : none = some tn := hUnsent.symm.trans hbad
      cases hbad'
    · refine ⟨tn, ?_⟩
      have hunch : (addMsg s m t).sent (Msg.novote q v') = s.sent (Msg.novote q v') :=
        msg_unchanged hmn
      simpa [hunch] using htn
  · right; right
    refine ⟨b0, hb0ne, ?_⟩
    rcases hqvote with ⟨tv, htv⟩
    by_cases hmn : Msg.vote q v' b0 = m
    · exfalso
      have hbad : s.sent m = some tv := by simpa [hmn] using htv
      have hbad' : none = some tv := hUnsent.symm.trans hbad
      cases hbad'
    · refine ⟨tv, ?_⟩
      have hunch : (addMsg s m t).sent (Msg.vote q v' b0) = s.sent (Msg.vote q v' b0) :=
        msg_unchanged hmn
      simpa [hunch] using htv

theorem addMsg_oneVote {s : St} {m : Msg} {t : Nat} {p : Proc} {v : View} {Byz : Finset Proc}
    (hByz : p ∈ Byz) (hm : IsMsgOf p v m) (hInv : OneVote s Byz) :
    OneVote (addMsg s m t) Byz := by
  intro p' hp' v' b1 b2 hb1 hb2
  by_cases hne : p' = p
  · subst p'
    exfalso
    exact hp' hByz
  · have hb1' : Sent s (Msg.vote p' v' b1) := by
      rcases hb1 with ⟨t1, ht1⟩
      have hunch : (addMsg s m t).sent (Msg.vote p' v' b1) = s.sent (Msg.vote p' v' b1) :=
        msg_unchanged (vote_ne_of_msg hne hm)
      refine ⟨t1, ?_⟩
      simpa [hunch] using ht1
    have hb2' : Sent s (Msg.vote p' v' b2) := by
      rcases hb2 with ⟨t2, ht2⟩
      have hunch : (addMsg s m t).sent (Msg.vote p' v' b2) = s.sent (Msg.vote p' v' b2) :=
        msg_unchanged (vote_ne_of_msg hne hm)
      refine ⟨t2, ?_⟩
      simpa [hunch] using ht2
    exact hInv p' hp' v' b1 b2 hb1' hb2'

theorem addMsg_excl {s : St} {m : Msg} {t : Nat} {p : Proc} {v : View} {Byz : Finset Proc}
    (hByz : p ∈ Byz) (hm : IsMsgOf p v m) (hInv : Excl s Byz) :
    Excl (addMsg s m t) Byz := by
  intro p' hp' v' hnov b hvot
  by_cases hne : p' = p
  · subst p'
    exfalso
    exact hp' hByz
  · have hnov' : Sent s (Msg.novote p' v') := by
      rcases hnov with ⟨tn, htn⟩
      have hunch : (addMsg s m t).sent (Msg.novote p' v') = s.sent (Msg.novote p' v') :=
        msg_unchanged (novote_ne_of_msg hne hm)
      refine ⟨tn, ?_⟩
      simpa [hunch] using htn
    exact hInv p' hp' v' hnov' b (by
      rcases hvot with ⟨tv, htv⟩
      have hunch : (addMsg s m t).sent (Msg.vote p' v' b) = s.sent (Msg.vote p' v' b) :=
        msg_unchanged (vote_ne_of_msg hne hm)
      refine ⟨tv, ?_⟩
      simpa [hunch] using htv)

theorem addMsg_evidenceBefore {s : St} {m : Msg} {t : Nat} {p : Proc} {v : View}
    {Byz : Finset Proc} {n f : Nat} (hByz : p ∈ Byz) (hm : IsMsgOf p v m)
    (hUnsent : s.sent m = none) (hInv : EvidenceBefore s n f Byz) :
    EvidenceBefore (addMsg s m t) n f Byz := by
  intro p' hp' v' b' t' hv' hnull'
  by_cases hne : p' = p
  · subst p'
    exfalso
    exact hp' hByz
  · have hv'0 : Sent s (Msg.vote p' v' b') := by
      rcases hv' with ⟨tv, htv⟩
      have hunch : (addMsg s m t).sent (Msg.vote p' v' b') = s.sent (Msg.vote p' v' b') :=
        msg_unchanged (vote_ne_of_msg hne hm)
      refine ⟨tv, ?_⟩
      simpa [hunch] using htv
    have hnull'0 : s.sent (Msg.nullify p' v') = some t' := by
      have hunch : (addMsg s m t).sent (Msg.nullify p' v') = s.sent (Msg.nullify p' v') :=
        msg_unchanged (nullify_ne_of_msg hne hm)
      simpa [hunch] using hnull'
    rcases hInv p' hp' v' b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
    have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addMsg s m t) t' q v' b' :=
      evidence_preserved hEv hUnsent
    exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩

/-! ## The invariant is inductive -/

theorem vote_inv {n f : Nat} {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View} {b : Block}
    (hstep : Vote Byz p v b s s') (hInv : Inv n f Byz s) : Inv n f Byz s' := by
  tla_unfold
  rcases hstep with ⟨hNotByz, hNoVote, hNoPrior, hNoNovote, hNoNullify, hTime', hSent'⟩
  have hs' : s' = addVote s p v b (s.time + 1) := by
    ext <;> simp [addVote, addMsg, hTime', hSent']
  subst s'
  constructor
  · simpa [addVote] using addMsg_sentLeTime hInv.1 (by omega)
  · constructor
    · intro p' hp' v' b1 b2 hb1 hb2
      by_cases hpp : p' = p
      · subst p'
        by_cases hvv : v' = v
        · subst v'
          have hb1' : b1 = b := by
            by_cases h1 : Msg.vote p v b1 = Msg.vote p v b
            · exact (by injection h1)
            · exfalso
              rcases hb1 with ⟨t1, ht1⟩
              have hb1ne : b1 ≠ b := by
                intro hbb
                exact h1 (by simp [hbb])
              have ht1' : s.sent (Msg.vote p v b1) = some t1 := by simpa [addVote, addMsg, h1] using ht1
              have hnone : s.sent (Msg.vote p v b1) = none := hNoPrior b1 hb1ne
              cases hnone.symm.trans ht1'
          have hb2' : b2 = b := by
            by_cases h2 : Msg.vote p v b2 = Msg.vote p v b
            · exact (by injection h2)
            · exfalso
              rcases hb2 with ⟨t2, ht2⟩
              have hb2ne : b2 ≠ b := by
                intro hbb
                exact h2 (by simp [hbb])
              have ht2' : s.sent (Msg.vote p v b2) = some t2 := by simpa [addVote, addMsg, h2] using ht2
              have hnone : s.sent (Msg.vote p v b2) = none := hNoPrior b2 hb2ne
              cases hnone.symm.trans ht2'
          simp [hb1', hb2']
        · have hb1' : Sent s (Msg.vote p v' b1) := by
            rcases hb1 with ⟨t1, ht1⟩
            have hne : Msg.vote p v' b1 ≠ Msg.vote p v b := vote_ne_of_view hvv
            refine ⟨t1, ?_⟩
            simpa [addVote, addMsg, hne] using ht1
          have hb2' : Sent s (Msg.vote p v' b2) := by
            rcases hb2 with ⟨t2, ht2⟩
            have hne : Msg.vote p v' b2 ≠ Msg.vote p v b := vote_ne_of_view hvv
            refine ⟨t2, ?_⟩
            simpa [addVote, addMsg, hne] using ht2
          exact hInv.2.1 p hp' v' b1 b2 hb1' hb2'
      · have hb1' : Sent s (Msg.vote p' v' b1) := by
          rcases hb1 with ⟨t1, ht1⟩
          have hne : Msg.vote p' v' b1 ≠ Msg.vote p v b :=
            vote_ne_of_msg hpp (Or.inl ⟨b, rfl⟩)
          refine ⟨t1, ?_⟩
          simpa [addVote, addMsg, hne] using ht1
        have hb2' : Sent s (Msg.vote p' v' b2) := by
          rcases hb2 with ⟨t2, ht2⟩
          have hne : Msg.vote p' v' b2 ≠ Msg.vote p v b :=
            vote_ne_of_msg hpp (Or.inl ⟨b, rfl⟩)
          refine ⟨t2, ?_⟩
          simpa [addVote, addMsg, hne] using ht2
        exact hInv.2.1 p' hp' v' b1 b2 hb1' hb2'
    · constructor
      · intro p' hp' v' hnov b0 hvot
        by_cases hpp : p' = p
        · subst p'
          by_cases hvv : v' = v
          · subst v'
            exfalso
            rcases hnov with ⟨tn, htn⟩
            have htn' : s.sent (Msg.novote p v) = some tn := by simpa [addVote, addMsg] using htn
            exact hNoNovote ⟨tn, htn'⟩
          · have hnov' : Sent s (Msg.novote p v') := by
              rcases hnov with ⟨tn, htn⟩
              have hne : Msg.novote p v' ≠ Msg.vote p v b := by
                intro heq
                exact Msg.noConfusion heq
              refine ⟨tn, ?_⟩
              simpa [addVote, addMsg, hne] using htn
            exact hInv.2.2.1 p hp' v' hnov' b0 (by
              rcases hvot with ⟨tv, htv⟩
              have hne : Msg.vote p v' b0 ≠ Msg.vote p v b := vote_ne_of_view hvv
              refine ⟨tv, ?_⟩
              simpa [addVote, addMsg, hne] using htv)
        · have hnov' : Sent s (Msg.novote p' v') := by
            rcases hnov with ⟨tn, htn⟩
            have hne : Msg.novote p' v' ≠ Msg.vote p v b := by
              intro heq
              exact Msg.noConfusion heq
            refine ⟨tn, ?_⟩
            simpa [addVote, addMsg, hne] using htn
          exact hInv.2.2.1 p' hp' v' hnov' b0 (by
            rcases hvot with ⟨tv, htv⟩
            have hne : Msg.vote p' v' b0 ≠ Msg.vote p v b :=
              vote_ne_of_msg hpp (Or.inl ⟨b, rfl⟩)
            refine ⟨tv, ?_⟩
            simpa [addVote, addMsg, hne] using htv)
      · intro p' hp' v' b' t' hv' hnull'
        by_cases hpp : p' = p
        · subst p'
          by_cases hvv : v' = v
          · subst v'
            by_cases hbb : b' = b
            · subst b'
              exfalso
              have htn : s.sent (Msg.nullify p v) = some t' := by simpa [addVote, addMsg] using hnull'
              exact hNoNullify ⟨t', htn⟩
            · have hv'0 : Sent s (Msg.vote p v b') := by
                rcases hv' with ⟨tv, htv⟩
                have hne : Msg.vote p v b' ≠ Msg.vote p v b := vote_ne_of_block hbb
                refine ⟨tv, ?_⟩
                simpa [addVote, addMsg, hne] using htv
              have hnull'0 : s.sent (Msg.nullify p v) = some t' := by
                have hne : Msg.nullify p v ≠ Msg.vote p v b := by
                  intro heq
                  exact Msg.noConfusion heq
                simpa [addVote, addMsg, hne] using hnull'
              rcases hInv.2.2.2 p hp' v b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
              have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addVote s p v b (s.time + 1)) t' q v b' :=
                evidence_preserved hEv hNoVote
              exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩
          · have hv'0 : Sent s (Msg.vote p v' b') := by
              rcases hv' with ⟨tv, htv⟩
              have hne : Msg.vote p v' b' ≠ Msg.vote p v b := vote_ne_of_view hvv
              refine ⟨tv, ?_⟩
              simpa [addVote, addMsg, hne] using htv
            have hnull'0 : s.sent (Msg.nullify p v') = some t' := by
              have hne : Msg.nullify p v' ≠ Msg.vote p v b := by
                intro heq
                exact Msg.noConfusion heq
              simpa [addVote, addMsg, hne] using hnull'
            rcases hInv.2.2.2 p hp' v' b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
            have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addVote s p v b (s.time + 1)) t' q v' b' :=
              evidence_preserved hEv hNoVote
            exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩
        · have hv'0 : Sent s (Msg.vote p' v' b') := by
            rcases hv' with ⟨tv, htv⟩
            have hne : Msg.vote p' v' b' ≠ Msg.vote p v b :=
              vote_ne_of_msg hpp (Or.inl ⟨b, rfl⟩)
            refine ⟨tv, ?_⟩
            simpa [addVote, addMsg, hne] using htv
          have hnull'0 : s.sent (Msg.nullify p' v') = some t' := by
            have hne : Msg.nullify p' v' ≠ Msg.vote p v b := by
              intro heq
              exact Msg.noConfusion heq
            simpa [addVote, addMsg, hne] using hnull'
          rcases hInv.2.2.2 p' hp' v' b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
          have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addVote s p v b (s.time + 1)) t' q v' b' :=
            evidence_preserved hEv hNoVote
          exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩

theorem timeout_inv {n f : Nat} {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View}
    (hstep : NullifyTimeout Byz p v s s') (hInv : Inv n f Byz s) : Inv n f Byz s' := by
  tla_unfold
  rcases hstep with ⟨hNotByz, hNoVote, hNoNovote, hNoNullify, hTime', hSent'⟩
  have hs' : s' = addNullify (addNovote s p v (s.time + 1)) p v (s.time + 1) := by
    ext <;> simp [addNullify, addNovote, addMsg, hTime', hSent']
  subst s'
  constructor
  · have h1 : SentLeTime (addNovote s p v (s.time + 1)) := by
      simpa [addNovote] using addMsg_sentLeTime hInv.1 (by simp [addMsg])
    simpa [addNullify] using addMsg_sentLeTime h1 (by simp [addNovote, addMsg])
  · constructor
    · intro p' hp' v' b1 b2 hb1 hb2
      have hb1' : Sent s (Msg.vote p' v' b1) := by
        rcases hb1 with ⟨t1, ht1⟩
        have hne1 : Msg.vote p' v' b1 ≠ Msg.nullify p v := vote_ne_any_nullify
        have hne2 : Msg.vote p' v' b1 ≠ Msg.novote p v := vote_ne_any_novote
        refine ⟨t1, ?_⟩
        simpa [addNullify, addNovote, addMsg, hne1, hne2] using ht1
      have hb2' : Sent s (Msg.vote p' v' b2) := by
        rcases hb2 with ⟨t2, ht2⟩
        have hne1 : Msg.vote p' v' b2 ≠ Msg.nullify p v := vote_ne_any_nullify
        have hne2 : Msg.vote p' v' b2 ≠ Msg.novote p v := vote_ne_any_novote
        refine ⟨t2, ?_⟩
        simpa [addNullify, addNovote, addMsg, hne1, hne2] using ht2
      exact hInv.2.1 p' hp' v' b1 b2 hb1' hb2'
    · constructor
      · intro p' hp' v' hnov b0 hvot
        by_cases hpp : p' = p
        · subst p'
          by_cases hvv : v' = v
          · subst v'
            exfalso
            rcases hvot with ⟨tb, htb⟩
            have htb' : s.sent (Msg.vote p v b0) = some tb := by simpa [addNullify, addNovote, addMsg] using htb
            have hnone : s.sent (Msg.vote p v b0) = none := hNoVote b0
            cases hnone.symm.trans htb'
          · have hnov' : Sent s (Msg.novote p v') := by
              rcases hnov with ⟨tn, htn⟩
              have hne : Msg.novote p v' ≠ Msg.nullify p v := by
                intro heq
                exact Msg.noConfusion heq
              have hne' : Msg.novote p v' ≠ Msg.novote p v := novote_ne_of_view hvv
              refine ⟨tn, ?_⟩
              simpa [addNullify, addNovote, addMsg, hne, hne'] using htn
            exact hInv.2.2.1 p hp' v' hnov' b0 (by
              rcases hvot with ⟨tv, htv⟩
              have hne : Msg.vote p v' b0 ≠ Msg.nullify p v := by
                intro heq
                exact Msg.noConfusion heq
              have hne' : Msg.vote p v' b0 ≠ Msg.novote p v := by
                intro heq
                exact Msg.noConfusion heq
              refine ⟨tv, ?_⟩
              simpa [addNullify, addNovote, addMsg, hne, hne'] using htv)
        · have hnov' : Sent s (Msg.novote p' v') := by
            rcases hnov with ⟨tn, htn⟩
            have hne : Msg.novote p' v' ≠ Msg.nullify p v := by
              intro heq
              exact Msg.noConfusion heq
            have hne' : Msg.novote p' v' ≠ Msg.novote p v := by
              intro heq
              exact hpp (by injection heq)
            refine ⟨tn, ?_⟩
            simpa [addNullify, addNovote, addMsg, hne, hne'] using htn
          exact hInv.2.2.1 p' hp' v' hnov' b0 (by
            rcases hvot with ⟨tv, htv⟩
            have hne : Msg.vote p' v' b0 ≠ Msg.nullify p v := by
              intro heq
              exact Msg.noConfusion heq
            have hne' : Msg.vote p' v' b0 ≠ Msg.novote p v := by
              intro heq
              exact Msg.noConfusion heq
            refine ⟨tv, ?_⟩
            simpa [addNullify, addNovote, addMsg, hne, hne'] using htv)
      · intro p' hp' v' b' t' hv' hnull'
        by_cases hpp : p' = p
        · subst p'
          by_cases hvv : v' = v
          · subst v'
            exfalso
            rcases hv' with ⟨tv, htv⟩
            have htv' : s.sent (Msg.vote p v b') = some tv := by
              simpa [addNullify, addNovote, addMsg] using htv
            have hnone : s.sent (Msg.vote p v b') = none := hNoVote b'
            cases hnone.symm.trans htv'
          · have hv'0 : Sent s (Msg.vote p v' b') := by
              rcases hv' with ⟨tv, htv⟩
              have hne : Msg.vote p v' b' ≠ Msg.nullify p v := by
                intro heq
                exact Msg.noConfusion heq
              have hne' : Msg.vote p v' b' ≠ Msg.novote p v := by
                intro heq
                exact Msg.noConfusion heq
              refine ⟨tv, ?_⟩
              simpa [addNullify, addNovote, addMsg, hne, hne'] using htv
            have hnull'0 : s.sent (Msg.nullify p v') = some t' := by
              have hne : Msg.nullify p v' ≠ Msg.nullify p v := nullify_ne_of_view hvv
              have hne' : Msg.nullify p v' ≠ Msg.novote p v := by
                intro heq
                exact Msg.noConfusion heq
              simpa [addNullify, addNovote, addMsg, hne, hne'] using hnull'
            rcases hInv.2.2.2 p hp' v' b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
            have hUnsent2 : (addNovote s p v (s.time + 1)).sent (Msg.nullify p v) = none := by
              have hne : Msg.nullify p v ≠ Msg.novote p v := by
                intro heq
                exact Msg.noConfusion heq
              simpa [addNovote, addMsg, hne] using hNoNullify
            have hEv1 : ∀ q : Proc, q ∈ E → EvidenceKinds (addNovote s p v (s.time + 1)) t' q v' b' :=
              evidence_preserved hEv hNoNovote
            have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addNullify (addNovote s p v (s.time + 1)) p v (s.time + 1)) t' q v' b' :=
              evidence_preserved hEv1 hUnsent2
            exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩
        · have hv'0 : Sent s (Msg.vote p' v' b') := by
            rcases hv' with ⟨tv, htv⟩
            have hne : Msg.vote p' v' b' ≠ Msg.nullify p v := by
              intro heq
              exact Msg.noConfusion heq
            have hne' : Msg.vote p' v' b' ≠ Msg.novote p v := by
              intro heq
              exact hpp (by injection heq)
            refine ⟨tv, ?_⟩
            simpa [addNullify, addNovote, addMsg, hne, hne'] using htv
          have hnull'0 : s.sent (Msg.nullify p' v') = some t' := by
            have hne : Msg.nullify p' v' ≠ Msg.nullify p v := by
              intro heq
              exact hpp (by injection heq)
            have hne' : Msg.nullify p' v' ≠ Msg.novote p v := by
              intro heq
              exact Msg.noConfusion heq
            simpa [addNullify, addNovote, addMsg, hne, hne'] using hnull'
          rcases hInv.2.2.2 p' hp' v' b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
          have hUnsent2 : (addNovote s p v (s.time + 1)).sent (Msg.nullify p v) = none := by
            have hne : Msg.nullify p v ≠ Msg.novote p v := by
              intro heq
              exact Msg.noConfusion heq
            simpa [addNovote, addMsg, hne] using hNoNullify
          have hEv1 : ∀ q : Proc, q ∈ E → EvidenceKinds (addNovote s p v (s.time + 1)) t' q v' b' :=
            evidence_preserved hEv hNoNovote
          have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addNullify (addNovote s p v (s.time + 1)) p v (s.time + 1)) t' q v' b' :=
            evidence_preserved hEv1 hUnsent2
          exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩

theorem evidence_inv {n f : Nat} {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View} {b : Block}
    (hstep : NullifyEvidence n f Byz p v b s s') (hInv : Inv n f Byz s) : Inv n f Byz s' := by
  tla_unfold
  rcases hstep with ⟨hNotByz, hVote, hNoNullify, hE, hTime', hSent'⟩
  have hs' : s' = addNullify s p v (s.time + 1) := by
    ext <;> simp [addNullify, addMsg, hTime', hSent']
  subst s'
  constructor
  · simpa [addNullify] using addMsg_sentLeTime hInv.1 (by omega)
  · constructor
    · intro p' hp' v' b1 b2 hb1 hb2
      have hb1' : Sent s (Msg.vote p' v' b1) := by
        rcases hb1 with ⟨t1, ht1⟩
        have hne : Msg.vote p' v' b1 ≠ Msg.nullify p v := vote_ne_any_nullify
        refine ⟨t1, ?_⟩
        simpa [addNullify, addMsg, hne] using ht1
      have hb2' : Sent s (Msg.vote p' v' b2) := by
        rcases hb2 with ⟨t2, ht2⟩
        have hne : Msg.vote p' v' b2 ≠ Msg.nullify p v := vote_ne_any_nullify
        refine ⟨t2, ?_⟩
        simpa [addNullify, addMsg, hne] using ht2
      exact hInv.2.1 p' hp' v' b1 b2 hb1' hb2'
    · constructor
      · intro p' hp' v' hnov b0 hvot
        have hnov' : Sent s (Msg.novote p' v') := by
          rcases hnov with ⟨tn, htn⟩
          have hne : Msg.novote p' v' ≠ Msg.nullify p v := by
            intro heq
            exact Msg.noConfusion heq
          refine ⟨tn, ?_⟩
          simpa [addNullify, addMsg, hne] using htn
        exact hInv.2.2.1 p' hp' v' hnov' b0 (by
          rcases hvot with ⟨tv, htv⟩
          have hne' : Msg.vote p' v' b0 ≠ Msg.nullify p v := by
            intro heq
            exact Msg.noConfusion heq
          refine ⟨tv, ?_⟩
          simpa [addNullify, addMsg, hne'] using htv)
      · intro p' hp' v' b' t' hv' hnull'
        by_cases hpp : p' = p
        · subst p'
          by_cases hvv : v' = v
          · subst v'
            by_cases hbb : b' = b
            · subst b'
              -- the new pair (p, v, b): the guard's evidence set works
              rcases hE with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
              have ht' : t' = s.time + 1 := (Option.some.inj (by simpa [addNullify, addMsg] using hnull')).symm
              have hEv0 : ∀ q : Proc, q ∈ E → EvidenceKinds s t' q v b := by
                intro q hq
                rcases hEv q hq with hqnull | hqnov | ⟨b0, hb0ne, hqvote⟩
                · left
                  rcases hqnull with ⟨tq, htq⟩
                  have hle : tq ≤ s.time := hInv.1 (Msg.nullify q v) tq htq
                  exact ⟨tq, htq, by omega⟩
                · right; left
                  exact hqnov
                · right; right
                  exact ⟨b0, hb0ne, hqvote⟩
              have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addNullify s p v (s.time + 1)) t' q v b :=
                evidence_preserved hEv0 hNoNullify
              exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩
            · -- same p,v but a different block: impossible, one vote per view
              exfalso
              have hv'0 : Sent s (Msg.vote p v b') := by
                rcases hv' with ⟨tv, htv⟩
                have hne : Msg.vote p v b' ≠ Msg.nullify p v := by
                  intro heq
                  exact Msg.noConfusion heq
                refine ⟨tv, ?_⟩
                simpa [addNullify, addMsg, hne] using htv
              have hbb' : b' = b := hInv.2.1 p hp' v b' b hv'0 hVote
              exact hbb hbb'
          · -- v' ≠ v: both messages unchanged
            have hv'0 : Sent s (Msg.vote p v' b') := by
              rcases hv' with ⟨tv, htv⟩
              have hne : Msg.vote p v' b' ≠ Msg.nullify p v := by
                intro heq
                exact Msg.noConfusion heq
              refine ⟨tv, ?_⟩
              simpa [addNullify, addMsg, hne] using htv
            have hnull'0 : s.sent (Msg.nullify p v') = some t' := by
              have hne : Msg.nullify p v' ≠ Msg.nullify p v := nullify_ne_of_view hvv
              simpa [addNullify, addMsg, hne] using hnull'
            rcases hInv.2.2.2 p hp' v' b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
            have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addNullify s p v (s.time + 1)) t' q v' b' :=
              evidence_preserved hEv hNoNullify
            exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩
        · have hv'0 : Sent s (Msg.vote p' v' b') := by
            rcases hv' with ⟨tv, htv⟩
            have hne : Msg.vote p' v' b' ≠ Msg.nullify p v := by
              intro heq
              exact Msg.noConfusion heq
            refine ⟨tv, ?_⟩
            simpa [addNullify, addMsg, hne] using htv
          have hnull'0 : s.sent (Msg.nullify p' v') = some t' := by
            have hne : Msg.nullify p' v' ≠ Msg.nullify p v :=
              nullify_ne_of_msg hpp (Or.inr (Or.inr rfl))
            simpa [addNullify, addMsg, hne] using hnull'
          rcases hInv.2.2.2 p' hp' v' b' t' hv'0 hnull'0 with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
          have hEv' : ∀ q : Proc, q ∈ E → EvidenceKinds (addNullify s p v (s.time + 1)) t' q v' b' :=
            evidence_preserved hEv hNoNullify
          exact ⟨E, hEsub, hEcard, hpNotE, hEv'⟩

theorem byz_inv {n f : Nat} {Byz : Finset Proc} {s s' : St} {p : Proc} {v : View}
    (hstep : Byzantine Byz p v s s') (hInv : Inv n f Byz s) : Inv n f Byz s' := by
  tla_unfold
  rcases hstep with ⟨hByz, hTime', hm⟩
  rcases hm with ⟨m, hUnsent, hKind, hSent'⟩
  have hs' : s' = addMsg s m (s.time + 1) := by
    ext <;> simp [addMsg, hTime', hSent']
  subst s'
  constructor
  · exact addMsg_sentLeTime hInv.1 (by omega)
  · constructor
    · exact addMsg_oneVote hByz hKind hInv.2.1
    · constructor
      · exact addMsg_excl hByz hKind hInv.2.2.1
      · exact addMsg_evidenceBefore hByz hKind hUnsent hInv.2.2.2

theorem init_inv {n f : Nat} {Byz : Finset Proc} {s : St} (h : Init s) : Inv n f Byz s := by
  tla_unfold
  rcases h with ⟨hSent, hTime⟩
  constructor
  · intro m t hmt
    simp [hSent m] at hmt
  · constructor
    · intro p hp v b b' hb hb'
      rcases hb with ⟨t, ht⟩
      simp [hSent (Msg.vote p v b)] at ht
    · constructor
      · intro p hp v hnov hvot
        rcases hnov with ⟨t, ht⟩
        simp [hSent (Msg.novote p v)] at ht
      · intro p hp v b t hv hnull
        rcases hv with ⟨tv, htv⟩
        simp [hSent (Msg.vote p v b)] at htv

theorem next_inv (n f : Nat) (Byz : Finset Proc) :
    ∀ s s' : St, Next n f Byz s s' → Inv n f Byz s → Inv n f Byz s' := by
  intro s s' hstep hInv
  unfold Next at hstep
  rcases hstep with ⟨p, v, hstep⟩
  rcases hstep with hvote | htimeout | hevidence | hbyz
  · rcases hvote with ⟨b, hvote⟩
    exact vote_inv hvote hInv
  · exact timeout_inv htimeout hInv
  · rcases hevidence with ⟨b, hevidence⟩
    exact evidence_inv hevidence hInv
  · exact byz_inv hbyz hInv

theorem stutter_inv {n f : Nat} {Byz : Finset Proc} :
    ∀ s s' : St, vars s' = vars s → Inv n f Byz s → Inv n f Byz s' := by
  intro s s' hstut hInv
  tla_unfold
  cases hstut
  exact hInv

theorem spec_entails_inv (n f : Nat) (Byz : Finset Proc) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n f Byz) vars)) ⊢ □ ⌜ Inv n f Byz ⌝ := by
  apply Tla.init_invariant_stut
  · intro s hs
    exact init_inv hs
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact next_inv n f Byz s s' hnext hInv
    · exact stutter_inv s s' hstut hInv

/-! ## Lemma 5: no nullification for a notarised view -/

theorem no_nullification {n f : Nat} {Byz : Finset Proc} {s : St} {v : View} {b : Block}
    (hInv : Inv n f Byz s) (hByzSub : Byz ⊆ Finset.range n) (hByzCard : Byz.card ≤ f)
    (hN5 : 5 * f + 1 ≤ n) (hN : Notarised s n f v b) :
    ¬ Nullified s n f v := by
  classical
  by_contra hnull
  rcases hnull with ⟨Q, hQsub, hQcard, hQnull⟩
  rcases hN with ⟨Q0, hQ0sub, hQ0card, hQ0vote⟩
  let A := (Finset.range n \ Byz).filter (fun p => Sent s (Msg.vote p v b))
  let B := (Finset.range n \ Byz).filter (fun p => ¬ Sent s (Msg.vote p v b))
  have hA_ge : n - f - Byz.card ≤ A.card := by
    have hsub : Q0.filter (fun p => p ∉ Byz) ⊆ A := by
      intro p hp
      have hp0 : p ∈ Q0 := (Finset.mem_filter.mp hp).1
      have hpNot : p ∉ Byz := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hQ0sub hp0, hpNot⟩, hQ0vote p hp0⟩
    have hcard_sub : (Q0.filter (fun p => p ∉ Byz)).card ≤ A.card := Finset.card_le_card hsub
    have hcard_minus : Q0.card - Byz.card ≤ (Q0.filter (fun p => p ∉ Byz)).card := by
      have hsum : (Q0.filter (fun p => p ∈ Byz)).card + (Q0.filter (fun p => p ∉ Byz)).card = Q0.card := by
        simpa using (Finset.card_filter_add_card_filter_not (s := Q0) (p := fun p => p ∈ Byz))
      have hle : (Q0.filter (fun p => p ∈ Byz)).card ≤ Byz.card := by
        exact Finset.card_le_card (by intro p hp; exact (Finset.mem_filter.mp hp).2)
      omega
    omega
  have hB_le : B.card ≤ f := by
    have hsum : A.card + B.card = (Finset.range n \ Byz).card := by
      simpa [A, B] using (Finset.card_filter_add_card_filter_not (s := Finset.range n \ Byz) (p := fun p => Sent s (Msg.vote p v b)))
    have huniv : (Finset.range n \ Byz).card = n - Byz.card := by
      simpa [Finset.card_range] using Finset.card_sdiff_of_subset hByzSub
    omega
  have hmain : ∀ t : Nat, ¬ (∃ p : Proc, p ∈ A ∧ s.sent (Msg.nullify p v) = some t) := by
    intro t
    refine Nat.strong_induction_on t ?_
    intro t' ih hp
    rcases hp with ⟨p, hpA, hpnull⟩
    have hpUniv : p ∈ Finset.range n := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpA).1).1
    have hpNotByz : p ∉ Byz := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpA).1).2
    have hpVote : Sent s (Msg.vote p v b) := (Finset.mem_filter.mp hpA).2
    rcases hInv.2.2.2 p hpNotByz v b t' hpVote hpnull with ⟨E, hEsub, hEcard, hpNotE, hEv⟩
    let C := E.filter (fun q => q ∉ Byz)
    have hC_sub_B : C ⊆ B := by
      intro q hq
      have hqE : q ∈ E := (Finset.mem_filter.mp hq).1
      have hqNot : q ∉ Byz := (Finset.mem_filter.mp hq).2
      have hqUniv : q ∈ Finset.range n := hEsub hqE
      have hqNotA : q ∉ A := by
        intro hqA
        have hqVote : Sent s (Msg.vote q v b) := (Finset.mem_filter.mp hqA).2
        rcases hEv q hqE with hnullq | hnovq | ⟨b', hb'ne, hvoteq⟩
        · rcases hnullq with ⟨tq, htq⟩
          have hlt : tq < t' := htq.2
          exact ih tq hlt ⟨q, hqA, htq.1⟩
        · rcases hnovq with ⟨tn, htn⟩
          exact hInv.2.2.1 q hqNot v (Exists.intro tn htn) b hqVote
        · rcases hvoteq with ⟨tv, htv⟩
          have hbb : b' = b := hInv.2.1 q hqNot v b' b (Exists.intro tv htv) hqVote
          exact hb'ne hbb
      have hqNotVote : ¬ Sent s (Msg.vote q v b) := by
        intro hqv
        exact hqNotA (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hqUniv, hqNot⟩, hqv⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hqUniv, hqNot⟩, hqNotVote⟩
    have hC_ge : f + 1 ≤ C.card := by
      have hsum : C.card + (E.filter (fun q => q ∈ Byz)).card = E.card := by
        simpa [C] using (Finset.card_filter_add_card_filter_not (s := E) (p := fun q => q ∉ Byz))
      have hbyz : (E.filter (fun q => q ∈ Byz)).card ≤ Byz.card := by
        exact Finset.card_le_card (by intro q hq; exact (Finset.mem_filter.mp hq).2)
      omega
    have hC_le : C.card ≤ B.card := Finset.card_le_card hC_sub_B
    omega
  have hQc : f + 1 ≤ (Q.filter (fun p => p ∉ Byz)).card := by
    have hsum : (Q.filter (fun p => p ∉ Byz)).card + (Q.filter (fun p => p ∈ Byz)).card = Q.card := by
      simpa using (Finset.card_filter_add_card_filter_not (s := Q) (p := fun p => p ∉ Byz))
    have hbyz : (Q.filter (fun p => p ∈ Byz)).card ≤ Byz.card := by
      exact Finset.card_le_card (by intro p hp; exact (Finset.mem_filter.mp hp).2)
    omega
  have hQc_sub_B : Q.filter (fun p => p ∉ Byz) ⊆ B := by
    intro p hp
    have hpNot : p ∉ Byz := (Finset.mem_filter.mp hp).2
    have hpNull : Sent s (Msg.nullify p v) := hQnull p (Finset.mem_filter.mp hp).1
    rcases hpNull with ⟨t, ht⟩
    have hpNotA : p ∉ A := by
      intro hpA
      exact hmain t ⟨p, hpA, ht⟩
    have hpUniv : p ∈ Finset.range n := hQsub (Finset.mem_filter.mp hp).1
    have hpNotVote : ¬ Sent s (Msg.vote p v b) := by
      intro hpv
      exact hpNotA (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hpUniv, hpNot⟩, hpv⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hpUniv, hpNot⟩, hpNotVote⟩
  have hQc_le : (Q.filter (fun p => p ∉ Byz)).card ≤ B.card := Finset.card_le_card hQc_sub_B
  omega

/-- The canonical statement of Lemma 5: if a block is L-notarised in a view,
the view receives no nullification. -/
@[simp] def NoNullification (n f : Nat) (v : View) (b : Block) : Tla.StatePred St :=
  [p| Notarised n f v b → ¬ Nullified n f v]

theorem spec_entails_no_nullification (n f : Nat) (Byz : Finset Proc) (v : View) (b : Block)
    (hP : ValidParams n f Byz) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n f Byz) vars)) ⊢ □ ⌜ NoNullification n f v b ⌝ := by
  rcases hP with ⟨hByzSub, hByzCard, hn⟩
  intro e he
  have hInv : Tla.always (Tla.statePred (Inv n f Byz)) e := spec_entails_inv n f Byz e he
  intro k hN
  exact no_nullification (n := n) (f := f) (Byz := Byz) (s := (e.drop k) 0)
    (hInv k) hByzSub hByzCard hn hN

end TlaDsl.Examples.MinimmitTimed
