import Leslie.Examples.CacheCoherence.TileLink.Messages.Liveness.Steps
import Leslie.Examples.CacheCoherence.TileLink.Messages.StepRelease
import Leslie.Rules.LeadsTo

/-! ## Liveness Composition: Acquire Eventually Completes

    The main liveness theorem: under weak fairness of all protocol actions,
    every acquire request eventually completes.

    The proof composes per-step leads-to lemmas via `leads_to_trans`.
    Each per-step lemma is proved via WF1 in Steps.lean.

    The acquire wave phase chain:

    ```
    acquirePending
      ↝ txnActive (recvAcquire consumes chanA, creates txn)
      ↝ grantReady (probing terminates: well-founded induction on remaining probes)
      ↝ grantPendingAck (sendGrant fires)
      ↝ txnComplete (recvGrant + recvGrantAck)
    ```
-/

namespace TileLink.Messages.Liveness

open TLA TileLink SymShared

/-! ### State predicates lifted to TLA predicates -/

def txnActiveForI (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => ∃ tx, s.shared.currentTxn = some tx ∧ tx.requester = i.1)

def chanAPending (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => (s.locals i).chanA ≠ none)

def tlGrantReady (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (grantReady n)

def tlGrantPendingAck (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (grantPendingAck n)

def probingOrReady (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => ∃ tx, s.shared.currentTxn = some tx ∧
    (tx.phase = .probing ∨ tx.phase = .grantReady))

def grantAckOnChanE (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => ∃ i : Fin n, (s.locals i).chanE ≠ none)

def txnDone (n : Nat) : pred (SymState HomeState NodeState n) :=
  state_pred (fun s => s.shared.currentTxn = none)

def tlAcquirePending (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (acquirePending n i)

def tlAcquireComplete (n : Nat) (i : Fin n) : pred (SymState HomeState NodeState n) :=
  state_pred (acquireComplete n i)

/-- Count true values in a Nat → Bool function up to bound n. -/
def countTrue (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (f n).toNat + countTrue f n

@[simp] private theorem Bool.toNat_true : Bool.toNat true = 1 := rfl
@[simp] private theorem Bool.toNat_false : Bool.toNat false = 0 := rfl

@[simp] private theorem probeAckPhase_ne_grantPendingAck :
    @probeAckPhase n f ≠ TxnPhase.grantPendingAck := by
  unfold probeAckPhase; split <;> decide

theorem countTrue_pos {f : Nat → Bool} {n j : Nat} (hj : j < n) (hf : f j = true) :
    countTrue f n > 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold countTrue
    by_cases hjn : j = n
    · subst j; simp [hf]; omega
    · have := ih (by omega : j < n); omega

private theorem countTrue_congr {f g : Nat → Bool} {n : Nat}
    (h : ∀ k, k < n → f k = g k) : countTrue f n = countTrue g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold countTrue; rw [h n (by omega)]
    congr 1; exact ih (fun k hk => h k (by omega))

theorem countTrue_decrease {f : Nat → Bool} {n j : Nat} (hj : j < n) (hf : f j = true) :
    countTrue (fun k => if k = j then false else f k) n < countTrue f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold countTrue
    by_cases hjn : j = n
    · subst j
      have h1 : (if n = n then false else f n) = false := if_pos rfl
      rw [h1, hf]; simp only [Bool.toNat_false, Bool.toNat_true]
      have heq : countTrue (fun k => if k = n then false else f k) n = countTrue f n :=
        countTrue_congr (fun k hk => if_neg (by omega))
      omega
    · have hj' : j < n := by omega
      have hih := ih hj'
      have h1 : (if n = j then false else f n) = f n := if_neg (fun h => hjn h.symm)
      rw [h1]; omega

theorem countTrue_clearProbeIdx_le (f : Nat → Bool) (j n : Nat) :
    countTrue (clearProbeIdx f j) n ≤ countTrue f n := by
  induction n with
  | zero => simp [countTrue]
  | succ n ih =>
    simp only [countTrue, clearProbeIdx]
    by_cases hjn : n = j
    · subst hjn; simp [Bool.toNat]; omega
    · simp [hjn]; omega

/-- Count of remaining probes. Recursively counts true bits in probesRemaining. -/
noncomputable def probeRemainingCount (n : Nat) (e : Nat → SymState HomeState NodeState n) : Nat :=
  match e 0 |>.shared.currentTxn with
  | none => 0
  | some tx => countTrue tx.probesRemaining n

/-! ### Helper: chain leads-to under a hypothesis -/

private theorem chain2 {Γ p q r : pred σ}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r)) :
    pred_implies Γ (leads_to p r) :=
  fun e hΓ => leads_to_trans p q r e (h1 e hΓ) (h2 e hΓ)

/-! ### WF extraction from fairActions

    The fairActions list is `(List.finRange n).flatMap (fun i => [6 actions])`.
    We need to extract individual WF facts from the big conjunction. -/

private theorem bigwedge_mem_list {σ : Type _} {α : Type _}
    (f : α → pred σ) (l : List α) (a : α) (e : exec σ)
    (hmem : a ∈ l) (hbw : (tla_bigwedge (fun x => f x) l) e) : f a e := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [tla_bigwedge, Foldable.fold, List.foldr] at hbw
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact hbw.1
    · exact ih hmem' hbw.2

private theorem fairAction_in_list (n : Nat) (i : Fin n)
    (a : action (SymState HomeState NodeState n))
    (hmem : a ∈ [actRecvAcquireAtManager n i,
                 actRecvProbeAtMaster n i,
                 actRecvProbeAckAtManager n i,
                 actSendGrantToRequester n i,
                 actRecvGrantAtMaster n i,
                 actRecvGrantAckAtManager n i]) :
    a ∈ fairActions n := by
  simp only [fairActions]
  apply List.mem_flatMap.mpr
  exact ⟨i, List.mem_finRange i, hmem⟩

/-- Extract WF for actRecvAcquireAtManager. -/
private theorem extract_wf_recvAcquire {n : Nat} {e : exec (SymState HomeState NodeState n)}
    (i : Fin n) (hspec : (tlMessagesFair n).formula e) :
    weak_fairness (actRecvAcquireAtManager n i) e := by
  apply bigwedge_mem_list _ _ _ _ _ hspec.2.2
  apply fairAction_in_list; exact List.Mem.head _

/-- Extract WF for actRecvProbeAtMaster. -/
private theorem extract_wf_recvProbe {n : Nat} {e : exec (SymState HomeState NodeState n)}
    (i : Fin n) (hspec : (tlMessagesFair n).formula e) :
    weak_fairness (actRecvProbeAtMaster n i) e := by
  apply bigwedge_mem_list _ _ _ _ _ hspec.2.2
  apply fairAction_in_list; exact List.Mem.tail _ (List.Mem.head _)

/-- Extract WF for actRecvProbeAckAtManager. -/
private theorem extract_wf_recvProbeAck {n : Nat} {e : exec (SymState HomeState NodeState n)}
    (i : Fin n) (hspec : (tlMessagesFair n).formula e) :
    weak_fairness (actRecvProbeAckAtManager n i) e := by
  apply bigwedge_mem_list _ _ _ _ _ hspec.2.2
  apply fairAction_in_list; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Extract WF for actSendGrantToRequester. -/
private theorem extract_wf_sendGrant {n : Nat} {e : exec (SymState HomeState NodeState n)}
    (i : Fin n) (hspec : (tlMessagesFair n).formula e) :
    weak_fairness (actSendGrantToRequester n i) e := by
  apply bigwedge_mem_list _ _ _ _ _ hspec.2.2
  apply fairAction_in_list
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Extract WF for actRecvGrantAtMaster. -/
private theorem extract_wf_recvGrant {n : Nat} {e : exec (SymState HomeState NodeState n)}
    (i : Fin n) (hspec : (tlMessagesFair n).formula e) :
    weak_fairness (actRecvGrantAtMaster n i) e := by
  apply bigwedge_mem_list _ _ _ _ _ hspec.2.2
  apply fairAction_in_list
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- Extract WF for actRecvGrantAckAtManager. -/
private theorem extract_wf_recvGrantAck {n : Nat} {e : exec (SymState HomeState NodeState n)}
    (i : Fin n) (hspec : (tlMessagesFair n).formula e) :
    weak_fairness (actRecvGrantAckAtManager n i) e := by
  apply bigwedge_mem_list _ _ _ _ _ hspec.2.2
  apply fairAction_in_list
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

/-! ### Combined invariant: all auxiliary invariants hold always -/

private def livenessInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  fullInv n s ∧
  pendingSinkTxnInv n s ∧
  probeChannelInv n s ∧
  accessAckChanAInv n s ∧
  accessAckNotRequesterInv n s ∧
  grantWaveActiveInv n s ∧
  pendingSinkInv n s ∧
  requesterChanAInv n s ∧
  txnLineInv n s ∧
  probingHasRemainingInv n s

private theorem init_livenessInv (n : Nat) :
    ∀ s, (tlMessagesFair n).init s → livenessInv n s := by
  intro s hinit
  have hinit' : (tlMessages.toSpec n).init s := hinit
  exact ⟨init_fullInv n s hinit',
    init_pendingSinkTxnInv n s hinit',
    init_probeChannelInv n s hinit',
    init_accessAckChanAInv n s hinit',
    init_accessAckNotRequesterInv n s hinit',
    init_grantWaveActiveInv n s hinit',
    init_pendingSinkInv n s hinit',
    init_requesterChanAInv n s hinit',
    init_txnLineInv n s hinit',
    init_probingHasRemainingInv n s hinit'⟩

/-- `txnLineInv` is preserved under protocol steps, given only `fullInv` and `txnLineInv`.
    This is a lite version of `txnLineInv_preserved` from Refinement.lean which takes
    `forwardSimInv` but only uses the `fullInv` and `txnLineInv` components. -/
private theorem txnLineInv_preserved_lite (n : Nat) (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnLineInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp only [setFn, ite_true] at hpre ⊢
            simp only [txnSnapshotLine, probeSnapshotLine] at hpre ⊢; exact hpre
          · simp only [setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false] at hpre ⊢
            exact hpre
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp only [setFn, ite_true] at hpre ⊢
            simp only [txnSnapshotLine, probeSnapshotLine] at hpre ⊢; exact hpre
          · simp only [setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false] at hpre ⊢
            exact hpre
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [txnLineInv, recvAcquireState, recvAcquireShared, recvAcquireLocals_line]
        intro j
        unfold txnSnapshotLine probeSnapshotLine plannedTxn
        have hnotGPA : probeAckPhase (n := n) (probeMaskForResult s i grow.result) ≠ .grantPendingAck := by
          simp only [probeAckPhase]; split <;> decide
        have hCj := hCnone j
        have hlt := j.2
        by_cases hmask : probeMaskForResult s i grow.result j.1 = true
        · simp [hmask, hCj, hlt, hnotGPA]
        · have hmaskF : probeMaskForResult s i grow.result j.1 = false := by
            cases h : probeMaskForResult s i grow.result j.1 <;> simp_all
          simp [hmaskF, hlt, hnotGPA]
      · rcases hperm with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [txnLineInv, recvAcquireState, recvAcquireShared, recvAcquireLocals_line]
        intro j
        unfold txnSnapshotLine probeSnapshotLine plannedTxn
        have hnotGPA : probeAckPhase (n := n) (probeMaskForResult s i grow.result) ≠ .grantPendingAck := by
          simp only [probeAckPhase]; split <;> decide
        have hCj := hCnone j
        have hlt := j.2
        by_cases hmask : probeMaskForResult s i grow.result j.1 = true
        · simp [hmask, hCj, hlt, hnotGPA]
        · have hmaskF : probeMaskForResult s i grow.result j.1 = false := by
            cases h : probeMaskForResult s i grow.result j.1 <;> simp_all
          simp [hmaskF, hlt, hnotGPA]
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _hB, _hsrc, _hop, hparam, hCnone, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvProbeState, hcur]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [recvProbeLocals, recvProbeLocal, setFn, ite_true]
        have hpre_i := htxnLine i
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_i ⊢
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧
            (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧ _ ∧ _)
          with ⟨_, _, _, _, _, hsubset, _, _⟩
        have hneeded : tx.probesNeeded i.1 = true := hsubset i.1 hrem
        simp only [probeSnapshotLine, hneeded, ite_true, hrem, hCnone, and_self] at hpre_i
        simp only [probeSnapshotLine, hneeded, ite_true, hrem]
        simp only [show (some (probeAckMsg i (s.locals i).line) = none) = False from by simp, and_false, ite_false]
        rw [hpre_i, hparam]
      · simp only [recvProbeLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        exact htxnLine j
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, hC, _hsrc, _hwf, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvProbeAckState, recvProbeAckShared, hcur]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [recvProbeAckLocals, recvProbeAckLocal, setFn, ite_true]
        have hpre_i := htxnLine i
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_i ⊢
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧
            (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧ _ ∧ _)
          with ⟨_, _, _, _, _, hsubset, _, _⟩
        have hneeded : tx.probesNeeded i.1 = true := hsubset i.1 hrem
        have hnotGPA' : ¬((probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) = .grantPendingAck ∧
            tx.requester = i.1) := by
          intro ⟨h, _⟩; simp [probeAckPhase] at h; split at h <;> cases h
        simp only [hnotGPA', ite_false]
        simp only [probeSnapshotLine, hneeded, ite_true] at hpre_i ⊢
        simp only [hC, hrem, show (some msg = none) = False from by simp, and_false, ite_false] at hpre_i
        simp only [clearProbeIdx, show i.1 = i.1 from rfl, ite_true, show (false = true) = False from by simp,
          false_and, ite_false]
        exact hpre_i
      · simp only [recvProbeAckLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hpre_j := htxnLine j
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = j.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        have hnotGPA' : ¬((probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) = .grantPendingAck ∧
            tx.requester = j.1) := by
          intro ⟨h, _⟩; simp [probeAckPhase] at h; split at h <;> cases h
        simp only [txnSnapshotLine, hnotGPA, hnotGPA', ite_false] at hpre_j ⊢
        simp only [probeSnapshotLine] at hpre_j ⊢
        have hne : i.1 ≠ j.1 := by intro h; exact hji (Fin.ext_iff.mpr h.symm)
        simp only [clearProbeIdx, show (j.1 = i.1) = False from propext ⟨fun h => hne h.symm, False.elim⟩, ite_false]
        exact hpre_j
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, hreq, hphase, _, _, _hD, hE, _hSink, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, sendGrantState, sendGrantShared, hcur]
      intro j
      have hpre_j := htxnLine j
      by_cases hji : j = i
      · subst j
        simp only [sendGrantLocals, setFn, ite_true, sendGrantLocal]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hE]
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_j
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧ _ ∧ _ ∧ _)
          with ⟨_, _, _, _, hnoProbeReq, _, _, _⟩
        rw [hreq] at hnoProbeReq
        simp only [probeSnapshotLine, hnoProbeReq, ite_false] at hpre_j
        exact hpre_j
      · simp only [sendGrantLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hreq_ne : ¬(tx.requester = j.1) := by
          intro h; apply hji; exact Fin.ext_iff.mpr (by rw [← hreq]; exact h.symm)
        -- Post txn has phase = grantPendingAck, but requester ≠ j → probeSnapshotLine
        simp only [txnSnapshotLine]
        simp only [show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl, true_and,
          hreq_ne, ite_false]
        -- Pre: phase = grantReady → also probeSnapshotLine (with original tx)
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = j.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_j
        -- probeSnapshotLine doesn't use phase, so both are equal
        simp only [probeSnapshotLine] at hpre_j ⊢
        exact hpre_j
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, hreq, hphase, _, _hA, _hD, hE, _hSink, _hmsg, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvGrantState, recvGrantShared, hcur]
      intro j
      have hpre_j := htxnLine j
      by_cases hji : j = i
      · subst j
        simp only [recvGrantLocals, recvGrantLocal, setFn, ite_true]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hphase]
        simp only [show (some ({ sink := tx.sink } : EMsg) = none) = False from by simp, ite_false]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hphase, hE, ite_true] at hpre_j
        rw [hpre_j]
      · simp only [recvGrantLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hreq_ne : ¬(tx.requester = j.1) := by
          intro h; apply hji; exact Fin.ext_iff.mpr (by rw [← hreq]; exact h.symm)
        simp only [txnSnapshotLine, show ¬(TxnPhase.grantPendingAck = TxnPhase.grantPendingAck ∧ tx.requester = j.1) from
          fun ⟨_, h⟩ => hreq_ne h, ite_false] at hpre_j ⊢
        exact hpre_j
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease param =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      -- currentTxn = none → txnLineInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact htxnLine
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, msg, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨msg, _, _, hs'⟩
      rw [hs']
      -- currentTxn unchanged (shared unchanged), so match on pre-state currentTxn
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp [setFn] at hpre ⊢; exact hpre
          · simp [setFn, hji] at hpre ⊢; exact hpre

private theorem livenessInv_preserved (n : Nat) :
    ∀ s s', (tlMessagesFair n).next s s' → livenessInv n s → livenessInv n s' := by
  intro s s' hnext ⟨hfull, hpst, hpci, hacca, hnotreq, hgwa, hpsi, hreq, htxnLine, hphr⟩
  have hnext' : (tlMessages.toSpec n).next s s' := hnext
  -- Use the individual preservation theorems
  exact ⟨fullInv_preserved_with_release n s s' hfull htxnLine hnext',
    pendingSinkTxnInv_preserved hfull hpst hnext',
    probeChannelInv_preserved hfull hpci hnext',
    accessAckChanAInv_preserved hfull hacca hnext',
    accessAckNotRequesterInv_preserved hfull hacca hnotreq hnext',
    grantWaveActiveInv_preserved hfull hnotreq hgwa hnext',
    pendingSinkInv_preserved hfull hnotreq hpst hgwa hnext',
    requesterChanAInv_preserved hfull hnotreq hreq hnext',
    txnLineInv_preserved_lite n s s' hfull htxnLine hnext',
    probingHasRemainingInv_preserved hphr hnext'⟩

private theorem always_livenessInv (n : Nat) (e : exec (SymState HomeState NodeState n))
    (hspec : (tlMessagesFair n).formula e) : ∀ k, livenessInv n (e k) := by
  have hinit := hspec.1
  have hnext := hspec.2.1
  intro k
  induction k with
  | zero => exact init_livenessInv n (e 0) hinit
  | succ k ih =>
    exact livenessInv_preserved n (e k) (e (k + 1)) (hnext k) ih

/-! ### State-level WF1 helper

    We provide a helper that lifts state-level premises to WF1Premises on a suffix.
    The key issue: WF1 on a suffix `e.drop k` creates `exec.drop`-wrapped terms
    that resist `subst`/`rfl` patterns. We work around this by providing the
    safety/progress/enablement premises in terms of plain states. -/

/-- State-level safety: grantReady is preserved or becomes grantPendingAck. -/
private theorem grantReady_safety {n : Nat} (s s' : SymState HomeState NodeState n)
    (hgr : grantReady n s) (hnxt : (tlMessages.toSpec n).next s s') :
    grantReady n s' ∨ grantPendingAck n s' := by
  rcases hgr with ⟨tx', hcur', hphase'⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnxt
  obtain ⟨j, a, hstep⟩ := hnxt
  match a with
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx0, hcur0, _, _, _, _, _, _, _, rfl⟩
      right; rw [hcur0] at hcur'; cases Option.some.inj hcur'
      exact ⟨{ tx' with phase := .grantPendingAck },
        by simp [sendGrantState, sendGrantShared], rfl⟩
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, hphase0, _, _, _, _, _, rfl⟩
      rw [hcur0] at hcur'; cases Option.some.inj hcur'
      exact absurd hphase0 (by rw [hphase']; decide)
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, hphase0, _, _, _, _, _, _, rfl⟩
      rw [hcur0] at hcur'; cases Option.some.inj hcur'
      exact absurd hphase0 (by rw [hphase']; decide)
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, _, hphase0, _, _, _, _, _, rfl⟩
      rw [hcur0] at hcur'; cases Option.some.inj hcur'
      exact absurd hphase0 (by rw [hphase']; decide)
  | .recvAcquireAtManager =>
      rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
      · rcases hblk with ⟨hcurNone, _⟩; rw [hcur'] at hcurNone; simp at hcurNone
      · rcases hperm with ⟨hcurNone, _⟩; rw [hcur'] at hcurNone; simp at hcurNone
  | .sendRelease _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, hcurNone, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .store _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .uncachedGet _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .uncachedPut _ _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; exact ⟨tx', hcur', hphase'⟩
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; exact ⟨tx', hcur', hphase'⟩
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨tx', hcur', hphase'⟩
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      left; exact ⟨tx', hcur', hphase'⟩
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      left; exact ⟨tx', hcur', hphase'⟩

/-- One-step: if grantReady holds before and after a step, currentTxn is unchanged. -/
private theorem grantReady_preserves_txn {n : Nat} (s s' : SymState HomeState NodeState n)
    (hgr : grantReady n s) (hgr' : grantReady n s')
    (hnxt : (tlMessages.toSpec n).next s s') :
    s'.shared.currentTxn = s.shared.currentTxn := by
  rcases hgr with ⟨tx', hcur', hphase'⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnxt
  obtain ⟨j, a, hstep⟩ := hnxt
  match a with
  | .sendGrantToRequester =>
      -- sendGrant transitions to grantPendingAck, not grantReady
      rcases hstep with ⟨tx0, hcur0, _, _, _, _, _, _, _, rfl⟩
      rcases hgr' with ⟨tx1, hcur1, hphase1⟩
      simp only [sendGrantState, sendGrantShared, SymState.shared] at hcur1
      cases hcur1; simp at hphase1
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, hphase0, _, _, _, _, _, rfl⟩
      rw [hcur0] at hcur'; cases Option.some.inj hcur'
      exact absurd hphase0 (by rw [hphase']; decide)
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, hphase0, _, _, _, _, _, _, rfl⟩
      rw [hcur0] at hcur'; cases Option.some.inj hcur'
      exact absurd hphase0 (by rw [hphase']; decide)
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, _, hphase0, _, _, _, _, _, rfl⟩
      rw [hcur0] at hcur'; cases Option.some.inj hcur'
      exact absurd hphase0 (by rw [hphase']; decide)
  | .recvAcquireAtManager =>
      rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
      · rcases hblk with ⟨hcurNone, _⟩; rw [hcur'] at hcurNone; simp at hcurNone
      · rcases hperm with ⟨hcurNone, _⟩; rw [hcur'] at hcurNone; simp at hcurNone
  | .sendRelease _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, hcurNone, _, _, _, _, _, rfl⟩
      rw [hcur'] at hcurNone; simp at hcurNone
  | .store _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩; rfl
  | .uncachedGet _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩; rfl
  | .uncachedPut _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩; rfl
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; rfl
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩; rfl
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩; rfl
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩; rfl
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; rfl
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; rfl

/-- One-step safety for the specific-tx predicate: if currentTxn = some tx with
    tx.phase = grantReady and a step fires, then either currentTxn is still some tx
    with grantReady, or grantPendingAck holds. -/
private theorem grantReady_specific_safety {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (tx : ManagerTxn)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantReady)
    (hnxt : (tlMessages.toSpec n).next s s') :
    (s'.shared.currentTxn = some tx ∧ tx.phase = .grantReady) ∨ grantPendingAck n s' := by
  have hgr : grantReady n s := ⟨tx, hcur, hphase⟩
  rcases grantReady_safety s s' hgr hnxt with hgr' | hpa
  · have hpres := grantReady_preserves_txn s s' hgr hgr' hnxt
    left; exact ⟨hpres ▸ hcur, hphase⟩
  · right; exact hpa

/-- State-level progress: sendGrant advances grantReady to grantPendingAck. -/
private theorem grantReady_progress {n : Nat} (i : Fin n)
    (s s' : SymState HomeState NodeState n)
    (hgr : grantReady n s) (hact : actSendGrantToRequester n i s s') :
    grantPendingAck n s' := by
  rcases hact with ⟨a, ha, hstep⟩; cases ha
  rcases hgr with ⟨tx', hcur', hphase'⟩
  rcases hstep with ⟨tx0, hcur0, _, _, _, _, _, _, _, rfl⟩
  rw [hcur0] at hcur'; cases Option.some.inj hcur'
  exact ⟨{ tx' with phase := .grantPendingAck },
    by simp [sendGrantState, sendGrantShared], rfl⟩

/-! ### Per-step leads-to lemmas

    Each is proved by applying WF1 with the appropriate fair action.
    The WF1 premises are:
    1. Safety: p ∧ next ⇒ ◯p ∨ ◯q (stuttering or progress)
    2. Progress: p ∧ next ∧ a ⇒ ◯q (the fair action advances)
    3. Enablement: p ⇒ Enabled(a) ∨ q
    4. Fairness: □⟨next⟩ ∧ WF(a) -/

/-- Step 2: During probing, probes are eventually consumed.
    Uses well-founded induction on |{j | probesRemaining j = true}|.
    Each iteration uses WF1 on recvProbeAtMaster or recvProbeAckAtManager. -/
theorem probing_leads_to_grantReady (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (probingOrReady n) (tlGrantReady n)) := by
  intro e hspec k hp
  -- probingOrReady = probing ∨ grantReady. If already grantReady, done.
  simp only [probingOrReady, state_pred, exec.drop] at hp
  rcases hp with ⟨tx, hcur, hphase⟩
  rcases hphase with hprobing | hready
  · -- Probing phase: use leads_to_via_nat with probe count measure.
    -- Prove leads_to for "probing" ↝ "grantReady" on the full execution, then instantiate.
    let p : pred (SymState HomeState NodeState n) := state_pred (fun s =>
      ∃ tx' : ManagerTxn, s.shared.currentTxn = some tx' ∧ tx'.phase = TxnPhase.probing)
    have hp_k : p (e.drop k) := by
      simp only [p, state_pred, exec.drop, Nat.add_zero]; exact ⟨tx, hcur, hprobing⟩
    suffices h_lt : pred_implies (tlMessagesFair n).formula (leads_to p (tlGrantReady n)) from
      h_lt e hspec k hp_k
    apply leads_to_via_nat (probeRemainingCount n)
    · -- Step case: count = m > 0 → eventually grantReady or count decreased
      intro m hm e' hspec' i' hp' hmu
      -- Extract state info at position i'
      simp only [p, state_pred, exec.drop, Nat.add_zero] at hp'
      rcases hp' with ⟨tx', hcur', hphase'⟩
      -- Get invariants at position i'
      have hinv := always_livenessInv n e' hspec' i'
      rcases hinv with ⟨hfull', _, hpci', _, _, _, _, _, _, hphr'⟩
      -- There exists a remaining probe j
      have ⟨j, hrem⟩ := hphr' tx' hcur' hphase'
      -- By probeChannelInv, j has chanB or chanC
      have hBC := hpci' tx' hcur' hphase' j hrem
      -- Use WF1 on recvProbeAck j (when chanC j ≠ none) or
      -- recvProbe j then recvProbeAck j (when chanB j ≠ none).
      -- Define q_step: grantReady or (probing with smaller count)
      let q_step : pred _ := fun e0 => tlGrantReady n e0 ∨
        (p e0 ∧ probeRemainingCount n e0 < m)
      -- It suffices to find j' with q_step at (e'.drop (i' + j'))
      suffices hs : ∃ j', q_step (e'.drop (i' + j')) by
        rcases hs with ⟨j', hq⟩
        exact ⟨j', hq⟩
      -- Define p_pa: probing with remaining j, chanC j set, count ≤ m
      let p_pa : pred (SymState HomeState NodeState n) := state_pred (fun s =>
        ∃ tx0 : ManagerTxn, s.shared.currentTxn = some tx0 ∧ tx0.phase = TxnPhase.probing ∧
          tx0.probesRemaining j.1 = true ∧ (s.locals j).chanC ≠ none ∧
          countTrue tx0.probesRemaining n ≤ m)
      -- WF1: p_pa ↝ q_step via recvProbeAck j (factor out before case split)
      have hwf1 : leads_to p_pa q_step (e'.drop i') := by
        apply wf1_apply (next := (tlMessages.toSpec n).next) (a := actRecvProbeAckAtManager n j)
        exact {
          safety := by
            intro kk hpk hnxt
            simp only [p_pa, state_pred, exec.drop, Nat.add_zero] at hpk
            rcases hpk with ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
            -- Create exec.drop-form aliases for rw compatibility with step hypotheses
            have hcur0' : ((e'.drop i') kk).shared.currentTxn = some tx0 := hcur0
            have hphase0' : tx0.phase = TxnPhase.probing := hphase0
            have hrem0' : tx0.probesRemaining j.1 = true := hrem0
            have hCj0' : (((e'.drop i') kk).locals j).chanC ≠ none := hCj0
            -- Generalize post-state to a variable so rcases...rfl can substitute it
            generalize hpost : (e'.drop i') (kk + 1) = s_post at hnxt
            simp only [SymSharedSpec.toSpec, tlMessages] at hnxt
            obtain ⟨ii, a, hstep⟩ := hnxt
            -- Most actions either preserve p_pa or are disabled during probing.
            -- Only recvProbeAck k (k≠j) achieves q_step (count decreases).
            match a with
            -- Frame: shared unchanged, chanC j unchanged
            | .sendAcquireBlock _ _ =>
                rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
                simp only [exec.drop] at hpost
                left; show p_pa ((e'.drop (i' + kk)).drop 1)
                simp only [p_pa, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                rw [hpost]
                by_cases hjii : j = ii
                · cases hjii; simp [setFn]; exact ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
                · simp [setFn, hjii]; exact ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
            | .sendAcquirePerm _ _ =>
                rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
                simp only [exec.drop] at hpost
                left; show p_pa ((e'.drop (i' + kk)).drop 1)
                simp only [p_pa, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                rw [hpost]
                by_cases hjii : j = ii
                · cases hjii; simp [setFn]; exact ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
                · simp [setFn, hjii]; exact ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
            -- Disabled: currentTxn = none → contradiction
            | .recvAcquireAtManager =>
                rcases hstep with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
                { rcases h with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn }
            -- recvProbe: for j, requires chanC j = none → contradiction.
            -- For k≠j: chanC j unchanged, shared unchanged → p_pa preserved.
            | .recvProbeAtMaster =>
                rcases hstep with ⟨_, _, _, _, _, _, _, _, _, hCnone, rfl⟩
                simp only [exec.drop] at hpost
                left; show p_pa ((e'.drop (i' + kk)).drop 1)
                simp only [p_pa, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                rw [hpost]
                simp only [recvProbeState, SymState.shared, recvProbeLocals, SymState.locals]
                by_cases hjii : j = ii
                · cases hjii; simp [hCj0'] at hCnone
                · refine ⟨tx0, hcur0, hphase0, hrem0, ?_, hbound⟩
                  simp [setFn, hjii]; exact hCj0
            -- recvProbeAck k: if k=j, the fair action fires (handled by progress).
            -- If k≠j: remaining j unchanged, chanC j unchanged. Count decreases → q_step.
            | .recvProbeAckAtManager =>
                rcases hstep with ⟨tx1, msg1, hcur1, hphase1, hrem1, hC1, hsrc1, hwf1_m, rfl⟩
                simp only [exec.drop] at hpost
                rw [hcur0'] at hcur1; have := Option.some.inj hcur1; subst this
                -- ii is the node that processed the probeAck
                by_cases hjii : j = ii
                · -- j = ii: this is the fair action (recvProbeAck j fires → progress)
                  cases hjii
                  right; show q_step ((e'.drop (i' + kk)).drop 1)
                  simp only [q_step, p, tlGrantReady, state_pred, exec.drop_drop, exec.drop,
                    Nat.add_zero, Nat.add_assoc]
                  rw [hpost]
                  simp only [recvProbeAckState, SymState.shared, recvProbeAckShared]
                  -- New tx has clearProbeIdx, new phase
                  by_cases hphPA : (@probeAckPhase n (clearProbeIdx tx0.probesRemaining j.1)) = TxnPhase.grantReady
                  · left; exact ⟨_, rfl, hphPA⟩
                  · right
                    have hphPr : @probeAckPhase n (clearProbeIdx tx0.probesRemaining j.1) = TxnPhase.probing := by
                      unfold probeAckPhase at hphPA ⊢
                      split
                      · next h => rw [dif_pos h] at hphPA; exact absurd rfl hphPA
                      · rfl
                    constructor
                    · exact ⟨_, rfl, hphPr⟩
                    · -- count decrease: clearProbeIdx < original ≤ m
                      show probeRemainingCount n (e'.drop (i' + (kk + 1))) < m
                      simp only [probeRemainingCount, exec.drop, Nat.add_zero]
                      rw [hpost]; simp only [recvProbeAckState, SymState.shared, recvProbeAckShared]
                      unfold clearProbeIdx
                      have := countTrue_decrease j.2 hrem0; clear hmu; omega
                · -- k ≠ j: remaining j unchanged, count decreases → q_step
                  right; show q_step ((e'.drop (i' + kk)).drop 1)
                  simp only [q_step, p, tlGrantReady, state_pred, exec.drop_drop, exec.drop,
                    Nat.add_zero, Nat.add_assoc]
                  rw [hpost]
                  simp only [recvProbeAckState, SymState.shared, recvProbeAckShared,
                    recvProbeAckLocals, SymState.locals]
                  have hjne : j.1 ≠ ii.1 := fun h => hjii (Fin.ext h)
                  by_cases hphPA : (@probeAckPhase n (clearProbeIdx tx0.probesRemaining ii.1)) = TxnPhase.grantReady
                  · left; exact ⟨_, rfl, hphPA⟩
                  · right
                    have hphPr : @probeAckPhase n (clearProbeIdx tx0.probesRemaining ii.1) = TxnPhase.probing := by
                      unfold probeAckPhase at hphPA ⊢
                      split
                      · next h => rw [dif_pos h] at hphPA; exact absurd rfl hphPA
                      · rfl
                    constructor
                    · exact ⟨_, rfl, hphPr⟩
                    · show probeRemainingCount n (e'.drop (i' + (kk + 1))) < m
                      simp only [probeRemainingCount, exec.drop, Nat.add_zero]
                      rw [hpost]; simp only [recvProbeAckState, SymState.shared, recvProbeAckShared]
                      unfold clearProbeIdx
                      have := countTrue_decrease ii.2 hrem1; clear hmu; omega
            -- Disabled: phase mismatch
            | .sendGrantToRequester =>
                rcases hstep with ⟨tx1, hc1, _, hph, _, _, _, _, _, rfl⟩
                rw [hcur0'] at hc1; have := Option.some.inj hc1; subst this
                rw [hphase0'] at hph; cases hph
            | .recvGrantAtMaster =>
                rcases hstep with ⟨tx1, _, hc1, _, hph, _, _, _, _, _, _, rfl⟩
                rw [hcur0'] at hc1; have := Option.some.inj hc1; subst this
                rw [hphase0'] at hph; cases hph
            | .recvGrantAckAtManager =>
                rcases hstep with ⟨tx1, _, hc1, _, hph, _, _, _, _, _, rfl⟩
                rw [hcur0'] at hc1; have := Option.some.inj hc1; subst this
                rw [hphase0'] at hph; cases hph
            -- Disabled: currentTxn = none
            | .sendRelease _ =>
                rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
            | .sendReleaseData _ =>
                rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
            | .recvReleaseAtManager =>
                rcases hstep with ⟨_, _, hcn, _⟩; simp [recvReleaseState, recvReleaseShared] at *
                rw [hcur0'] at hcn; simp at hcn
            | .recvReleaseAckAtMaster =>
                rcases hstep with ⟨_, hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
            | .store _ =>
                rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
            | .read =>
                rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
                simp only [exec.drop] at hpost
                left; show p_pa ((e'.drop (i' + kk)).drop 1)
                simp only [p_pa, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                rw [hpost]
                exact ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
            | .uncachedGet _ =>
                rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
            | .uncachedPut _ _ =>
                rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
            | .recvUncachedAtManager =>
                rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
            | .recvAccessAckAtMaster =>
                rcases hstep with ⟨_, _, _, rfl⟩
                simp only [exec.drop] at hpost
                left; show p_pa ((e'.drop (i' + kk)).drop 1)
                simp only [p_pa, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                rw [hpost]
                by_cases hjii : j = ii
                · cases hjii; simp [setFn]; exact ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
                · simp [setFn, hjii]; exact ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
          progress := by
            intro kk hpk hnxt hact
            simp only [p_pa, state_pred, exec.drop, Nat.add_zero] at hpk
            rcases hpk with ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
            have hcur0' : ((e'.drop i') kk).shared.currentTxn = some tx0 := hcur0
            generalize hpost : (e'.drop i') (kk + 1) = s_post at hnxt hact
            rcases hact with ⟨a, ha, hstep⟩; cases ha
            -- recvProbeAck j fires
            rcases hstep with ⟨tx1, msg1, hcur1, _, hrem1, hC1, hsrc1, hwf1_m, rfl⟩
            simp only [exec.drop] at hpost
            rw [hcur0'] at hcur1; have := Option.some.inj hcur1; subst this
            show q_step ((e'.drop (i' + kk)).drop 1)
            simp only [q_step, p, tlGrantReady, state_pred, exec.drop_drop, exec.drop,
              Nat.add_zero, Nat.add_assoc]
            rw [hpost]
            simp only [recvProbeAckState, SymState.shared, recvProbeAckShared]
            by_cases hphPA : (@probeAckPhase n (clearProbeIdx tx0.probesRemaining j.1)) = TxnPhase.grantReady
            · left; exact ⟨_, rfl, hphPA⟩
            · right
              have hphPr : @probeAckPhase n (clearProbeIdx tx0.probesRemaining j.1) = TxnPhase.probing := by
                unfold probeAckPhase at hphPA ⊢; split
                · next h => rw [dif_pos h] at hphPA; exact absurd rfl hphPA
                · rfl
              constructor
              · exact ⟨_, rfl, hphPr⟩
              · show probeRemainingCount n (e'.drop (i' + (kk + 1))) < m
                simp only [probeRemainingCount, exec.drop, Nat.add_zero]
                rw [hpost]; simp only [recvProbeAckState, SymState.shared, recvProbeAckShared]
                unfold clearProbeIdx
                have := countTrue_decrease j.2 hrem0; clear hmu; omega
          enablement := by
            intro kk hpk
            simp only [p_pa, state_pred, exec.drop, Nat.add_zero] at hpk
            rcases hpk with ⟨tx0, hcur0, hphase0, hrem0, hCj0, hbound⟩
            -- Get chanCInv to extract message properties
            have hinv_kk := always_livenessInv n e' hspec' (i' + kk)
            rcases hinv_kk with ⟨⟨_, ⟨_, _, hchanC_kk, _, _⟩, _⟩, _⟩
            -- chanC j has a message
            have hcc := hchanC_kk j
            rcases (show ∃ msg, ((e' (i' + kk)).locals j).chanC = some msg from
              match h : ((e' (i' + kk)).locals j).chanC with
              | some msg => ⟨msg, rfl⟩
              | none => absurd h hCj0) with ⟨msg, hCmsg⟩
            rw [hCmsg] at hcc
            -- chanCInv gives us message properties
            rcases hcc with ⟨tx1, hcur1, _, _, _, _, hsrc, hwfm, _⟩ | ⟨_, hcurNone, _⟩
            · -- probeAck case: msg has correct source and is well-formed
              left; show ∃ s', actRecvProbeAckAtManager n j (e' (i' + kk)) s'
              rw [hcur0] at hcur1; have := Option.some.inj hcur1; subst this
              exact ⟨recvProbeAckState (e' (i' + kk)) j tx0 msg,
                .recvProbeAckAtManager, rfl, tx0, msg, hcur0, hphase0, hrem0, hCmsg, hsrc, hwfm, rfl⟩
            · -- release case: currentTxn = none → contradiction
              rw [hcur0] at hcurNone; simp at hcurNone
          always_next := by
            intro m; rw [exec.drop_drop]; exact hspec'.2.1 (i' + m)
          fair := by
            intro m henabled
            rw [exec.drop_drop] at henabled
            have h := (extract_wf_recvProbeAck j hspec') (i' + m) henabled
            rw [exec.drop_drop]; exact h
        }
      -- Case split: chanB j or chanC j
      rcases hBC with hBj | hCj
      · -- Case: chanB j ≠ none — WF1 on recvProbe j reaches p_pa or q_step, then compose with hwf1
        -- Define p_pb: probing, remaining j, chanB j set, chanC j = none, count ≤ m
        let p_pb : pred (SymState HomeState NodeState n) := state_pred (fun s =>
          ∃ tx0 : ManagerTxn, s.shared.currentTxn = some tx0 ∧ tx0.phase = TxnPhase.probing ∧
            tx0.probesRemaining j.1 = true ∧ (s.locals j).chanB ≠ none ∧
            (s.locals j).chanC = none ∧ countTrue tx0.probesRemaining n ≤ m)
        have hp_pb : p_pb (e'.drop i') := by
          simp only [p_pb, state_pred, exec.drop, Nat.add_zero]
          refine ⟨tx', hcur', hphase', hrem, hBj, ?_, ?_⟩
          · -- chanC j = none: chanCInv says if chanC j ≠ none then chanB j = none.
            -- Contrapositively, chanB j ≠ none → chanC j = none.
            -- Extract chanBInv and chanCInv from fullInv at position i'
            rcases hfull' with ⟨_, ⟨_, hchanB_i', hchanC_i', _, _⟩, _⟩
            have hcb := hchanB_i' j
            rcases (show ∃ msg, ((e' i').locals j).chanB = some msg from
              match h : ((e' i').locals j).chanB with
              | some msg => ⟨msg, rfl⟩
              | none => absurd h hBj) with ⟨msg, hBmsg⟩
            rw [hBmsg] at hcb
            have hcc := hchanC_i' j
            match hcj : ((e' i').locals j).chanC with
            | none => exact rfl
            | some cmsg =>
                rw [hcj] at hcc
                rcases hcc with ⟨_, _, _, _, _, hcbNone, _, _, _⟩ | ⟨_, hcurNone, _⟩
                · rw [hBmsg] at hcbNone; simp at hcbNone
                · rw [hcur'] at hcurNone; simp at hcurNone
          · simp only [probeRemainingCount, exec.drop, Nat.add_zero, hcur'] at hmu; omega
        let q_pb := fun e0 => q_step e0 ∨ p_pa e0
        -- WF1: p_pb ↝ q_pb via recvProbe j
        have hwf2 : leads_to p_pb q_pb (e'.drop i') := by
          apply wf1_apply (next := (tlMessages.toSpec n).next) (a := actRecvProbeAtMaster n j)
          exact {
            safety := by
              intro kk hpk hnxt
              simp only [p_pb, state_pred, exec.drop, Nat.add_zero] at hpk
              rcases hpk with ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
              have hcur0' : ((e'.drop i') kk).shared.currentTxn = some tx0 := hcur0
              have hphase0' : tx0.phase = TxnPhase.probing := hphase0
              have hBj0' : (((e'.drop i') kk).locals j).chanB ≠ none := hBj0
              have hCj0' : (((e'.drop i') kk).locals j).chanC = none := hCj0
              generalize hpost : (e'.drop i') (kk + 1) = s_post at hnxt
              simp only [SymSharedSpec.toSpec, tlMessages] at hnxt
              obtain ⟨ii, a, hstep⟩ := hnxt
              match a with
              -- Frame: shared unchanged, chanB/chanC j unchanged
              | .sendAcquireBlock _ _ =>
                  rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
                  simp only [exec.drop] at hpost
                  left; show p_pb ((e'.drop (i' + kk)).drop 1)
                  simp only [p_pb, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                  rw [hpost]
                  by_cases hjii : j = ii
                  · cases hjii; simp [setFn]; exact ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
                  · simp [setFn, hjii]; exact ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
              | .sendAcquirePerm _ _ =>
                  rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
                  simp only [exec.drop] at hpost
                  left; show p_pb ((e'.drop (i' + kk)).drop 1)
                  simp only [p_pb, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                  rw [hpost]
                  by_cases hjii : j = ii
                  · cases hjii; simp [setFn]; exact ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
                  · simp [setFn, hjii]; exact ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
              -- Disabled: currentTxn = none → contradiction
              | .recvAcquireAtManager =>
                  rcases hstep with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
                  { rcases h with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn }
              -- recvProbe ii: if ii=j, chanB j cleared, chanC j set → p_pa (→ q_pb right)
              -- If ii≠j: chanB j unchanged, chanC j unchanged, shared unchanged → p_pb preserved
              | .recvProbeAtMaster =>
                  rcases hstep with ⟨_, _, _, _, _, _, _, _, _, hCnone_ii, rfl⟩
                  simp only [exec.drop] at hpost
                  by_cases hjii : j = ii
                  · -- j = ii: recvProbe j fires → chanC j set → p_pa
                    cases hjii
                    right; right; show p_pa ((e'.drop (i' + kk)).drop 1)
                    simp only [p_pa, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                    rw [hpost]
                    simp only [recvProbeState, SymState.shared, recvProbeLocals, SymState.locals]
                    refine ⟨tx0, hcur0, hphase0, hrem0, ?_, hbound⟩
                    simp [setFn, recvProbeLocal]
                  · -- ii ≠ j: chanB j unchanged, chanC j unchanged → p_pb preserved
                    left; show p_pb ((e'.drop (i' + kk)).drop 1)
                    simp only [p_pb, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                    rw [hpost]
                    simp only [recvProbeState, SymState.shared, recvProbeLocals, SymState.locals]
                    refine ⟨tx0, hcur0, hphase0, hrem0, ?_, ?_, hbound⟩
                    · simp [setFn, hjii]; exact hBj0
                    · simp [setFn, hjii]; exact hCj0
              -- recvProbeAck k: requires chanC k ≠ none.
              -- If k=j: chanC j = none from p_pb → contradiction
              -- If k≠j: chanB j unchanged, chanC j unchanged, count may decrease → q_step or p_pb
              | .recvProbeAckAtManager =>
                  rcases hstep with ⟨tx1, msg1, hcur1, hphase1, hrem1, hC1, hsrc1, hwf1_m, rfl⟩
                  simp only [exec.drop] at hpost
                  rw [hcur0'] at hcur1; have := Option.some.inj hcur1; subst this
                  by_cases hjii : j = ii
                  · -- j = ii: recvProbeAck j requires chanC j ≠ none, but p_pb says chanC j = none
                    cases hjii; rw [hCj0'] at hC1; simp at hC1
                  · -- k ≠ j: shared changes (count), chanB j unchanged, chanC j unchanged
                    -- Count decreases or phase changes → q_step
                    right; left; show q_step ((e'.drop (i' + kk)).drop 1)
                    simp only [q_step, p, tlGrantReady, state_pred, exec.drop_drop, exec.drop,
                      Nat.add_zero, Nat.add_assoc]
                    rw [hpost]
                    simp only [recvProbeAckState, SymState.shared, recvProbeAckShared]
                    have hjne : j.1 ≠ ii.1 := fun h => hjii (Fin.ext h)
                    by_cases hphPA : (@probeAckPhase n (clearProbeIdx tx0.probesRemaining ii.1)) = TxnPhase.grantReady
                    · left; exact ⟨_, rfl, hphPA⟩
                    · right
                      have hphPr : @probeAckPhase n (clearProbeIdx tx0.probesRemaining ii.1) = TxnPhase.probing := by
                        unfold probeAckPhase at hphPA ⊢
                        split
                        · next h => rw [dif_pos h] at hphPA; exact absurd rfl hphPA
                        · rfl
                      constructor
                      · exact ⟨_, rfl, hphPr⟩
                      · show probeRemainingCount n (e'.drop (i' + (kk + 1))) < m
                        simp only [probeRemainingCount, exec.drop, Nat.add_zero]
                        rw [hpost]; simp only [recvProbeAckState, SymState.shared, recvProbeAckShared]
                        unfold clearProbeIdx
                        have := countTrue_decrease ii.2 hrem1; clear hmu; omega
              -- Disabled: phase mismatch
              | .sendGrantToRequester =>
                  rcases hstep with ⟨tx1, hc1, _, hph, _, _, _, _, _, rfl⟩
                  rw [hcur0'] at hc1; have := Option.some.inj hc1; subst this
                  rw [hphase0'] at hph; cases hph
              | .recvGrantAtMaster =>
                  rcases hstep with ⟨tx1, _, hc1, _, hph, _, _, _, _, _, _, rfl⟩
                  rw [hcur0'] at hc1; have := Option.some.inj hc1; subst this
                  rw [hphase0'] at hph; cases hph
              | .recvGrantAckAtManager =>
                  rcases hstep with ⟨tx1, _, hc1, _, hph, _, _, _, _, _, rfl⟩
                  rw [hcur0'] at hc1; have := Option.some.inj hc1; subst this
                  rw [hphase0'] at hph; cases hph
              -- Disabled: currentTxn = none
              | .sendRelease _ =>
                  rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
              | .sendReleaseData _ =>
                  rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
              | .recvReleaseAtManager =>
                  rcases hstep with ⟨_, _, hcn, _⟩; simp [recvReleaseState, recvReleaseShared] at *
                  rw [hcur0'] at hcn; simp at hcn
              | .recvReleaseAckAtMaster =>
                  rcases hstep with ⟨_, hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
              | .store _ =>
                  rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
              | .read =>
                  rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
                  simp only [exec.drop] at hpost
                  left; show p_pb ((e'.drop (i' + kk)).drop 1)
                  simp only [p_pb, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                  rw [hpost]
                  exact ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
              | .uncachedGet _ =>
                  rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
              | .uncachedPut _ _ =>
                  rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
              | .recvUncachedAtManager =>
                  rcases hstep with ⟨hcn, _⟩; rw [hcur0'] at hcn; simp at hcn
              | .recvAccessAckAtMaster =>
                  rcases hstep with ⟨_, _, _, rfl⟩
                  simp only [exec.drop] at hpost
                  left; show p_pb ((e'.drop (i' + kk)).drop 1)
                  simp only [p_pb, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
                  rw [hpost]
                  by_cases hjii : j = ii
                  · cases hjii; simp [setFn]; exact ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
                  · simp [setFn, hjii]; exact ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
            progress := by
              intro kk hpk hnxt hact
              simp only [p_pb, state_pred, exec.drop, Nat.add_zero] at hpk
              rcases hpk with ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
              have hcur0' : ((e'.drop i') kk).shared.currentTxn = some tx0 := hcur0
              have hCj0' : (((e'.drop i') kk).locals j).chanC = none := hCj0
              generalize hpost : (e'.drop i') (kk + 1) = s_post at hnxt hact
              rcases hact with ⟨a, ha, hstep⟩; cases ha
              -- recvProbe j fires → chanC j set → p_pa
              rcases hstep with ⟨tx1, msg1, hcur1, _, hrem1, hB1, hsrc1, hop1, hparam1, hCnone1, rfl⟩
              simp only [exec.drop] at hpost
              rw [hcur0'] at hcur1; have := Option.some.inj hcur1; subst this
              right; show p_pa ((e'.drop (i' + kk)).drop 1)
              simp only [p_pa, state_pred, exec.drop_drop, exec.drop, Nat.add_zero, Nat.add_assoc]
              rw [hpost]
              simp only [recvProbeState, SymState.shared, recvProbeLocals, SymState.locals]
              refine ⟨tx0, hcur0, hphase0, hrem0, ?_, hbound⟩
              simp [setFn, recvProbeLocal]
            enablement := by
              intro kk hpk
              simp only [p_pb, state_pred, exec.drop, Nat.add_zero] at hpk
              rcases hpk with ⟨tx0, hcur0, hphase0, hrem0, hBj0, hCj0, hbound⟩
              -- Get chanBInv to extract message properties
              have hinv_kk := always_livenessInv n e' hspec' (i' + kk)
              rcases hinv_kk with ⟨⟨_, ⟨_, hchanB_kk, _, _, _⟩, _⟩, _⟩
              -- chanB j has a message
              have hcb := hchanB_kk j
              rcases (show ∃ msg, ((e' (i' + kk)).locals j).chanB = some msg from
                match h : ((e' (i' + kk)).locals j).chanB with
                | some msg => ⟨msg, rfl⟩
                | none => absurd h hBj0) with ⟨msg, hBmsg⟩
              rw [hBmsg] at hcb
              -- chanBInv gives us message properties
              rcases hcb with ⟨tx1, hcur1, hph1, hrem1, hsrc, hop, hparam⟩
              left; show ∃ s', actRecvProbeAtMaster n j (e' (i' + kk)) s'
              rw [hcur0] at hcur1; have := Option.some.inj hcur1; subst this
              exact ⟨recvProbeState (e' (i' + kk)) j msg,
                .recvProbeAtMaster, rfl, tx0, msg, hcur0, hphase0, hrem0, hBmsg, hsrc, hop, hparam, hCj0, rfl⟩
            always_next := by
              intro m; rw [exec.drop_drop]; exact hspec'.2.1 (i' + m)
            fair := by
              intro m henabled
              rw [exec.drop_drop] at henabled
              have h := (extract_wf_recvProbe j hspec') (i' + m) henabled
              rw [exec.drop_drop]; exact h
          }
        -- Chain: get p_pa or q_step from hwf2, then use hwf1 for p_pa case
        have hwf2_0 := hwf2 0 (exec.drop_zero _ ▸ hp_pb)
        rw [exec.drop_zero] at hwf2_0
        rcases hwf2_0 with ⟨j1, hj1⟩
        rcases hj1 with hqs | hpa1
        · -- q_step directly at (e'.drop i').drop j1
          exact ⟨j1, by rw [exec.drop_drop] at hqs; exact hqs⟩
        · -- p_pa at j1: apply hwf1 at offset j1
          have hwf1_j1 := hwf1 j1 hpa1
          rcases hwf1_j1 with ⟨j2, hj2⟩
          -- hj2 : q_step (((e'.drop i').drop j1).drop j2)
          rw [exec.drop_drop] at hj2  -- q_step ((e'.drop i').drop (j1 + j2))
          rw [exec.drop_drop] at hj2  -- q_step (e'.drop (i' + (j1 + j2)))
          exact ⟨j1 + j2, hj2⟩
      · -- Case: chanC j ≠ none — p_pa holds at i', use hwf1 directly
        have hp_pa : p_pa (e'.drop i') := by
          simp only [p_pa, state_pred, exec.drop, Nat.add_zero]
          refine ⟨tx', hcur', hphase', hrem, hCj, ?_⟩
          simp only [probeRemainingCount, exec.drop, Nat.add_zero, hcur'] at hmu; omega
        have hwf1_0 := hwf1 0 (exec.drop_zero _ ▸ hp_pa)
        rcases hwf1_0 with ⟨j', hj'⟩
        simp only [Nat.zero_add, exec.drop_drop] at hj'
        exact ⟨j', hj'⟩
    · -- Base case: count = 0 is vacuous (probing → count > 0)
      intro e' hspec' i' hp' hmu
      simp only [p, state_pred, exec.drop, Nat.add_zero] at hp'
      rcases hp' with ⟨tx', hcur', hphase'⟩
      have hinv := always_livenessInv n e' hspec' i'
      rcases hinv with ⟨_, _, _, _, _, _, _, _, _, hphr'⟩
      have ⟨j, hrem⟩ := hphr' tx' hcur' hphase'
      -- count = 0 but ∃ j remaining → contradiction
      simp only [probeRemainingCount, exec.drop, Nat.add_zero, hcur'] at hmu
      exact absurd (countTrue_pos j.2 hrem) (by omega)
  · -- Already grantReady: done immediately
    exact ⟨0, show tlGrantReady n (e.drop (k + 0)) from by
      simp [tlGrantReady, state_pred, exec.drop, grantReady]; exact ⟨tx, hcur, hready⟩⟩

/-- Step 3: At grantReady, the grant is sent to the requester.
    Fair action: sendGrantToRequester.
    Uses WF1 with a specific-tx predicate to track txn identity.
    Relies on sendGrant_enabled from Steps.lean. -/
theorem grantReady_leads_to_grantPendingAck (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantReady n) (tlGrantPendingAck n)) := by
  intro e hspec
  have hnext : always (action_pred (tlMessages.toSpec n).next) e := hspec.2.1
  intro k hp
  -- Extract the requester from the current state
  have hp' : grantReady n (e k) := by
    change state_pred (grantReady n) (e.drop k) at hp
    simp only [state_pred, exec.drop, Nat.add_zero] at hp; exact hp
  rcases hp' with ⟨tx, hcur, hphase⟩
  have hinvk := always_livenessInv n e hspec k
  rcases hinvk with ⟨hfull, hpst, _, _, hnotreq, _, _, _⟩
  rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
  rw [txnCoreInv, hcur] at htxnCore
  rcases htxnCore with ⟨hreqLt, _, _, _, _, _, _, _⟩
  let req : Fin n := ⟨tx.requester, hreqLt⟩
  have hwf := extract_wf_sendGrant req hspec
  -- Use a stronger predicate p that pins the specific tx
  let p : pred (SymState HomeState NodeState n) :=
    state_pred (fun s => s.shared.currentTxn = some tx ∧ tx.phase = .grantReady)
  -- p holds at position k
  have hp_k : p (e.drop k) := by
    simp only [p, state_pred, exec.drop, Nat.add_zero]; exact ⟨hcur, hphase⟩
  -- Prove leads_to p (tlGrantPendingAck n) on suffix
  suffices h : leads_to p (tlGrantPendingAck n) (e.drop k) from by
    have := h 0 (exec.drop_zero _ ▸ hp_k)
    rw [exec.drop_zero] at this; exact this
  apply wf1_apply (next := (tlMessages.toSpec n).next) (a := actSendGrantToRequester n req)
  exact {
    safety := by
      intro m hpm hnxt
      have hpm' : (e (k + m)).shared.currentTxn = some tx ∧ tx.phase = .grantReady := by
        simp only [p, state_pred, exec.drop] at hpm; exact hpm
      have hnxt' : (tlMessages.toSpec n).next (e (k + m)) (e (k + m + 1)) := hnxt
      rcases grantReady_specific_safety _ _ tx hpm'.1 hpm'.2 hnxt' with ⟨hcur', hph'⟩ | hpa
      · left; show p ((e.drop k).drop (m + 1))
        simp only [p, state_pred, exec.drop]; exact ⟨hcur', hph'⟩
      · right; show tlGrantPendingAck n ((e.drop k).drop (m + 1))
        simp only [tlGrantPendingAck, state_pred, exec.drop]; exact hpa
    progress := by
      intro m hpm hnxt hact
      have hpm' : grantReady n (e (k + m)) := by
        simp only [p, state_pred, exec.drop] at hpm
        exact ⟨tx, hpm.1, hpm.2⟩
      have hact' : actSendGrantToRequester n req (e (k + m)) (e (k + m + 1)) := hact
      have hpa := grantReady_progress req _ _ hpm' hact'
      show tlGrantPendingAck n ((e.drop k).drop (m + 1))
      simp only [tlGrantPendingAck, state_pred, exec.drop]; exact hpa
    enablement := by
      intro m hpm
      have hpm' : (e (k + m)).shared.currentTxn = some tx ∧ tx.phase = .grantReady := by
        simp only [p, state_pred, exec.drop] at hpm; exact hpm
      have hinvm := always_livenessInv n e hspec (k + m)
      rcases hinvm with ⟨hfullm, hpstm, _, _, hnotreqm, _, _, _⟩
      rcases hfullm with ⟨⟨_, _, hpendingm, htxnCorem⟩, ⟨_, _, _, hchanDm, hchanEm⟩, _⟩
      rw [txnCoreInv, hpm'.1] at htxnCorem
      rcases htxnCorem with ⟨_, _, _, _, _, _, _, _⟩
      left; show ∃ s', actSendGrantToRequester n req (e (k + m)) s'
      refine ⟨sendGrantState (e (k + m)) req tx, .sendGrantToRequester, rfl, ?_⟩
      simp only [tlMessages]
      refine ⟨tx, hpm'.1, rfl, hphase, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · rw [pendingInv, hpm'.1] at hpendingm
        rcases hpendingm with ⟨_, hga⟩; simp [hphase] at hga; exact hga
      · rw [pendingInv, hpm'.1] at hpendingm; exact hpendingm.1
      · specialize hchanDm req
        match hD : (e (k + m)).locals req |>.chanD with
        | none => rfl
        | some msg =>
          rw [hD] at hchanDm
          rcases hchanDm with ⟨tx', hcur', _, hphase', _, _, _, _⟩ | ⟨hcurNone, _⟩ | ⟨hop, _⟩
          · rw [hpm'.1] at hcur'; cases hcur'
            exact absurd hphase' (by rw [hphase]; decide)
          · rw [hpm'.1] at hcurNone; simp at hcurNone
          · exfalso; exact hnotreqm req msg hD hop tx hpm'.1 rfl
      · specialize hchanEm req
        match hE : (e (k + m)).locals req |>.chanE with
        | none => rfl
        | some msg =>
          rw [hE] at hchanEm
          rcases hchanEm with ⟨tx', hcur', _, hphase', _, _, _, _⟩
          rw [hpm'.1] at hcur'; cases hcur'
          exact absurd hphase' (by rw [hphase]; decide)
      · by_contra hps
        rcases hpstm req hps with ⟨tx', hcur', _, hphase'⟩
        rw [hpm'.1] at hcur'; cases hcur'
        exact absurd hphase' (by rw [hphase]; decide)
    always_next := by
      intro m; exact hnext (k + m)
    fair := by
      intro m henabled
      rw [exec.drop_drop] at henabled
      have h := hwf (k + m) henabled
      rw [exec.drop_drop]; exact h
  }

/-- Step 4a: At grantPendingAck, the requester receives the grant.
    From grantWaveActiveInv: chanD or chanE is non-none for the requester.
    If chanE is already non-none, we're done (grantAckOnChanE holds).
    If chanD is non-none, recvGrantAtMaster fires to move it to chanE.
    Relies on recvGrant_enabled from Steps.lean. -/
theorem grantPendingAck_leads_to_grantAckSent (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantPendingAck n) (grantAckOnChanE n)) := by
  intro e hspec k hp
  have hp' : grantPendingAck n (e k) := by
    change state_pred _ (e.drop k) at hp
    simp only [state_pred, exec.drop, Nat.add_zero] at hp; exact hp
  rcases hp' with ⟨tx, hcur, hphase⟩
  have hinvk := always_livenessInv n e hspec k
  rcases hinvk with ⟨hfull, _, _, _, _, hgwa, _, _⟩
  rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
  rw [txnCoreInv, hcur] at htxnCore
  rcases htxnCore with ⟨hreqLt, _, _, _, _, _, _, _⟩
  let req : Fin n := ⟨tx.requester, hreqLt⟩
  -- From grantWaveActiveInv: chanD or chanE at requester is non-none
  have hwave := hgwa tx hcur hphase req rfl
  rcases hwave with hchanD | hchanE
  · -- chanD ≠ none → need WF1 step with recvGrantAtMaster
    have hnext : always (action_pred (tlMessages.toSpec n).next) e := hspec.2.1
    have hwf := extract_wf_recvGrant req hspec
    -- Use a specific predicate pinning both tx and chanD at req
    let p' : pred (SymState HomeState NodeState n) :=
      state_pred (fun s => s.shared.currentTxn = some tx ∧ tx.phase = .grantPendingAck ∧
        (s.locals req).chanD ≠ none)
    have hp'_k : p' (e.drop k) := by
      simp only [p', state_pred, exec.drop, Nat.add_zero]; exact ⟨hcur, hphase, hchanD⟩
    suffices h : leads_to p' (grantAckOnChanE n) (e.drop k) from by
      have := h 0 (exec.drop_zero _ ▸ hp'_k)
      rw [exec.drop_zero] at this; exact this
    apply wf1_apply (next := (tlMessages.toSpec n).next) (a := actRecvGrantAtMaster n req)
    exact {
      safety := by
        intro m hpm hnxt
        have hpm' := by simp only [p', state_pred, exec.drop] at hpm; exact hpm
        have hcur_m : (e (k + m)).shared.currentTxn = some tx := hpm'.1
        have hphase_m : tx.phase = .grantPendingAck := hpm'.2.1
        have hchanD_m : ((e (k + m)).locals req).chanD ≠ none := hpm'.2.2
        have hnxt' : (tlMessages.toSpec n).next (e (k + m)) (e (k + m + 1)) := hnxt
        simp only [SymSharedSpec.toSpec, tlMessages] at hnxt'
        obtain ⟨j, a, hstep⟩ := hnxt'
        match a with
        | .recvGrantAtMaster =>
            -- This is the key case: if j = req, chanD consumed, chanE produced → q
            -- If j ≠ req, chanD at req unchanged → p'
            rcases hstep with ⟨tx_r, msg_r, hcur_r, hreq_r, hphase_r, _, _, hD_r, _, _, _, hs'_r⟩
            by_cases hjr : j = req
            · -- j = req: recvGrant at req consumes chanD, sets chanE → grantAckOnChanE
              right; show grantAckOnChanE n ((e.drop k).drop (m + 1))
              simp only [grantAckOnChanE, state_pred, exec.drop]
              have : ((e (k + m + 1)).locals req).chanE ≠ none := by
                rw [hs'_r, hjr]; simp [recvGrantState, recvGrantLocals, setFn, recvGrantLocal]
              exact ⟨req, this⟩
            · -- j ≠ req: chanD at req unchanged, currentTxn unchanged
              left; show p' ((e.drop k).drop (m + 1))
              simp only [p', state_pred, exec.drop]
              have hcur' : (e (k + m + 1)).shared.currentTxn = some tx := by
                rw [hs'_r]; simp only [recvGrantState, SymState.shared, recvGrantShared]
                exact hcur_m
              have hchanD' : ((e (k + m + 1)).locals req).chanD ≠ none := by
                rw [hs'_r]; simp only [recvGrantState, SymState.locals, recvGrantLocals, setFn]
                simp only [show (req = j) = False from propext ⟨fun h => hjr h.symm, False.elim⟩, ite_false]
                exact hchanD_m
              exact ⟨hcur', hphase_m, hchanD'⟩
        | .recvGrantAckAtManager =>
            -- Requires chanE ≠ none and chanD = none at j; if j = req then chanD req ≠ none
            -- contradicts guard chanD = none. If j ≠ req, currentTxn cleared → but phase is grantPendingAck
            rcases hstep with ⟨tx_r, msg_r, hcur_r, hreq_r, hphase_r, _, hD_none_r, hE_r, _, _, hs'_r⟩
            rw [hcur_m] at hcur_r; cases hcur_r
            -- tx_r = tx, so requester = j.1 and chanD j = none
            -- But req has chanD ≠ none and j.1 = tx.requester = req.1, so j = req
            -- Then chanD req = none contradicts hchanD_m
            have hjeq : j = req := by ext; exact hreq_r.symm
            rw [hjeq] at hD_none_r
            exact absurd hD_none_r hchanD_m
        | .recvAcquireAtManager =>
            -- Requires currentTxn = none, but we have currentTxn = some tx
            rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
            · rcases hblk with ⟨hcurNone, _⟩; rw [hcur_m] at hcurNone; simp at hcurNone
            · rcases hperm with ⟨hcurNone, _⟩; rw [hcur_m] at hcurNone; simp at hcurNone
        | .sendGrantToRequester =>
            -- Requires phase = grantReady, but we have grantPendingAck
            rcases hstep with ⟨tx_r, hcur_r, _, hphase_r, _, _, _, _, _, _⟩
            rw [hcur_m] at hcur_r; cases hcur_r
            exact absurd hphase_r (by rw [hphase_m]; decide)
        | .recvProbeAckAtManager =>
            -- Requires phase = probing, but we have grantPendingAck
            rcases hstep with ⟨tx_r, _, hcur_r, hphase_r, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcur_r; cases hcur_r
            exact absurd hphase_r (by rw [hphase_m]; decide)
        | .recvProbeAtMaster =>
            -- Requires phase = probing, but we have grantPendingAck
            rcases hstep with ⟨tx_r, _, hcur_r, hphase_r, _, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcur_r; cases hcur_r
            exact absurd hphase_r (by rw [hphase_m]; decide)
        | .sendRelease _ =>
            -- Requires currentTxn = none
            rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .sendReleaseData _ =>
            -- Requires currentTxn = none
            rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .recvReleaseAtManager =>
            -- Requires currentTxn = none
            rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .recvReleaseAckAtMaster =>
            -- Requires currentTxn = none
            rcases hstep with ⟨_, hcurNone, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .store _ =>
            -- Requires currentTxn = none
            rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .read =>
            -- s' = s
            rcases hstep with ⟨_, _, _, _, _, _, hs'_r⟩
            left; show p' ((e.drop k).drop (m + 1))
            simp only [p', state_pred, exec.drop]
            have hcur' : (e (k + m + 1)).shared.currentTxn = some tx := hs'_r ▸ hcur_m
            have hchanD' : ((e (k + m + 1)).locals req).chanD ≠ none := hs'_r ▸ hchanD_m
            exact ⟨hcur', hphase_m, hchanD'⟩
        | .uncachedGet _ =>
            -- Requires currentTxn = none
            rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .uncachedPut _ _ =>
            -- Requires currentTxn = none
            rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .recvUncachedAtManager =>
            -- Requires currentTxn = none
            rcases hstep with ⟨hcurNone, _, _, _, _, _, hs'_r⟩
            rw [hcur_m] at hcurNone; simp at hcurNone
        | .sendAcquireBlock _ _ =>
            -- Shared unchanged, chanD at req unchanged (only chanA/pendingSource at j change)
            rcases hstep with ⟨_, _, _, _, _, _, _, hs'_r⟩
            left; show p' ((e.drop k).drop (m + 1))
            simp only [p', state_pred, exec.drop]
            have hcur' : (e (k + m + 1)).shared.currentTxn = some tx := by
              rw [hs'_r]; exact hcur_m
            have hchanD' : ((e (k + m + 1)).locals req).chanD ≠ none := by
              rw [hs'_r]; simp only [SymState.locals, setFn]
              split
              · -- req = j: chanD of the updated record = chanD of original
                simp_all
              · exact hchanD_m
            exact ⟨hcur', hphase_m, hchanD'⟩
        | .sendAcquirePerm _ _ =>
            -- Shared unchanged, chanD at req unchanged
            rcases hstep with ⟨_, _, _, _, _, _, _, hs'_r⟩
            left; show p' ((e.drop k).drop (m + 1))
            simp only [p', state_pred, exec.drop]
            have hcur' : (e (k + m + 1)).shared.currentTxn = some tx := by
              rw [hs'_r]; exact hcur_m
            have hchanD' : ((e (k + m + 1)).locals req).chanD ≠ none := by
              rw [hs'_r]; simp only [SymState.locals, setFn]
              split
              · simp_all
              · exact hchanD_m
            exact ⟨hcur', hphase_m, hchanD'⟩
        | .recvAccessAckAtMaster =>
            rcases hstep with ⟨msg_r, hD_r, hop_r, hs'_r⟩
            by_cases hjr : j = req
            · -- j = req: accessAckNotRequesterInv says accessAck msg can't be at requester
              have hD_req : ((e (k + m)).locals req).chanD = some msg_r := by rw [← hjr]; exact hD_r
              have hinvm := always_livenessInv n e hspec (k + m)
              rcases hinvm with ⟨_, _, _, _, hnotreqm, _, _, _, _⟩
              exact absurd rfl (hnotreqm req msg_r hD_req hop_r tx hcur_m)
            · left; show p' ((e.drop k).drop (m + 1))
              simp only [p', state_pred, exec.drop]
              have hcur' : (e (k + m + 1)).shared.currentTxn = some tx := by
                rw [hs'_r]; exact hcur_m
              have hchanD' : ((e (k + m + 1)).locals req).chanD ≠ none := by
                rw [hs'_r]; simp only [SymState.locals, setFn]
                simp only [show (req = j) = False from propext ⟨fun h => hjr h.symm, False.elim⟩, ite_false]
                exact hchanD_m
              exact ⟨hcur', hphase_m, hchanD'⟩
      progress := by
        intro m hpm hnxt hact
        have hact' : actRecvGrantAtMaster n req (e (k + m)) (e (k + m + 1)) := hact
        rcases hact' with ⟨a, ha, hstep⟩; cases ha
        -- hstep : RecvGrantAtMaster (e (k+m)) (e (k+m+1)) req
        rcases hstep with ⟨tx_r, msg_r, hcur_r, hreq_r, hphase_r, _, _, hD_r, _, _, _, hs'_r⟩
        have hchanE' : ((e (k + m + 1)).locals req).chanE ≠ none := by
          rw [hs'_r]; simp [recvGrantState, recvGrantLocals, setFn, recvGrantLocal]
        show grantAckOnChanE n ((e.drop k).drop (m + 1))
        simp only [grantAckOnChanE, state_pred, exec.drop]
        exact ⟨req, hchanE'⟩
      enablement := by
        intro m hpm
        have hpm' := by simp only [p', state_pred, exec.drop] at hpm; exact hpm
        have hcur_m : (e (k + m)).shared.currentTxn = some tx := hpm'.1
        have hchanD_m : ((e (k + m)).locals req).chanD ≠ none := hpm'.2.2
        have hinvm := always_livenessInv n e hspec (k + m)
        rcases hinvm with ⟨hfullm, _, _, _, hnotreqm, _, _, hreqm, _⟩
        rcases hfullm with ⟨_, ⟨_, _, _, hchanDm, _⟩, _⟩
        -- From chanDInv at req: get the grant branch
        specialize hchanDm req
        match hD : ((e (k + m)).locals req).chanD with
        | none => exact absurd hD hchanD_m
        | some msg =>
          rw [hD] at hchanDm
          rcases hchanDm with ⟨tx_d, hcur_d, _, _, hga_d, hps_d, hEn_d, hmsg_d⟩ |
              ⟨hcurNone, _⟩ | ⟨hop_d, _⟩
          · -- Grant branch: all RecvGrant guards available
            rw [hcur_m] at hcur_d; cases hcur_d
            left; show ∃ s', actRecvGrantAtMaster n req (e (k + m)) s'
            refine ⟨recvGrantState (e (k + m)) req tx, .recvGrantAtMaster, rfl, ?_⟩
            simp only [tlMessages]
            refine ⟨tx, msg, hcur_m, rfl, hphase, hga_d, ?_, hD, hEn_d, hps_d, hmsg_d, rfl⟩
            -- chanA req = none from requesterChanAInv
            exact (hreqm tx hcur_m req rfl (Or.inr (Or.inr ⟨hphase, hchanD_m⟩))).1
          · rw [hcur_m] at hcurNone; simp at hcurNone
          · exfalso; exact hnotreqm req msg hD hop_d tx hcur_m rfl
      always_next := by
        intro m; exact hnext (k + m)
      fair := by
        intro m henabled
        rw [exec.drop_drop] at henabled
        have h := hwf (k + m) henabled
        rw [exec.drop_drop]; exact h
    }
  · -- chanE already non-none → grantAckOnChanE already holds
    exact ⟨0, by
      simp only [grantAckOnChanE, state_pred, exec.drop, Nat.add_zero]
      exact ⟨req, hchanE⟩⟩

/-- State-level safety: grantAckOnChanE is preserved or txnDone. -/
private theorem grantAckOnChanE_safety {n : Nat} (s s' : SymState HomeState NodeState n)
    (hce : ∃ i : Fin n, (s.locals i).chanE ≠ none) (hnxt : (tlMessages.toSpec n).next s s') :
    (∃ i : Fin n, (s'.locals i).chanE ≠ none) ∨ s'.shared.currentTxn = none := by
  rcases hce with ⟨i0, hchanE0⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnxt
  obtain ⟨j, a, hstep⟩ := hnxt
  match a with
  -- recvGrantAckAtManager: clears chanE and sets currentTxn = none
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      by_cases hij : i0 = j
      · right; simp [recvGrantAckState, recvGrantAckShared]
      · left; exact ⟨i0, by simp [recvGrantAckState, recvGrantAckLocals, setFn, hij, hchanE0]⟩
  -- recvGrantAtMaster: sets chanE at j; chanE at other nodes unchanged
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨j, by simp [recvGrantState, recvGrantLocals, setFn, recvGrantLocal]⟩
  -- All other actions: chanE unchanged for all nodes, currentTxn may or may not change
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by by_cases hij : i0 = j <;> simp_all [setFn]⟩
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by by_cases hij : i0 = j <;> simp_all [setFn]⟩
  | .recvAcquireAtManager =>
      rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
        left; refine ⟨i0, ?_⟩
        simp only [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanE]
        exact hchanE0
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        left; refine ⟨i0, ?_⟩
        simp only [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanE]
        exact hchanE0
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        simp only [recvProbeState, recvProbeLocals]
        by_cases hij : i0 = j
        · subst hij; simp [setFn, recvProbeLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        simp only [recvProbeAckState, recvProbeAckLocals]
        by_cases hij : i0 = j
        · subst hij; simp [setFn, recvProbeAckLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        simp only [sendGrantState, sendGrantLocals]
        by_cases hij : i0 = j
        · subst hij; simp [setFn, sendGrantLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .sendRelease _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        simp only [sendReleaseState, sendReleaseLocals]
        by_cases hij : i0 = j
        · subst hij; simp [setFn, sendReleaseLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .sendReleaseData _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        simp only [sendReleaseState, sendReleaseLocals]
        by_cases hij : i0 = j
        · subst hij; simp [setFn, sendReleaseLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        simp only [recvReleaseState, recvReleaseLocals]
        by_cases hij : i0 = j
        · subst hij; simp [setFn, recvReleaseLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        simp only [recvReleaseAckState, recvReleaseAckLocals]
        by_cases hij : i0 = j
        · subst hij; simp [setFn, recvReleaseAckLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .store _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        by_cases hij : i0 = j
        · subst hij; simp [setFn, storeLocal, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, hchanE0⟩
  | .uncachedGet _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        by_cases hij : i0 = j
        · subst hij; simp [setFn, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .uncachedPut _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        by_cases hij : i0 = j
        · subst hij; simp [setFn, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      left; exact ⟨i0, by
        by_cases hij : i0 = j
        · subst hij; simp [setFn, hchanE0]
        · simp [setFn, hij, hchanE0]⟩
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      left; exact ⟨i0, by
        by_cases hij : i0 = j
        · subst hij; simp [setFn, hchanE0]
        · simp [setFn, hij, hchanE0]⟩

/-- State-level progress: recvGrantAck clears the transaction. -/
private theorem recvGrantAck_progress {n : Nat} (i : Fin n)
    (s s' : SymState HomeState NodeState n)
    (hact : actRecvGrantAckAtManager n i s s') :
    s'.shared.currentTxn = none := by
  rcases hact with ⟨a, ha, hstep⟩; cases ha
  rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  simp [recvGrantAckState, recvGrantAckShared]

/-- State-level safety: chanE at a specific node is preserved or txnDone. -/
private theorem chanE_at_node_safety {n : Nat} (i0 : Fin n)
    (s s' : SymState HomeState NodeState n)
    (hce : (s.locals i0).chanE ≠ none) (hnxt : (tlMessages.toSpec n).next s s') :
    (s'.locals i0).chanE ≠ none ∨ s'.shared.currentTxn = none := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnxt
  obtain ⟨j, a, hstep⟩ := hnxt
  match a with
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      by_cases hij : i0 = j
      · right; simp [recvGrantAckState, recvGrantAckShared]
      · left; simp [recvGrantAckState, recvGrantAckLocals, setFn, hij, hce]
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      by_cases hij : i0 = j
      · left; subst hij; simp [recvGrantState, recvGrantLocals, setFn, recvGrantLocal]
      · left; simp [recvGrantState, recvGrantLocals, setFn, hij, hce]
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j <;> simp_all [setFn]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j <;> simp_all [setFn]
  | .recvAcquireAtManager =>
      rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
        left; simp only [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanE]; exact hce
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        left; simp only [recvAcquireState, recvAcquireLocals, scheduleProbeLocals_chanE]; exact hce
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [recvProbeState, recvProbeLocals, setFn, recvProbeLocal, hce]
      · simp [recvProbeState, recvProbeLocals, setFn, hij, hce]
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [recvProbeAckState, recvProbeAckLocals, setFn, recvProbeAckLocal, hce]
      · simp [recvProbeAckState, recvProbeAckLocals, setFn, hij, hce]
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [sendGrantState, sendGrantLocals, setFn, sendGrantLocal, hce]
      · simp [sendGrantState, sendGrantLocals, setFn, hij, hce]
  | .sendRelease _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [sendReleaseState, sendReleaseLocals, setFn, sendReleaseLocal, hce]
      · simp [sendReleaseState, sendReleaseLocals, setFn, hij, hce]
  | .sendReleaseData _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [sendReleaseState, sendReleaseLocals, setFn, sendReleaseLocal, hce]
      · simp [sendReleaseState, sendReleaseLocals, setFn, hij, hce]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [recvReleaseState, recvReleaseLocals, setFn, recvReleaseLocal, hce]
      · simp [recvReleaseState, recvReleaseLocals, setFn, hij, hce]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [recvReleaseAckState, recvReleaseAckLocals, setFn, recvReleaseAckLocal, hce]
      · simp [recvReleaseAckState, recvReleaseAckLocals, setFn, hij, hce]
  | .store _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [setFn, storeLocal, hce]
      · simp [setFn, hij, hce]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      left; exact hce
  | .uncachedGet _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j <;> simp_all [setFn]
  | .uncachedPut _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j <;> simp_all [setFn]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      left; by_cases hij : i0 = j <;> simp_all [setFn]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      left; by_cases hij : i0 = j
      · subst hij; simp [setFn, hce]
      · simp [setFn, hij, hce]

/-- Step 4b: The grantAck is received by the manager, completing the transaction.
    Fair action: recvGrantAckAtManager.
    Uses a specific-node predicate to track chanE at i0. -/
theorem grantAckSent_leads_to_txnComplete (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (grantAckOnChanE n) (txnDone n)) := by
  intro e hspec
  have hnext : always (action_pred (tlMessages.toSpec n).next) e := hspec.2.1
  intro k hp
  have hp' : (∃ i : Fin n, ((e k).locals i).chanE ≠ none) := by
    change state_pred _ (e.drop k) at hp
    simp only [state_pred, exec.drop, Nat.add_zero] at hp; exact hp
  rcases hp' with ⟨i0, hchanE0⟩
  have hwf := extract_wf_recvGrantAck i0 hspec
  -- Use a stronger predicate that pins chanE at i0 specifically
  let p' : pred (SymState HomeState NodeState n) :=
    state_pred (fun s => (s.locals i0).chanE ≠ none)
  have hp'_k : p' (e.drop k) := by
    simp only [p', state_pred, exec.drop, Nat.add_zero]; exact hchanE0
  suffices h : leads_to p' (txnDone n) (e.drop k) from by
    have := h 0 (exec.drop_zero _ ▸ hp'_k)
    rw [exec.drop_zero] at this; exact this
  apply wf1_apply (next := (tlMessages.toSpec n).next) (a := actRecvGrantAckAtManager n i0)
  exact {
    safety := by
      intro m hpm hnxt
      have hpm' : ((e (k + m)).locals i0).chanE ≠ none := by
        simp only [p', state_pred, exec.drop] at hpm; exact hpm
      have hnxt' : (tlMessages.toSpec n).next (e (k + m)) (e (k + m + 1)) := hnxt
      rcases chanE_at_node_safety i0 _ _ hpm' hnxt' with hce' | hdone
      · left; show p' ((e.drop k).drop (m + 1))
        simp only [p', state_pred, exec.drop]; exact hce'
      · right; show txnDone n ((e.drop k).drop (m + 1))
        simp only [txnDone, state_pred, exec.drop]; exact hdone
    progress := by
      intro m hpm hnxt hact
      have hact' : actRecvGrantAckAtManager n i0 (e (k + m)) (e (k + m + 1)) := hact
      have hdone := recvGrantAck_progress i0 _ _ hact'
      show txnDone n ((e.drop k).drop (m + 1))
      simp only [txnDone, state_pred, exec.drop]; exact hdone
    enablement := by
      intro m hpm
      have hpm' : ((e (k + m)).locals i0).chanE ≠ none := by
        simp only [p', state_pred, exec.drop] at hpm; exact hpm
      -- Use chanEInv to get all guards for recvGrantAckAtManager at i0
      have hinvm := always_livenessInv n e hspec (k + m)
      rcases hinvm with ⟨hfullm, _, _, _, _, _, _, _⟩
      rcases hfullm with ⟨⟨_, _, hpendingm, _⟩, ⟨_, _, _, _, hchanEm⟩, _⟩
      -- From chanEInv at i0: get tx, phase, guards
      specialize hchanEm i0
      match hE : ((e (k + m)).locals i0).chanE with
      | none => exact absurd hE hpm'
      | some msg =>
        rw [hE] at hchanEm
        rcases hchanEm with ⟨tx_m, hcur_m, hreq_m, hphase_m, hga_m, hps_m, hDn_m, hmsg_m⟩
        left; show ∃ s', actRecvGrantAckAtManager n i0 (e (k + m)) s'
        refine ⟨recvGrantAckState (e (k + m)) i0, .recvGrantAckAtManager, rfl, ?_⟩
        simp only [tlMessages]
        exact ⟨tx_m, msg, hcur_m, hreq_m, hphase_m, hga_m, hDn_m, hE, hps_m, hmsg_m, rfl⟩
    always_next := by
      intro m; exact hnext (k + m)
    fair := by
      intro m henabled
      rw [exec.drop_drop] at henabled
      have h := hwf (k + m) henabled
      rw [exec.drop_drop]; exact h
  }

/-! ### Composed chains -/

/-- The grant wave completes: grantReady ↝ txnDone.
    Chains steps 3, 4a, 4b via leads_to_trans. -/
theorem grantReady_leads_to_txnDone (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlGrantReady n) (txnDone n)) :=
  chain2 (grantReady_leads_to_grantPendingAck n)
    (chain2 (grantPendingAck_leads_to_grantAckSent n)
      (grantAckSent_leads_to_txnComplete n))

/-- From probing/grantReady to txnDone.
    Chains steps 2, 3, 4a, 4b. -/
theorem probingOrReady_leads_to_txnDone (n : Nat) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (probingOrReady n) (txnDone n)) :=
  chain2 (probing_leads_to_grantReady n) (grantReady_leads_to_txnDone n)

/-! ### Main composition -/

/-- txnActiveForI implies probingOrReady ∨ grantPendingAck.
    From txnCoreInv: phase ∈ {probing, grantReady, grantPendingAck}. -/
theorem txnActive_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (txnActiveForI n i) (txnDone n)) := by
  intro e hspec k hp
  change state_pred _ (e.drop k) at hp
  simp only [state_pred, exec.drop, Nat.add_zero] at hp
  rcases hp with ⟨tx, hcur, hreqi⟩
  -- Get invariant to determine the phase
  have hinv := always_livenessInv n e hspec k
  rcases hinv with ⟨⟨⟨_, _, _, htxnCore⟩, _, _⟩, _⟩
  rw [txnCoreInv, hcur] at htxnCore
  rcases htxnCore with ⟨_, hphaseIn, _, _, _, _, _, _⟩
  rcases hphaseIn with hprobe | hready | hpending
  · -- Phase = probing: probingOrReady holds
    have hpor : probingOrReady n (e.drop k) := by
      simp only [state_pred, exec.drop, Nat.add_zero, probingOrReady]
      exact ⟨tx, hcur, Or.inl hprobe⟩
    exact probingOrReady_leads_to_txnDone n e hspec k hpor
  · -- Phase = grantReady
    have hpor : probingOrReady n (e.drop k) := by
      simp only [state_pred, exec.drop, Nat.add_zero, probingOrReady]
      exact ⟨tx, hcur, Or.inr hready⟩
    exact probingOrReady_leads_to_txnDone n e hspec k hpor
  · -- Phase = grantPendingAck
    have hgpa : tlGrantPendingAck n (e.drop k) := by
      simp only [state_pred, exec.drop, Nat.add_zero, tlGrantPendingAck, grantPendingAck]
      exact ⟨tx, hcur, hpending⟩
    exact (chain2 (grantPendingAck_leads_to_grantAckSent n)
      (grantAckSent_leads_to_txnComplete n)) e hspec k hgpa

/-- Step 1: A pending acquire on chanA eventually reaches txnDone.
    When currentTxn = none, txnDone already holds.
    When currentTxn = some tx, that transaction eventually completes. -/
theorem chanA_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (chanAPending n i) (txnDone n)) := by
  intro e hspec k hp
  -- Case split on currentTxn at position k
  match hcur : (e k).shared.currentTxn with
  | some tx =>
    -- Any active transaction eventually completes.
    -- Extract requester bound from txnCoreInv.
    have hinv := always_livenessInv n e hspec k
    rcases hinv with ⟨⟨⟨_, _, _, htxnCore⟩, _, _⟩, _⟩
    rw [txnCoreInv, hcur] at htxnCore
    rcases htxnCore with ⟨hreqLt, _⟩
    let req : Fin n := ⟨tx.requester, hreqLt⟩
    have hta : txnActiveForI n req (e.drop k) := by
      simp only [txnActiveForI, state_pred, exec.drop, Nat.add_zero]
      exact ⟨tx, hcur, rfl⟩
    exact txnActive_leads_to_txnDone n req e hspec k hta
  | none =>
    -- currentTxn = none means txnDone already holds.
    exact ⟨0, by simp only [txnDone, state_pred, exec.drop, Nat.add_zero]; exact hcur⟩

/-- The full acquire wave completes under weak fairness.
    Every acquire request eventually leads to a completed transaction. -/
theorem acquire_leads_to_txnDone (n : Nat) (i : Fin n) :
    pred_implies (tlMessagesFair n).formula
      (leads_to (tlAcquirePending n i) (txnDone n)) := by
  intro e hspec k hp
  change state_pred (acquirePending n i) (e.drop k) at hp
  simp only [state_pred, exec.drop, Nat.add_zero, acquirePending] at hp
  rcases hp with hchanA | htxn
  · -- chanAPending: chanA ↝ txnDone directly
    have hca : chanAPending n i (e.drop k) := by
      simp only [chanAPending, state_pred, exec.drop, Nat.add_zero]; exact hchanA
    exact chanA_leads_to_txnDone n i e hspec k hca
  · -- txnActive: direct
    have hta : txnActiveForI n i (e.drop k) := by
      simp only [txnActiveForI, state_pred, exec.drop, Nat.add_zero]; exact htxn
    exact txnActive_leads_to_txnDone n i e hspec k hta

end TileLink.Messages.Liveness
