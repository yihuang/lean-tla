import Leslie.Examples.BindingCrusaderAgreement

set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

/-! # Binding Crusader Agreement — Liveness (milestones) -/

open TLA
namespace BindingCrusaderAgreement

variable (n f : Nat)

/-! ## Setup -/

def bca_action (input : Fin n → Bool) (a : Action n) : action (State n) :=
  (bca n f input).actions a |>.fires

def bca_fairness (input : Fin n → Bool) : pred (State n) :=
  fun e =>
    (∀ src dst t v, weak_fairness
      (fun s s' => isCorrect n s src ∧
        bca_action n f input (.send src dst t v) s s') e) ∧
    (∀ src dst t v, weak_fairness (bca_action n f input (.recv src dst t v)) e) ∧
    (∀ i v, weak_fairness (bca_action n f input (.decide i v)) e)

/-! ## Counting helpers -/

/-- Number of distinct senders from which `q` has received any init message. -/
def countAnyInitRecv (ls : LocalState n) : Nat :=
  ((List.finRange n).filter
    (fun p => ls.initRecv p false || ls.initRecv p true)).length

/-- Number of distinct *correct* senders from which `q` has received any
    init message. Stronger than `countAnyInitRecv`: it requires the
    sender itself to be correct at the current step. -/
def countCorrectInitRecv (s : State n) (q : Fin n) : Nat :=
  ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) &&
    ((s.local_ q).initRecv p false || (s.local_ q).initRecv p true))).length

/-! ## Persistence lemmas

    Each fact below is of the form "once `P` holds at step `k`, it holds
    at every later step `k + d`". Most are inductive consequences of the
    safety invariant or pure monotonicity of update functions. -/

/-- Corruption is monotone at the single-step level: `corrupted` only grows. -/
private theorem corrupted_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (p : Fin n) (h : p ∈ s.corrupted) : p ∈ s'.corrupted := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; exact List.mem_cons_of_mem j h
  | send src dst t mv => subst htrans ; exact h
  | recv src dst t mv => subst htrans ; exact h
  | decide i mv => subst htrans ; exact h

/-- Sent is monotone at the single-step level: once `sent d t w = true`,
    it remains true after any action. -/
private theorem sent_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (p : Fin n) (d : Fin n) (mt : MsgType) (w : Val)
    (h : (s.local_ p).sent d mt w = true) :
    (s'.local_ p).sent d mt w = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; exact h
  | send src' dst' t' mv =>
    subst htrans
    simp only
    by_cases hp : p = src'
    · subst hp ; simp
      by_cases hargs : d = dst' ∧ mt = t' ∧ w = mv
      · obtain ⟨rfl, rfl, rfl⟩ := hargs ; simp
      · simp [hargs] ; exact h
    · simp [hp] ; exact h
  | recv src' dst' t' mv =>
    subst htrans
    simp only
    by_cases hp : p = dst'
    · subst hp ; simp
      cases t' with
      | init =>
        cases mv with
        | none => exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ p).initRecv src' bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ p).echoRecv src' bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ p).voteRecv src' mv = false
        · rw [if_pos halready] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hp] ; exact h
  | decide j mv =>
    subst htrans
    simp only
    by_cases hp : p = j
    · subst hp ; simp ; exact h
    · simp [hp] ; exact h

/-- `sent` is monotone in time: once true, stays true. -/
theorem sent_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (p dst : Fin n) (t : MsgType) (v : Val) (k d : Nat) :
    ((exec.drop k e 0).local_ p).sent dst t v = true →
    ((exec.drop (k + d) e 0).local_ p).sent dst t v = true := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih ; rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega] ; exact h'
    exact sent_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' p dst t v ih

/-- After a send action fires, the corresponding `sent` flag is `true`. -/
private theorem sent_true_after_send (input : Fin n → Bool)
    (s s' : State n) (src dst : Fin n) (t : MsgType) (mv : Val)
    (hfire : ((bca n f input).actions (.send src dst t mv)).fires s s') :
    (s'.local_ src).sent dst t mv = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  subst htrans ; simp

/-- If `sent p d t w` goes from `false` to `true` in one step, then the
    action that fired was `send(p, d, t, w)` — and the send gate was open
    and the send transition produced the successor state. -/
private theorem sent_false_true_implies_send (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (p : Fin n) (d : Fin n) (mt : MsgType) (w : Val)
    (h_old : (s.local_ p).sent d mt w = false)
    (h_new : (s'.local_ p).sent d mt w = true) :
    ((bca n f input).actions (.send p d mt w)).gate s ∧
    ((bca n f input).actions (.send p d mt w)).fires s s' := by
  simp only [bca, GatedAction.fires] at hfire ⊢
  obtain ⟨hgate_i, htrans_i⟩ := hfire
  cases i with
  | corrupt j =>
    exfalso ; rw [htrans_i] at h_new
    exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
  | recv src' dst' t' mv =>
    exfalso ; rw [htrans_i] at h_new ; simp only at h_new
    by_cases hp : dst' = p
    · subst hp ; simp at h_new
      cases t' <;> (try cases mv) <;> simp at h_new <;>
        (try split at h_new <;> simp_all) <;>
        exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
    · simp [Ne.symm hp] at h_new
      exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
  | decide j mv =>
    exfalso ; rw [htrans_i] at h_new ; simp only at h_new
    by_cases hp : j = p
    · subst hp ; simp at h_new
      exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
    · simp [Ne.symm hp] at h_new
      exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
  | send src' dst' t' mv =>
    by_cases hsrc' : src' = p
    · subst hsrc'
      by_cases hargs : dst' = d ∧ t' = mt ∧ mv = w
      · obtain ⟨rfl, rfl, rfl⟩ := hargs
        exact ⟨hgate_i, hgate_i, htrans_i⟩
      · exfalso ; rw [htrans_i] at h_new ; simp only [ite_true] at h_new
        have hne : ¬(d = dst' ∧ mt = t' ∧ w = mv) := by
          intro ⟨h1, h2, h3⟩ ; exact hargs ⟨h1.symm, h2.symm, h3.symm⟩
        simp [hne] at h_new
        exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
    · exfalso ; rw [htrans_i] at h_new ; simp [Ne.symm hsrc'] at h_new
      exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)

/-- Corruption is monotone: once a process is not correct, it stays so. -/
theorem isCorrect_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (p : Fin n) (k d : Nat) :
    ¬isCorrect n (exec.drop k e 0) p →
    ¬isCorrect n (exec.drop (k + d) e 0) p := by
  intro h
  simp only [isCorrect, Classical.not_not] at h ⊢
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    have hnext := hsafety.2 (k + d')
    obtain ⟨i, hfire⟩ := hnext
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have : e (k + d' + 1) = e (k + d' + 1) := rfl
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact corrupted_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' p ih

/-- Contrapositive of `isCorrect_persist`: if `p` is correct at step
    `k + d`, it was already correct at step `k`. Useful for "rebase to
    earlier step" arguments in `hmono` and hdel callbacks. -/
theorem isCorrect_at_earlier (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (p : Fin n) (k d : Nat)
    (hlate : isCorrect n (exec.drop (k + d) e 0) p) :
    isCorrect n (exec.drop k e 0) p := by
  by_contra hnc
  exact isCorrect_persist n f input e hsafety p k d hnc hlate

/-- Single-step monotonicity of `initRecv`: no action ever clears an
    `initRecv` bit. -/
private theorem initRecv_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q p : Fin n) (b : Bool)
    (h : (s.local_ q).initRecv p b = true) :
    (s'.local_ q).initRecv p b = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; simpa using h
  | send src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = src
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = dst
    · subst hq
      simp
      cases t with
      | init =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready]
            dsimp only
            by_cases hpeq : p = src ∧ b = bv
            · simp [hpeq]
            · simp [hpeq] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide i mv =>
    subst htrans
    simp
    by_cases hq : q = i
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h

/-- `initRecv` is monotone in time: once received, stays received. -/
theorem initRecv_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q p : Fin n) (b : Bool) (k d : Nat) :
    ((exec.drop k e 0).local_ q).initRecv p b = true →
    ((exec.drop (k + d) e 0).local_ q).initRecv p b = true := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact initRecv_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' q p b ih

/-- Single-step monotonicity of `echoRecv`. -/
private theorem echoRecv_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q p : Fin n) (b : Bool)
    (h : (s.local_ q).echoRecv p b = true) :
    (s'.local_ q).echoRecv p b = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; simpa using h
  | send src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = src
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = dst
    · subst hq
      simp
      cases t with
      | init =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready]
            dsimp only
            by_cases hpeq : p = src ∧ b = bv
            · simp [hpeq]
            · simp [hpeq] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide i mv =>
    subst htrans
    simp
    by_cases hq : q = i
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h

/-- `echoRecv` is monotone in time: once received, stays received. -/
theorem echoRecv_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q p : Fin n) (b : Bool) (k d : Nat) :
    ((exec.drop k e 0).local_ q).echoRecv p b = true →
    ((exec.drop (k + d) e 0).local_ q).echoRecv p b = true := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact echoRecv_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' q p b ih

/-- Single-step monotonicity of `echoed`. -/
private theorem echoed_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q : Fin n) (b' : Bool)
    (h : (s.local_ q).echoed = some b') :
    (s'.local_ q).echoed = some b' := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨hgate, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; simpa using h
  | send src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = src
    · subst hq
      cases t with
      | init => simp ; exact h
      | echo =>
        cases mv with
        | some bv =>
          by_cases hc : q ∈ s.corrupted
          · simp [hc] ; exact h
          · -- From gate: correct q ∧ sent = false ∧ approved bv ∧
            -- (echoed = none ∨ echoed = some bv). h says echoed = some b',
            -- so by single-shot, b' = bv.
            have hcq : isCorrect n s q := by
              simp only [isCorrect] ; exact hc
            simp only [] at hgate
            rcases hgate with hcorr | ⟨_, _, _, hecho_ok⟩
            · exact absurd hcorr hc
            · rcases hecho_ok with hnone | hsome
              · rw [hnone] at h ; exact absurd h (by simp)
              · rw [hsome] at h
                injection h with hbv_eq
                subst hbv_eq
                simp [hc]
        | none =>
          -- echoed unchanged in the none case
          simp only [] at hgate
          rcases hgate with _ | ⟨_, _, hmv⟩
          all_goals (simp ; exact h)
      | vote => simp ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = dst
    · subst hq
      simp
      cases t with
      | init =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide i mv =>
    subst htrans
    simp
    by_cases hq : q = i
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h

/-- `echoed` is monotone in time: once set to `some b'`, stays so. -/
theorem echoed_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (b' : Bool) (k d : Nat) :
    ((exec.drop k e 0).local_ q).echoed = some b' →
    ((exec.drop (k + d) e 0).local_ q).echoed = some b' := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact echoed_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' q b' ih

/-- Single-step monotonicity of `approved`. -/
private theorem approved_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q : Fin n) (b : Bool)
    (h : (s.local_ q).approved b = true) :
    (s'.local_ q).approved b = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; simpa using h
  | send src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = src
    · subst hq
      cases t
      · simp ; exact h
      · simp ; exact h
      · simp ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = dst
    · subst hq
      simp
      cases t with
      | init =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready]
            dsimp only
            -- approved := fun w => if w = bv ∧ ... then true else (s.local_ q).approved w
            by_cases hcond : b = bv ∧
                approveThreshold n f ≤ countInitRecv n (s.local_ q) bv + 1
            · simp [hcond]
            · simp [hcond] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide i mv =>
    subst htrans
    simp
    by_cases hq : q = i
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h

/-- `approved b` is monotone in time: once approved, stays approved. -/
theorem approved_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (b : Bool) (k d : Nat) :
    ((exec.drop k e 0).local_ q).approved b = true →
    ((exec.drop (k + d) e 0).local_ q).approved b = true := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact approved_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' q b ih

/-- Single-step monotonicity of `voteRecv`. -/
private theorem voteRecv_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q p : Fin n) (v : Val)
    (h : (s.local_ q).voteRecv p v = true) :
    (s'.local_ q).voteRecv p v = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; simpa using h
  | send src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = src
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = dst
    · subst hq
      simp
      cases t with
      | init =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready]
          dsimp only
          by_cases hpeq : p = src ∧ v = mv
          · simp [hpeq]
          · simp [hpeq] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide i mv =>
    subst htrans
    simp
    by_cases hq : q = i
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h

/-- `voteRecv` is monotone in time: once received, stays received. -/
theorem voteRecv_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q p : Fin n) (v : Val) (k d : Nat) :
    ((exec.drop k e 0).local_ q).voteRecv p v = true →
    ((exec.drop (k + d) e 0).local_ q).voteRecv p v = true := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact voteRecv_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' q p v ih

/-- Single-step monotonicity of `decided`. -/
private theorem decided_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q : Fin n) (v : Val)
    (h : (s.local_ q).decided = some v) :
    (s'.local_ q).decided = some v := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨hgate, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; simpa using h
  | send src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = src
    · subst hq
      cases t
      · simp ; exact h
      · simp ; exact h
      · simp ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = dst
    · subst hq
      simp
      cases t with
      | init =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide i mv =>
    subst htrans
    simp only
    by_cases hq : q = i
    · -- Decide on q: gate requires decided = none, contradicts h.
      subst hq
      simp only at hgate
      obtain ⟨_, hdec_none, _⟩ := hgate
      rw [hdec_none] at h
      exact absurd h (by simp)
    · simp [hq] ; exact h

/-- `decided` is monotone in time: once set to `some v`, stays so. -/
theorem decided_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (v : Val) (k d : Nat) :
    ((exec.drop k e 0).local_ q).decided = some v →
    ((exec.drop (k + d) e 0).local_ q).decided = some v := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact decided_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' q v ih

/-- Single-step monotonicity of `voted`. -/
private theorem voted_step_mono (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q : Fin n) (v : Val)
    (h : (s.local_ q).voted v = true) :
    (s'.local_ q).voted v = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; simpa using h
  | send src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = src
    · subst hq
      cases t with
      | init => simp ; exact h
      | echo => simp ; exact h
      | vote =>
        simp
        by_cases hc : q ∈ s.corrupted
        · simp [hc] ; exact h
        · simp [hc]
          by_cases hvmv : v = mv
          · simp [hvmv]
          · simp [hvmv] ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans
    simp only
    by_cases hq : q = dst
    · subst hq
      simp
      cases t with
      | init =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => simp ; exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready] ; exact h
        · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide i mv =>
    subst htrans
    simp
    by_cases hq : q = i
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h

/-- `voted` is monotone in time: once `voted v = true`, stays true. -/
theorem voted_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (v : Val) (k d : Nat) :
    ((exec.drop k e 0).local_ q).voted v = true →
    ((exec.drop (k + d) e 0).local_ q).voted v = true := by
  intro h
  induction d with
  | zero => simpa using h
  | succ d' ih =>
    rw [show k + (d' + 1) = (k + d') + 1 from by omega]
    obtain ⟨i, hfire⟩ := hsafety.2 (k + d')
    simp only [exec.drop] at ih ⊢
    have heq1 : 0 + (k + d') = k + d' := by omega
    have heq2 : 0 + (k + d' + 1) = k + d' + 1 := by omega
    rw [heq1] at ih
    rw [heq2]
    have hfire' : ((bca n f input).actions i).fires (e (k + d')) (e (k + d' + 1)) := by
      have h' : ((bca n f input).actions i).fires (e (k + d')) (e (1 + (k + d'))) := by
        simpa [exec.drop] using hfire
      rw [show k + d' + 1 = 1 + (k + d') from by omega]
      exact h'
    exact voted_step_mono n f input (e (k + d')) (e (k + d' + 1)) i hfire' q v ih

/-- `countEchoRecv` is monotone in time. Follows from `echoRecv_persist`
    by `filter_length_mono`. -/
theorem countEchoRecv_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (b : Bool) (threshold : Nat) (k d : Nat) :
    countEchoRecv n ((exec.drop k e 0).local_ q) b ≥ threshold →
    countEchoRecv n ((exec.drop (k + d) e 0).local_ q) b ≥ threshold := by
  intro h
  unfold countEchoRecv at h ⊢
  have hmono : ((List.finRange n).filter
      (((exec.drop k e 0).local_ q).echoRecv · b)).length ≤
      ((List.finRange n).filter
      (((exec.drop (k + d) e 0).local_ q).echoRecv · b)).length := by
    apply filter_length_mono
    intro p hp
    exact echoRecv_persist n f input e hsafety q p b k d hp
  omega

/-- `countVoteRecv` is monotone in time. Follows from `voteRecv_persist`
    by `filter_length_mono`. -/
theorem countVoteRecv_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (v : Val) (threshold : Nat) (k d : Nat) :
    countVoteRecv n ((exec.drop k e 0).local_ q) v ≥ threshold →
    countVoteRecv n ((exec.drop (k + d) e 0).local_ q) v ≥ threshold := by
  intro h
  unfold countVoteRecv at h ⊢
  have hmono : ((List.finRange n).filter
      (((exec.drop k e 0).local_ q).voteRecv · v)).length ≤
      ((List.finRange n).filter
      (((exec.drop (k + d) e 0).local_ q).voteRecv · v)).length := by
    apply filter_length_mono
    intro p hp
    exact voteRecv_persist n f input e hsafety q p v k d hp
  omega

/-- `countAnyVoteRecv` is monotone in time. Follows from `voteRecv_persist`
    on each of the three vote values. -/
theorem countAnyVoteRecv_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (threshold : Nat) (k d : Nat) :
    countAnyVoteRecv n ((exec.drop k e 0).local_ q) ≥ threshold →
    countAnyVoteRecv n ((exec.drop (k + d) e 0).local_ q) ≥ threshold := by
  intro h
  unfold countAnyVoteRecv at h ⊢
  have hmono : ((List.finRange n).filter
      (fun p => ((exec.drop k e 0).local_ q).voteRecv p (some false) ||
                ((exec.drop k e 0).local_ q).voteRecv p (some true) ||
                ((exec.drop k e 0).local_ q).voteRecv p none)).length ≤
      ((List.finRange n).filter
      (fun p => ((exec.drop (k + d) e 0).local_ q).voteRecv p (some false) ||
                ((exec.drop (k + d) e 0).local_ q).voteRecv p (some true) ||
                ((exec.drop (k + d) e 0).local_ q).voteRecv p none)).length := by
    apply filter_length_mono
    intro p hp
    simp only [Bool.or_eq_true] at hp ⊢
    rcases hp with (hf | ht) | hn
    · left ; left ; exact voteRecv_persist n f input e hsafety q p (some false) k d hf
    · left ; right ; exact voteRecv_persist n f input e hsafety q p (some true) k d ht
    · right ; exact voteRecv_persist n f input e hsafety q p none k d hn
  omega

/-- `countInitRecv` is monotone in time. Follows from `initRecv_persist`
    by `filter_length_mono`. -/
theorem countInitRecv_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (q : Fin n) (b : Bool) (threshold : Nat) (k d : Nat) :
    countInitRecv n ((exec.drop k e 0).local_ q) b ≥ threshold →
    countInitRecv n ((exec.drop (k + d) e 0).local_ q) b ≥ threshold := by
  intro h
  unfold countInitRecv at h ⊢
  have hmono : ((List.finRange n).filter
      (((exec.drop k e 0).local_ q).initRecv · b)).length ≤
      ((List.finRange n).filter
      (((exec.drop (k + d) e 0).local_ q).initRecv · b)).length := by
    apply filter_length_mono
    intro p hp
    exact initRecv_persist n f input e hsafety q p b k d hp
  omega

/-! ## Safety lemmas

    State-relational safety facts, derived inductively from `bca_inv`
    (or sorried pending such a proof). Each claim is of the form "in
    every reachable state, some relationship between state fields
    holds". No time dependence here — for time-monotone claims see
    the Persistence and Gate persistence sections. -/

/-! ### Corruption budget -/

/-- Corruption budget: at every step, the corrupted set has size ≤ f.
    Derived from `bca_inv` (the safety invariant proven in BCA.lean). -/
theorem corruption_budget (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n)) (hsafety : (bca n f input).safety e) (k : Nat) :
    ((exec.drop k e 0).corrupted).length ≤ f := by
  have hinv := init_invariant
    (bca_inv_init n f input)
    (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
    e hsafety
  exact (hinv k).1

/-! ### Init safety -/

/-- Converse of the new `bca_inv` conjunct 11: if `approved b = true` at
    a correct process, then the init count for `b` has reached the
    approve threshold. Safety-style; sorried pending addition of a
    matching inductive conjunct to `bca_inv`. -/
theorem approved_implies_countInitRecv (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p : Fin n) (b : Bool)
    (happ : ((exec.drop k e 0).local_ p).approved b = true) :
    countInitRecv n ((exec.drop k e 0).local_ p) b ≥ approveThreshold n f := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p b,
      (s.local_ p).approved b = true →
      countInitRecv n (s.local_ p) b ≥ approveThreshold n f)
    (by -- hinit: approved = false initially.
      intro s ⟨hlocal, _, _, _⟩ p b happ
      rw [hlocal p] at happ ; exact absurd happ Bool.false_ne_true)
    (by -- hnext
      intro s s' hnext hinv_s p b happ_s'
      obtain ⟨i, hfire⟩ := hnext
      by_cases happ_s : (s.local_ p).approved b = true
      · -- Already approved at s. Count ≥ threshold at s by IH. Count monotone.
        have hcount_s := hinv_s p b happ_s
        -- countInitRecv is monotone: uses filter_length_mono + initRecv_step_mono.
        have hcount_mono : countInitRecv n (s.local_ p) b ≤ countInitRecv n (s'.local_ p) b := by
          unfold countInitRecv
          apply filter_length_mono
          intro x hx
          exact initRecv_step_mono n f input s s' i hfire p x b hx
        exact Nat.le_trans hcount_s hcount_mono
      · -- approved is new. Case-split on action to find what set it.
        simp only [bca, GatedAction.fires] at hfire
        obtain ⟨hg, ht⟩ := hfire
        cases i with
        | corrupt j => subst ht ; exact absurd happ_s' happ_s
        | send src' dst' t' mv =>
          -- send doesn't change approved.
          subst ht ; simp only at happ_s'
          by_cases hp : p = src'
          · subst hp ; simp at happ_s' ; exact absurd happ_s' happ_s
          · simp [hp] at happ_s' ; exact absurd happ_s' happ_s
        | recv src' dst' t' mv =>
          -- Save hfire before it's consumed.
          have hfire_recv : ((bca n f input).actions (.recv src' dst' t' mv)).fires s s' := by
            simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩
          -- recv for init may set approved when count crosses threshold.
          rw [ht] at happ_s' ; simp only at happ_s'
          by_cases hp : p = dst'
          · subst hp ; simp at happ_s'
            cases t' with
            | init =>
              cases mv with
              | some bv =>
                dsimp only at happ_s'
                by_cases halready : (s.local_ p).initRecv src' bv = false
                · rw [if_pos halready] at happ_s'
                  simp at happ_s'
                  by_cases hbv : b = bv
                  · subst hbv
                    rcases happ_s' with ⟨_, hthresh⟩ | hold
                    · -- Use filter_length_strict_mono.
                      -- First show initRecv src' b = true at s'.
                      have h_new_ir : (s'.local_ p).initRecv src' b = true := by
                        rw [ht] ; simp [halready]
                      unfold countInitRecv at hthresh ⊢
                      have hstrict := _root_.filter_length_strict_mono
                        (fun x => (s.local_ p).initRecv x b)
                        (fun x => (s'.local_ p).initRecv x b)
                        (fun x hx => initRecv_step_mono n f input s s' _ hfire_recv p x b hx)
                        src' halready h_new_ir
                      omega
                    · exact absurd hold happ_s
                  · rcases happ_s' with ⟨rfl, _⟩ | hold
                    · exact absurd rfl hbv
                    · exact absurd hold happ_s
                · rw [if_neg halready] at happ_s' ; exact absurd happ_s' happ_s
              | none => exact absurd happ_s' happ_s
            | echo =>
              cases mv <;> simp at happ_s' <;>
                (try split at happ_s' <;> simp_all) <;> exact absurd happ_s' happ_s
            | vote =>
              simp at happ_s'
              by_cases halready : (s.local_ p).voteRecv src' mv = false
              · rw [if_pos halready] at happ_s' ; exact absurd happ_s' happ_s
              · rw [if_neg halready] at happ_s' ; exact absurd happ_s' happ_s
          · simp [hp] at happ_s' ; exact absurd happ_s' happ_s
        | decide j mv =>
          subst ht ; simp only at happ_s'
          by_cases hp : p = j
          · subst hp ; simp at happ_s' ; exact absurd happ_s' happ_s
          · simp [hp] at happ_s' ; exact absurd happ_s' happ_s)
    e hsafety
  exact hinv k p b happ

/-- If `initRecv p s b` goes from `false` to `true` in one step, then
    the action was `recv(s, p, init, some b)` and the buffer had the entry. -/
private theorem initRecv_false_true_implies_recv (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (p src : Fin n) (b : Bool)
    (h_old : (s.local_ p).initRecv src b = false)
    (h_new : (s'.local_ p).initRecv src b = true) :
    s.buffer ⟨src, p, .init, some b⟩ = true := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨hg, ht⟩ := hfire
  cases i with
  | corrupt j => subst ht ; exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
  | send src' dst' t' mv =>
    subst ht ; simp only at h_new
    by_cases hp : p = src'
    · subst hp ; simp at h_new ; exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
    · simp [hp] at h_new ; exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
  | recv src' dst' t' mv =>
    subst ht ; simp only at h_new
    by_cases hp : p = dst'
    · subst hp ; simp at h_new
      cases t' with
      | init =>
        cases mv with
        | some bv =>
          dsimp only at h_new
          by_cases hal : (s.local_ p).initRecv src' bv = false
          · rw [if_pos hal] at h_new
            -- h_new : (decide (src = src') && decide (b = bv) || old) = true.
            -- If src = src' ∧ b = bv: this is the matching recv. Gate gives buffer.
            -- Otherwise: old = true, contradicting h_old.
            by_cases hmatch : src = src' ∧ b = bv
            · obtain ⟨rfl, rfl⟩ := hmatch ; exact hg
            · -- ¬match: the new entry doesn't affect (src, b). So old = true.
              simp only at h_new
              have hne : decide (src = src') && decide (b = bv) = false := by
                cases hdp : decide (src = src') <;> cases hdv : decide (b = bv) <;> simp_all
              simp_all
          · rw [if_neg hal] at h_new
            exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
        | none => exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
      | echo =>
        cases mv <;> simp at h_new <;>
          (try split at h_new <;> simp_all) <;>
          exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
      | vote =>
        simp at h_new
        by_cases hal : (s.local_ p).voteRecv src' mv = false
        · rw [if_pos hal] at h_new
          exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
        · rw [if_neg hal] at h_new
          exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
    · simp [hp] at h_new ; exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
  | decide j mv =>
    subst ht ; simp only at h_new
    by_cases hp : p = j
    · subst hp ; simp at h_new ; exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)
    · simp [hp] at h_new ; exact absurd h_new (by rw [h_old] ; exact Bool.false_ne_true)

/-- **Honest-cond witness**: if a correct process `s` appears in some peer
    `p`'s `initRecv` for value `b`, then the *honest condition* of `s`'s
    init-send gate for `b` holds — namely `input s = b` or the amplify
    threshold has been reached at `s`. This is weaker than "the full send
    gate is enabled" because the gate additionally requires `sent = false`
    for the specific destination, which does *not* follow from having
    been received somewhere. Clients that previously called a stronger
    form now case-split on `sent` themselves. -/
theorem correct_initRecv_implies_honest_cond (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (s p : Fin n) (b : Bool)
    (hcs : isCorrect n (exec.drop k e 0) s)
    (hir : ((exec.drop k e 0).local_ p).initRecv s b = true) :
    input s = b ∨ countInitRecv n ((exec.drop k e 0).local_ s) b ≥ amplifyThreshold f := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun state =>
      (∀ s p b, isCorrect n state s → (state.local_ p).initRecv s b = true →
        input s = b ∨ countInitRecv n (state.local_ s) b ≥ amplifyThreshold f) ∧
      (∀ s dst b, isCorrect n state s → state.buffer ⟨s, dst, .init, some b⟩ = true →
        input s = b ∨ countInitRecv n (state.local_ s) b ≥ amplifyThreshold f))
    (by -- hinit: all false initially.
      intro state ⟨hlocal, hbuf, _, _⟩
      exact ⟨fun s p b _ hir => by rw [hlocal p] at hir ; exact absurd hir Bool.false_ne_true,
             fun s dst b _ hb => by rw [hbuf] at hb ; exact absurd hb Bool.false_ne_true⟩)
    (by -- hnext
      intro state state' hnext ⟨hinv_ir, hinv_buf⟩
      obtain ⟨i, hfire⟩ := hnext
      constructor
      · -- initRecv trace.
        intro s p b hcs' hir'
        have hcs : isCorrect n state s :=
          fun hmem => hcs' (corrupted_step_mono n f input state state' i hfire s hmem)
        by_cases hir_old : (state.local_ p).initRecv s b = true
        · -- Old initRecv. By IH, condition held at state. countInitRecv monotone.
          rcases hinv_ir s p b hcs hir_old with hinput | hcount
          · exact Or.inl hinput
          · exact Or.inr (Nat.le_trans hcount (by
              unfold countInitRecv ; apply filter_length_mono
              intro x hx ; exact initRecv_step_mono n f input state state' i hfire s x b hx))
        · -- New initRecv. By initRecv_false_true_implies_recv, buffer had the entry.
          have hir_false : (state.local_ p).initRecv s b = false := by
            cases hv : (state.local_ p).initRecv s b
            · rfl
            · exact absurd hv hir_old
          have hbuf := initRecv_false_true_implies_recv n f input state state' i
            (by exact hfire) p s b hir_false hir'
          -- By hinv_buf, condition at state. countInitRecv monotone.
          rcases hinv_buf s p b hcs hbuf with hinput | hcount
          · exact Or.inl hinput
          · exact Or.inr (Nat.le_trans hcount (by
              unfold countInitRecv ; apply filter_length_mono
              intro x hx ; exact initRecv_step_mono n f input state state' i hfire s x b hx))
      · -- Buffer trace.
        intro s dst b hcs' hbuf'
        have hcs : isCorrect n state s :=
          fun hmem => hcs' (corrupted_step_mono n f input state state' i hfire s hmem)
        by_cases hbuf_old : state.buffer ⟨s, dst, .init, some b⟩ = true
        · -- Old buffer. By IH, condition held at state. countInitRecv monotone.
          rcases hinv_buf s dst b hcs hbuf_old with hinput | hcount
          · exact Or.inl hinput
          · exact Or.inr (Nat.le_trans hcount (by
              unfold countInitRecv ; apply filter_length_mono
              intro x hx ; exact initRecv_step_mono n f input state state' i hfire s x b hx))
        · -- New buffer entry. Use sent_false_true_implies_send pattern for buffer.
          -- The action must be send(s, dst, init, some b).
          have hfire_saved := hfire
          simp only [bca, GatedAction.fires] at hfire
          obtain ⟨hg, ht⟩ := hfire
          cases i with
          | corrupt j => subst ht ; exact absurd hbuf' hbuf_old
          | send src' dst' t' mv =>
            by_cases hmsg : (⟨s, dst, .init, some b⟩ : Message n) = ⟨src', dst', t', mv⟩
            · have := Message.mk.inj hmsg
              obtain ⟨rfl, rfl, rfl, rfl⟩ := this
              rcases hg with hcor | ⟨_, _, hcond⟩
              · exact absurd hcor hcs
              · -- hcond : input s = b ∨ countInitRecv ≥ amplifyThreshold.
                -- countInitRecv monotone ⟹ persists to state'.
                rcases hcond with hinput | hcount
                · exact Or.inl hinput
                · exact Or.inr (Nat.le_trans hcount (by
                    unfold countInitRecv ; apply filter_length_mono
                    intro x hx
                    exact initRecv_step_mono n f input state state' (.send s dst .init (some b))
                      hfire_saved s x b hx))
            · subst ht ; simp [hmsg] at hbuf' ; exact absurd hbuf' hbuf_old
          | recv src' dst' t' mv =>
            by_cases hmsg : (⟨s, dst, .init, some b⟩ : Message n) = ⟨src', dst', t', mv⟩
            · subst ht ; simp [hmsg] at hbuf'
            · subst ht ; simp [hmsg] at hbuf' ; exact absurd hbuf' hbuf_old
          | decide j mv => subst ht ; exact absurd hbuf' hbuf_old)
    e hsafety
  exact (hinv k).1 s p b hcs hir

/-- Gate of `send p q .init (some (input p))` is enabled as long as `p`
    has not yet fired the specific send: the honest condition `input p =
    input p` is trivially true, and if `p` is corrupt the `corrupted`
    disjunct of the gate fires. -/
theorem init_send_gate_trivial (input : Fin n → Bool) (p q : Fin n) (s : State n)
    (hsent_false : (s.local_ p).sent q .init (some (input p)) = false) :
    ((bca n f input).actions (.send p q .init (some (input p)))).gate s := by
  by_cases hcp : isCorrect n s p
  · exact Or.inr ⟨hcp, hsent_false, Or.inl rfl⟩
  · exact Or.inl (by simpa [isCorrect] using hcp)

/-- Gate of `send p q .init (some b)` is enabled when `p`'s init count for
    `b` has crossed the amplify threshold (and `p` has not yet fired the
    specific send). -/
theorem init_send_gate_amplify (input : Fin n → Bool) (p q : Fin n) (b : Bool)
    (s : State n)
    (hsent_false : (s.local_ p).sent q .init (some b) = false)
    (hcount : countInitRecv n (s.local_ p) b ≥ f + 1) :
    ((bca n f input).actions (.send p q .init (some b))).gate s := by
  by_cases hcp : isCorrect n s p
  · exact Or.inr ⟨hcp, hsent_false, Or.inr hcount⟩
  · exact Or.inl (by simpa [isCorrect] using hcp)

/-- Init message tracking: if `p` has the `sent` flag for `init(b) → q`,
    then either the message is in the buffer or `q` has already recorded
    it. (Inductive safety invariant on `bca`.) -/
theorem init_msg_tracking (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p q : Fin n) (b : Bool) :
    ((exec.drop k e 0).local_ p).sent q .init (some b) = true →
    (exec.drop k e 0).buffer ⟨p, q, .init, some b⟩ = true ∨
    ((exec.drop k e 0).local_ q).initRecv p b = true := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p q b,
      (s.local_ p).sent q .init (some b) = true →
      s.buffer ⟨p, q, .init, some b⟩ = true ∨ (s.local_ q).initRecv p b = true)
    (by intro s ⟨hlocal, _, _, _⟩ p q b hsent
        rw [hlocal p] at hsent ; exact absurd hsent Bool.false_ne_true)
    (by intro s s' hnext hinv_s p q b hsent_s'
        obtain ⟨i, hfire⟩ := hnext
        by_cases hsent_s : (s.local_ p).sent q .init (some b) = true
        · -- sent was true at s. By IH: buffer ∨ initRecv at s.
          rcases hinv_s p q b hsent_s with hbuf | hrcv
          · -- buffer at s. Check if still in buffer at s'.
            by_cases hbuf_s' : s'.buffer ⟨p, q, .init, some b⟩ = true
            · exact Or.inl hbuf_s'
            · -- buffer cleared. The action must be recv(p, q, init, some b).
              -- recv sets initRecv. Use initRecv_step_mono or direct analysis.
              -- Actually, buffer went true→false. The recv that cleared it set initRecv.
              -- But we need initRecv at s', not just "some recv fired".
              -- Use init_buffer_cleared with d = 0... no, that's circular.
              -- Case-split on the action.
              simp only [bca, GatedAction.fires] at hfire
              obtain ⟨hg, ht⟩ := hfire
              cases i with
              | corrupt j => subst ht ; simp_all
              | send src' dst' t' mv =>
                -- send adds ⟨src', dst', t', mv⟩ to buffer. For our msg, either matches or old.
                by_cases hmsg : (⟨p, q, .init, some b⟩ : Message n) = ⟨src', dst', t', mv⟩
                · -- Matching: buffer set to true. But hbuf_s' says not true. Contradiction.
                  have := Message.mk.inj hmsg
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := this
                  subst ht ; simp at hbuf_s'
                · -- Different msg: buffer unchanged. Old was true, contradiction.
                  subst ht ; simp [hmsg] at hbuf_s'
                  rw [hbuf] at hbuf_s' ; simp at hbuf_s'
              | recv src' dst' t' mv =>
                by_cases hmsg : (⟨p, q, .init, some b⟩ : Message n) = ⟨src', dst', t', mv⟩
                · -- Matching recv: clears buffer, sets initRecv.
                  have := Message.mk.inj hmsg
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := this
                  right ; subst ht ; simp
                  -- Goal: initRecv in recv-modified state. Split on whether already received.
                  by_cases halready : (s.local_ q).initRecv p b = false
                  · rw [if_pos halready] ; simp
                  · rw [if_neg halready]
                    cases hv : (s.local_ q).initRecv p b
                    · exact absurd hv halready
                    · exact rfl
                · -- Different recv. Buffer unchanged. Contradiction.
                  subst ht
                  simp [hmsg] at hbuf_s'
                  simp_all
              | decide j mv => subst ht ; simp_all
          · -- initRecv at s. Persists.
            exact Or.inr (initRecv_step_mono n f input s s' i hfire q p b hrcv)
        · -- sent is new. By sent_false_true_implies_send, action was send(p, q, init, some b).
          have hsent_false : (s.local_ p).sent q .init (some b) = false := by
            cases hv : (s.local_ p).sent q .init (some b)
            · rfl
            · exact absurd hv hsent_s
          obtain ⟨_, hfires_send⟩ :=
            sent_false_true_implies_send n f input s s' i hfire p q .init (some b) hsent_false hsent_s'
          -- The transition sets buffer ⟨p, q, init, some b⟩ = true.
          simp only [bca, GatedAction.fires] at hfires_send
          obtain ⟨_, ht⟩ := hfires_send
          left ; subst ht ; simp)
    e hsafety
  exact hinv k p q b

/-- If a message is in the buffer, the sender's sent flag is true.
    Independent inductive invariant: send sets both simultaneously,
    recv clears buffer but doesn't clear sent. -/
theorem buffer_implies_sent (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p dst : Fin n) (t : MsgType) (v : Val) :
    (exec.drop k e 0).buffer ⟨p, dst, t, v⟩ = true →
    ((exec.drop k e 0).local_ p).sent dst t v = true := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p dst t v,
      s.buffer ⟨p, dst, t, v⟩ = true → (s.local_ p).sent dst t v = true)
    (by -- hinit: buffer all false initially.
      intro s ⟨_, hbuf, _, _⟩ p dst t v hb
      rw [hbuf] at hb ; exact absurd hb Bool.false_ne_true)
    (by -- hnext
      intro s s' hnext hinv_s p dst t v hbuf_s'
      obtain ⟨i, hfire⟩ := hnext
      -- Was buffer already true at s?
      by_cases hbuf_s : s.buffer ⟨p, dst, t, v⟩ = true
      · -- Old buffer entry. sent was true at s by IH. Persist.
        exact sent_step_mono n f input s s' i hfire p dst t v (hinv_s p dst t v hbuf_s)
      · -- New buffer entry. Case-split on action.
        simp only [bca, GatedAction.fires] at hfire
        obtain ⟨hg, ht⟩ := hfire
        cases i with
        | corrupt j => subst ht ; exact absurd hbuf_s' hbuf_s
        | send src' dst' t' mv =>
          -- send sets buffer ⟨src', dst', t', mv⟩ = true.
          by_cases hmsg : (⟨p, dst, t, v⟩ : Message n) = ⟨src', dst', t', mv⟩
          · -- Matching: p = src', dst = dst', t = t', v = mv.
            have := Message.mk.inj hmsg
            obtain ⟨rfl, rfl, rfl, rfl⟩ := this
            -- send also sets sent dst t v = true.
            exact sent_true_after_send n f input s s' p dst t v
              (by simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩)
          · -- Different message: buffer unchanged. Contradiction.
            subst ht ; simp [hmsg] at hbuf_s' ; exact absurd hbuf_s' hbuf_s
        | recv src' dst' t' mv =>
          -- recv clears buffer, never creates entries (except for the message it processes).
          -- Actually recv sets buffer to false for the matching msg, and doesn't change others.
          by_cases hmsg : (⟨p, dst, t, v⟩ : Message n) = ⟨src', dst', t', mv⟩
          · -- Matching recv: buffer set to false, not true. Contradiction.
            subst ht ; simp [hmsg] at hbuf_s'
          · subst ht ; simp [hmsg] at hbuf_s' ; exact absurd hbuf_s' hbuf_s
        | decide j mv => subst ht ; exact absurd hbuf_s' hbuf_s)
    e hsafety
  exact hinv k p dst t v

/-- Init buffer-clear: if `init(b)` was in the buffer at step `k`
    and is no longer at step `k+d`, then `q` has recorded it. -/
theorem init_buffer_cleared (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (p q : Fin n) (b : Bool) (k d : Nat) :
    (exec.drop k e 0).buffer ⟨p, q, .init, some b⟩ = true →
    (exec.drop (k + d) e 0).buffer ⟨p, q, .init, some b⟩ = false →
    ((exec.drop (k + d) e 0).local_ q).initRecv p b = true := by
  intro hbuf_k hbuf_kd
  -- buffer at k → sent at k. Persist sent to k+d. Msg tracking at k+d: buffer ∨ received.
  have hsent_k := buffer_implies_sent n f input e hsafety k p q .init (some b) hbuf_k
  have hsent_kd := sent_persist n f input e hsafety p q .init (some b) k d hsent_k
  rcases init_msg_tracking n f input e hsafety (k + d) p q b hsent_kd with hbuf | hrcv
  · exact absurd hbuf (by rw [hbuf_kd] ; exact Bool.false_ne_true)
  · exact hrcv

/-! ### Echo safety -/

/-- Safety corollary of `bca_inv` conjunct 2 (echo trace): if a correct
    process `p` shows up in any peer's `echoRecv` for value `b`, then
    `p.echoed = some b`. Pulls the conjunct out via `init_invariant`. -/
theorem echoed_from_echoRecv (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p q : Fin n) (b : Bool)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (her : ((exec.drop k e 0).local_ q).echoRecv p b = true) :
    ((exec.drop k e 0).local_ p).echoed = some b := by
  have hinv := init_invariant
    (bca_inv_init n f input)
    (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
    e hsafety
  obtain ⟨_, hetrace, _, _, _, _, _, _, _, _, _, _⟩ := hinv k
  exact hetrace p q b hcp her

/-- A correct process that has committed to an echo value has also
    approved that value. Inductive invariant (echoed only set by the
    echo send, whose gate requires approved). -/
theorem echoed_implies_approved (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p : Fin n) (b' : Bool)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hecho : ((exec.drop k e 0).local_ p).echoed = some b') :
    ((exec.drop k e 0).local_ p).approved b' = true := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p b, isCorrect n s p →
      (s.local_ p).echoed = some b → (s.local_ p).approved b = true)
    (by intro s ⟨hlocal, _, _, _⟩ p b _ hecho
        rw [hlocal p] at hecho ; exact absurd hecho (by simp [LocalState.init]))
    (by -- hnext: if echoed = some b at s' and p correct, then approved b at s'.
        -- Either echoed was already some b (IH + approved_step_mono) or it
        -- changed (only via echo send whose gate requires approved b).
        intro s s' hnext hinv_s p b hcp_s' hecho_s'
        obtain ⟨i, hfire⟩ := hnext
        have hcp_s : isCorrect n s p :=
          fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
        by_cases hecho_s : (s.local_ p).echoed = some b
        · exact approved_step_mono n f input s s' i hfire p b (hinv_s p b hcp_s hecho_s)
        · -- echoed changed. Case-split on the action to find what changed it.
          simp only [bca, GatedAction.fires] at hfire
          obtain ⟨hg, ht⟩ := hfire
          cases i with
          | corrupt j => subst ht ; exact absurd hecho_s' hecho_s
          | send src' dst' t' mv =>
            -- echoed changed via send. Only echo send from correct p does this.
            -- Use sent_false_true_implies_send pattern at state level.
            -- The gate for send(p, _, echo, some b) requires approved b.
            -- Reconstruct fires to use approved_step_mono.
            have hfires_i : ((bca n f input).actions (.send src' dst' t' mv)).fires s s' := by
              simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩
            rw [ht] at hecho_s' ; simp only at hecho_s'
            by_cases hp : p = src'
            · subst hp ; simp at hecho_s'
              cases t' with
              | echo =>
                cases mv with
                | some bv =>
                  simp only [isCorrect] at hcp_s ; simp [hcp_s] at hecho_s'
                  -- hecho_s' : bv = b. Rewrite goal.
                  rw [← hecho_s']
                  have hfires_p := hfires_i
                  simp only [bca, GatedAction.fires] at hfires_i
                  obtain ⟨hg', _⟩ := hfires_i
                  rcases hg' with hcor | ⟨_, _, happ, _⟩
                  · exact absurd hcor hcp_s
                  · exact approved_step_mono n f input s s'
                      (.send p dst' .echo (some bv)) hfires_p p bv happ
                | none =>
                  simp only [bca, GatedAction.fires] at hfires_i
                  obtain ⟨hg', _⟩ := hfires_i
                  rcases hg' with hcor | ⟨_, _, hfalse⟩
                  · exact absurd hcor hcp_s
                  · exact hfalse.elim
              | init => exact absurd hecho_s' hecho_s
              | vote => exact absurd hecho_s' hecho_s
            · simp [hp] at hecho_s' ; exact absurd hecho_s' hecho_s
          | recv src' dst' t' mv =>
            subst ht ; simp only at hecho_s'
            by_cases hp : dst' = p
            · subst hp ; simp at hecho_s'
              cases t' <;> (try cases mv) <;> simp at hecho_s' <;>
                (try split at hecho_s' <;> simp_all) <;> exact absurd hecho_s' hecho_s
            · simp [Ne.symm hp] at hecho_s' ; exact absurd hecho_s' hecho_s
          | decide j mv =>
            subst ht ; simp only at hecho_s'
            by_cases hp : j = p
            · subst hp ; simp at hecho_s' ; exact absurd hecho_s' hecho_s
            · simp [Ne.symm hp] at hecho_s' ; exact absurd hecho_s' hecho_s)
    e hsafety
  exact hinv k p b' hcp hecho

/-- Echo send gate from approved + echoed: if `p` is correct, has
    approved `b`, `echoed = none ∨ echoed = some b`, and has not yet
    sent the specific message, then the echo send gate holds. -/
theorem echo_send_gate_from_approved (input : Fin n → Bool)
    (p r : Fin n) (b : Bool) (s : State n)
    (hcp : isCorrect n s p)
    (hsent_false : (s.local_ p).sent r .echo (some b) = false)
    (happ : (s.local_ p).approved b = true)
    (hecho_ok : (s.local_ p).echoed = none ∨ (s.local_ p).echoed = some b) :
    ((bca n f input).actions (.send p r .echo (some b))).gate s := by
  exact Or.inr ⟨hcp, hsent_false, happ, hecho_ok⟩

/-- A correct process that has sent an echo must have committed `echoed`.
    If `sent dst echo (some b) = true` and the process is correct, then
    `echoed = some b`. Consequence of the BCA safety invariant: the send
    transition for echo atomically sets both `sent` and `echoed`. -/
theorem sent_echo_implies_echoed (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p dst : Fin n) (b : Bool)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hsent : ((exec.drop k e 0).local_ p).sent dst .echo (some b) = true) :
    ((exec.drop k e 0).local_ p).echoed = some b := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p dst b, isCorrect n s p →
      (s.local_ p).sent dst .echo (some b) = true → (s.local_ p).echoed = some b)
    (by -- hinit: init state has all sent = false.
      intro s ⟨hlocal, _, _, _⟩ p dst b _ hsent
      rw [hlocal p] at hsent ; exact absurd hsent Bool.false_ne_true)
    (by -- hnext
      intro s s' hnext hinv_s p dst b hcp_s' hsent_s'
      obtain ⟨i, hfire⟩ := hnext
      have hcp_s : isCorrect n s p :=
        fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
      -- Did sent go from false to true (new) or was it already true (old)?
      by_cases hsent_s : (s.local_ p).sent dst .echo (some b) = true
      · -- Already sent at s. By IH, echoed = some b at s.
        have hecho_s : (s.local_ p).echoed = some b := by
          exact hinv_s p dst b hcp_s hsent_s
        -- echoed at s' is either unchanged or set to some b' by an echo send.
        -- Use echoed_step_mono: echoed = some b at s → echoed = some b at s'.
        exact echoed_step_mono n f input s s' i hfire p b hecho_s
      · -- sent was false at s, true at s'. By sent_false_true_implies_send,
        -- the action was send(p, dst, echo, some b) and its gate was open.
        have hsent_false : (s.local_ p).sent dst .echo (some b) = false := by
          cases hv : (s.local_ p).sent dst .echo (some b)
          · rfl
          · exact absurd hv hsent_s
        obtain ⟨hgate, hfires_send⟩ :=
          sent_false_true_implies_send n f input s s' i hfire p dst .echo (some b)
            hsent_false hsent_s'
        -- The transition for send(p, dst, echo, some b) sets echoed = some b (for correct p).
        simp only [bca, GatedAction.fires] at hfires_send
        obtain ⟨_, ht⟩ := hfires_send
        have : (s'.local_ p).echoed = some b := by
          subst ht ; simp only [ite_true]
          simp only [isCorrect] at hcp_s ; simp [hcp_s]
        exact this)
    e hsafety
  exact hinv k p dst b hcp hsent

/-- A correct process never has `sent dst echo none = true`. The echo gate's
    correct disjunct requires `match mv with | some b => ... | none => False`,
    so only corrupt processes can send echo(none). -/
theorem sent_echo_none_false_correct (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p dst : Fin n)
    (hcp : isCorrect n (exec.drop k e 0) p) :
    ((exec.drop k e 0).local_ p).sent dst .echo none = false := by
  -- Use init_invariant with inv = "∀ p dst, correct p → sent dst echo none = false".
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p dst, isCorrect n s p → (s.local_ p).sent dst .echo none = false)
    (by -- hinit: init → inv
      intro s ⟨hlocal, _, _, _⟩ p dst _
      rw [hlocal p] ; rfl)
    (by -- hnext: next s s' → inv s → inv s'
      intro s s' hnext hinv_s p dst hcp_s'
      obtain ⟨i, hfire⟩ := hnext
      -- If sent was true at s', sent_false_true_implies_send gives the action.
      by_contra h
      have hsent_true : (s'.local_ p).sent dst .echo none = true := by
        cases hv : (s'.local_ p).sent dst .echo none
        · exact absurd hv h
        · rfl
      -- p was correct at s (corruption monotone: correct at s' → correct at s).
      have hcp_s : isCorrect n s p :=
        fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
      have hsent_false := hinv_s p dst hcp_s
      -- sent went false→true. By sent_false_true_implies_send, the action was
      -- send(p, dst, echo, none) and its gate was open.
      obtain ⟨hgate, _⟩ :=
        sent_false_true_implies_send n f input s s' i hfire p dst .echo none hsent_false hsent_true
      -- Gate = p ∈ corrupted ∨ (isCorrect ∧ ... ∧ False). Since p correct, False.
      rcases hgate with hcor | ⟨_, _, hfalse⟩
      · exact hcp_s hcor
      · exact hfalse)
    e hsafety
  exact hinv k p dst hcp

/-- No `echo none` message from a correct source is ever in the buffer. -/
theorem buffer_echo_none_false_correct (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p dst : Fin n)
    (hcp : isCorrect n (exec.drop k e 0) p) :
    (exec.drop k e 0).buffer ⟨p, dst, .echo, none⟩ = false := by
  -- Same approach: init_invariant with inv = "correct p → buffer echo none = false".
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p dst, isCorrect n s p → s.buffer ⟨p, dst, .echo, none⟩ = false)
    (by -- hinit
      intro s ⟨_, hbuf, _, _⟩ p dst _
      exact hbuf _)
    (by -- hnext: the only action that adds to buffer is send.
      -- send(p, dst, echo, none) gate is closed for correct p.
      intro s s' hnext hinv_s p dst hcp_s'
      obtain ⟨i, hfire⟩ := hnext
      by_contra h
      have hbuf_true : s'.buffer ⟨p, dst, .echo, none⟩ = true := by
        cases hv : s'.buffer ⟨p, dst, .echo, none⟩
        · exact absurd hv h
        · rfl
      have hcp_s : isCorrect n s p :=
        fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
      have hbuf_false := hinv_s p dst hcp_s
      -- buffer went false→true. The only action that sets buffer ⟨p, dst, echo, none⟩
      -- to true is send(p, dst, echo, none). Its gate is closed for correct p.
      -- Case-split on i to find which action changed the buffer.
      simp only [bca, GatedAction.fires] at hfire
      obtain ⟨hg, ht⟩ := hfire
      cases i with
      | corrupt j => rw [ht] at hbuf_true ; rw [hbuf_false] at hbuf_true ; exact absurd hbuf_true Bool.false_ne_true
      | send src' dst' t' mv =>
        rw [ht] at hbuf_true ; simp only at hbuf_true
        -- buffer update: if msg = ⟨src', dst', t', mv⟩ then true else old.
        by_cases hmsg : (⟨p, dst, .echo, none⟩ : Message n) = ⟨src', dst', t', mv⟩
        · -- This is the matching send. Extract src' = p, dst' = dst, t' = echo, mv = none.
          have := Message.mk.inj hmsg
          obtain ⟨rfl, rfl, rfl, rfl⟩ := this
          -- Gate for send(p, dst, echo, none): p ∈ corrupted ∨ (isCorrect ∧ ... ∧ False).
          rcases hg with hcor | ⟨_, _, hfalse⟩
          · exact hcp_s hcor
          · exact hfalse
        · -- Different message: buffer unchanged.
          simp [hmsg] at hbuf_true
          rw [hbuf_false] at hbuf_true ; exact absurd hbuf_true Bool.false_ne_true
      | recv src' dst' t' mv =>
        rw [ht] at hbuf_true ; simp only at hbuf_true
        -- recv clears buffer, never sets it to true for a different message.
        by_cases hmsg : (⟨p, dst, .echo, none⟩ : Message n) = ⟨src', dst', t', mv⟩
        · simp [hmsg] at hbuf_true
        · simp [hmsg] at hbuf_true
          rw [hbuf_false] at hbuf_true ; exact absurd hbuf_true Bool.false_ne_true
      | decide j mv =>
        rw [ht] at hbuf_true ; rw [hbuf_false] at hbuf_true ; exact absurd hbuf_true Bool.false_ne_true)
    e hsafety
  exact hinv k p dst hcp

/-- Echo message tracking: if `p` has the `sent` flag for `echo(b) → q`,
    then either the message is in the buffer or `q` has already recorded
    it. Echo-analog of `init_msg_tracking`. -/
theorem echo_msg_tracking (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p q : Fin n) (b : Bool) :
    ((exec.drop k e 0).local_ p).sent q .echo (some b) = true →
    (exec.drop k e 0).buffer ⟨p, q, .echo, some b⟩ = true ∨
    ((exec.drop k e 0).local_ q).echoRecv p b = true := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p q b,
      (s.local_ p).sent q .echo (some b) = true →
      s.buffer ⟨p, q, .echo, some b⟩ = true ∨ (s.local_ q).echoRecv p b = true)
    (by intro s ⟨hlocal, _, _, _⟩ p q b hsent
        rw [hlocal p] at hsent ; exact absurd hsent Bool.false_ne_true)
    (by intro s s' hnext hinv_s p q b hsent_s'
        obtain ⟨i, hfire⟩ := hnext
        by_cases hsent_s : (s.local_ p).sent q .echo (some b) = true
        · rcases hinv_s p q b hsent_s with hbuf | hrcv
          · by_cases hbuf_s' : s'.buffer ⟨p, q, .echo, some b⟩ = true
            · exact Or.inl hbuf_s'
            · simp only [bca, GatedAction.fires] at hfire
              obtain ⟨hg, ht⟩ := hfire
              cases i with
              | corrupt j => subst ht ; simp_all
              | send src' dst' t' mv =>
                by_cases hmsg : (⟨p, q, .echo, some b⟩ : Message n) = ⟨src', dst', t', mv⟩
                · have := Message.mk.inj hmsg ; obtain ⟨rfl, rfl, rfl, rfl⟩ := this
                  subst ht ; simp at hbuf_s'
                · subst ht ; simp [hmsg] at hbuf_s' ; rw [hbuf] at hbuf_s' ; simp at hbuf_s'
              | recv src' dst' t' mv =>
                by_cases hmsg : (⟨p, q, .echo, some b⟩ : Message n) = ⟨src', dst', t', mv⟩
                · have := Message.mk.inj hmsg ; obtain ⟨rfl, rfl, rfl, rfl⟩ := this
                  right ; subst ht ; simp
                  by_cases halready : (s.local_ q).echoRecv p b = false
                  · rw [if_pos halready] ; simp
                  · rw [if_neg halready]
                    cases hv : (s.local_ q).echoRecv p b
                    · exact absurd hv halready
                    · exact rfl
                · subst ht ; simp [hmsg] at hbuf_s' ; rw [hbuf] at hbuf_s' ; simp at hbuf_s'
              | decide j mv => subst ht ; simp_all
          · exact Or.inr (echoRecv_step_mono n f input s s' i hfire q p b hrcv)
        · have hsent_false : (s.local_ p).sent q .echo (some b) = false := by
            cases hv : (s.local_ p).sent q .echo (some b)
            · rfl
            · exact absurd hv hsent_s
          obtain ⟨_, hfires_send⟩ :=
            sent_false_true_implies_send n f input s s' i hfire p q .echo (some b) hsent_false hsent_s'
          simp only [bca, GatedAction.fires] at hfires_send
          obtain ⟨_, ht⟩ := hfires_send
          left ; subst ht ; simp)
    e hsafety
  exact hinv k p q b

/-- Echo buffer-clear: if `echo(b)` was in the buffer at step `k` and is
    no longer at step `k+d`, then `q` has recorded it. -/
theorem echo_buffer_cleared (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (p q : Fin n) (b : Bool) (k d : Nat) :
    (exec.drop k e 0).buffer ⟨p, q, .echo, some b⟩ = true →
    (exec.drop (k + d) e 0).buffer ⟨p, q, .echo, some b⟩ = false →
    ((exec.drop (k + d) e 0).local_ q).echoRecv p b = true := by
  intro hbuf_k hbuf_kd
  have hsent_k := buffer_implies_sent n f input e hsafety k p q .echo (some b) hbuf_k
  have hsent_kd := sent_persist n f input e hsafety p q .echo (some b) k d hsent_k
  rcases echo_msg_tracking n f input e hsafety (k + d) p q b hsent_kd with hbuf | hrcv
  · exact absurd hbuf (by rw [hbuf_kd] ; exact Bool.false_ne_true)
  · exact hrcv

/-- `voteRecv q p v` is unchanged by any action other than `recv(p, q, vote, v)`.
    For the matching recv, it can only go false→true. -/
private theorem voteRecv_false_step (input : Fin n → Bool)
    (s s' : State n) (i : Action n)
    (hfire : ((bca n f input).actions i).fires s s')
    (q p : Fin n) (v : Val)
    (h : (s.local_ q).voteRecv p v = false)
    (hneq : i ≠ .recv p q .vote v) :
    (s'.local_ q).voteRecv p v = false := by
  simp only [bca, GatedAction.fires] at hfire
  obtain ⟨_, htrans⟩ := hfire
  cases i with
  | corrupt j => subst htrans ; exact h
  | send src dst t mv =>
    subst htrans ; simp only
    by_cases hq : q = src
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h
  | recv src dst t mv =>
    subst htrans ; simp only
    by_cases hq : q = dst
    · subst hq ; simp
      cases t with
      | vote =>
        dsimp only
        by_cases halready : (s.local_ q).voteRecv src mv = false
        · rw [if_pos halready]
          -- The update sets voteRecv for (src, mv). For (p, v) ≠ (src, mv), unchanged.
          have hne : ¬(p = src ∧ v = mv) := by
            intro ⟨rfl, rfl⟩ ; exact hneq rfl
          -- Goal: (decide (p = src) && decide (v = mv) || old) = false.
          -- Since ¬(p = src ∧ v = mv) and old = false: result is false.
          have : ¬(p = src ∧ v = mv) := hne
          simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h ⊢
          constructor
          · by_cases hp : p = src
            · right ; exact decide_eq_false (fun hv => hne ⟨hp, hv⟩)
            · left ; exact decide_eq_false hp
          · exact h
        · rw [if_neg halready] ; exact h
      | init =>
        cases mv with
        | none => exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).initRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
      | echo =>
        cases mv with
        | none => exact h
        | some bv =>
          dsimp only
          by_cases halready : (s.local_ q).echoRecv src bv = false
          · rw [if_pos halready] ; exact h
          · rw [if_neg halready] ; exact h
    · simp [hq] ; exact h
  | decide j mv =>
    subst htrans ; simp only
    by_cases hq : q = j
    · subst hq ; simp ; exact h
    · simp [hq] ; exact h

/-! ### Vote safety -/

/-- **Vote-none trace**: if a correct process `p` appears in any peer's
    `voteRecv` with value `none`, or if a `vote(none)` message from correct
    `p` is in the buffer, then `p.voted none = true`.  Independent inductive
    invariant (not part of `bca_inv`). -/
theorem vote_none_trace (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) :
    (∀ p q, isCorrect n (exec.drop k e 0) p →
      ((exec.drop k e 0).local_ q).voteRecv p none = true →
      ((exec.drop k e 0).local_ p).voted none = true) ∧
    (∀ p dst, isCorrect n (exec.drop k e 0) p →
      (exec.drop k e 0).buffer ⟨p, dst, .vote, none⟩ = true →
      ((exec.drop k e 0).local_ p).voted none = true) := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s =>
      (∀ p q, isCorrect n s p → (s.local_ q).voteRecv p none = true →
        (s.local_ p).voted none = true) ∧
      (∀ p dst, isCorrect n s p → s.buffer ⟨p, dst, .vote, none⟩ = true →
        (s.local_ p).voted none = true))
    (by intro s ⟨hlocal, hbuf, _, _⟩
        exact ⟨fun p q _ hvr => by rw [hlocal q] at hvr ; exact absurd hvr Bool.false_ne_true,
               fun p dst _ hb => by rw [hbuf] at hb ; exact absurd hb Bool.false_ne_true⟩)
    (by intro s s' hnext ⟨hinv_vr, hinv_buf⟩
        obtain ⟨i, hfire⟩ := hnext
        constructor
        · intro p q hcp_s' hvr_s'
          have hcp_s : isCorrect n s p :=
            fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
          by_cases hvr_s : (s.local_ q).voteRecv p none = true
          · exact voted_step_mono n f input s s' i hfire p none (hinv_vr p q hcp_s hvr_s)
          · -- voteRecv new. Case-split on action.
            cases i with
            | corrupt j =>
              simp only [bca, GatedAction.fires] at hfire
              obtain ⟨_, ht⟩ := hfire ; subst ht
              exact absurd hvr_s' hvr_s
            | send src' dst' t' mv =>
              simp only [bca, GatedAction.fires] at hfire
              obtain ⟨_, ht⟩ := hfire ; subst ht ; simp only at hvr_s'
              by_cases hq : q = src'
              · subst hq ; simp at hvr_s' ; exact absurd hvr_s' hvr_s
              · simp [hq] at hvr_s' ; exact absurd hvr_s' hvr_s
            | recv src' dst' t' mv =>
              simp only [bca, GatedAction.fires] at hfire
              obtain ⟨hg, ht⟩ := hfire
              by_cases hq : q = dst'
              · rw [← hq] at hg ht
                by_cases hmatch : p = src' ∧ t' = .vote ∧ mv = none
                · obtain ⟨rfl, rfl, rfl⟩ := hmatch
                  -- hg : buffer ⟨p, dst', vote, none⟩ = true. hq : q = dst'.
                  have hvoted_s := hinv_buf p q hcp_s hg
                  exact voted_step_mono n f input s s'
                    (.recv p q .vote none)
                    (by simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩)
                    p none hvoted_s
                · -- Not matching recv: voteRecv p none unchanged.
                  rw [ht] at hvr_s' ; simp at hvr_s'
                  -- Need to show voteRecv didn't change for non-matching recv.
                  -- The recv updates voteRecv for (src', mv) if t' = vote.
                  -- For non-matching (src', t', mv) ≠ (p, vote, none), unchanged.
                  cases t' with
                  | vote =>
                    have hne_action : Action.recv src' q .vote mv ≠ .recv p q .vote none := by
                      intro heq ; apply hmatch
                      injection heq with h1 _ _ h4
                      exact ⟨h1.symm, rfl, h4⟩
                    have := voteRecv_false_step n f input s s' (.recv src' q .vote mv) (by simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩) q p none
                      (by cases hv : (s.local_ q).voteRecv p none ; rfl ; exact absurd hv hvr_s) hne_action
                    exact absurd hvr_s' (by simp_all)
                  | init =>
                    have := voteRecv_false_step n f input s s' (.recv src' q .init mv) (by simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩) q p none
                      (by cases hv : (s.local_ q).voteRecv p none ; rfl ; exact absurd hv hvr_s)
                      (by simp)
                    exact absurd hvr_s' (by simp_all)
                  | echo =>
                    have := voteRecv_false_step n f input s s' (.recv src' q .echo mv) (by simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩) q p none
                      (by cases hv : (s.local_ q).voteRecv p none ; rfl ; exact absurd hv hvr_s)
                      (by simp)
                    exact absurd hvr_s' (by simp_all)
              · -- q ≠ dst': voteRecv at q unchanged.
                have := voteRecv_false_step n f input s s' (.recv src' dst' t' mv) (by simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩) q p none
                  (by cases hv : (s.local_ q).voteRecv p none ; rfl ; exact absurd hv hvr_s)
                  (by intro heq ; injection heq with _ h2 ; exact hq h2.symm)
                exact absurd hvr_s' (by simp_all)
            | decide j mv =>
              have := voteRecv_false_step n f input s s' (.decide j mv) hfire q p none
                (by cases hv : (s.local_ q).voteRecv p none ; rfl ; exact absurd hv hvr_s)
                (by simp)
              exact absurd hvr_s' (by simp_all)
        · intro p dst hcp_s' hbuf_s'
          have hcp_s : isCorrect n s p :=
            fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
          by_cases hbuf_s : s.buffer ⟨p, dst, .vote, none⟩ = true
          · exact voted_step_mono n f input s s' i hfire p none (hinv_buf p dst hcp_s hbuf_s)
          · -- buffer new. Case-split on action.
            simp only [bca, GatedAction.fires] at hfire
            obtain ⟨hg, ht⟩ := hfire
            cases i with
            | corrupt j => subst ht ; exact absurd hbuf_s' hbuf_s
            | send src' dst' t' mv =>
              by_cases hmsg : (⟨p, dst, .vote, none⟩ : Message n) = ⟨src', dst', t', mv⟩
              · -- Matching send. Extract p = src', dst = dst', t' = vote, mv = none.
                have := Message.mk.inj hmsg
                obtain ⟨rfl, rfl, rfl, rfl⟩ := this
                -- send(p, dst, vote, none) fired. Transition sets voted none = true.
                subst ht ; simp only
                simp only [isCorrect] at hcp_s ; simp [hcp_s]
              · subst ht ; simp [hmsg] at hbuf_s' ; exact absurd hbuf_s' hbuf_s
            | recv src' dst' t' mv =>
              by_cases hmsg : (⟨p, dst, .vote, none⟩ : Message n) = ⟨src', dst', t', mv⟩
              · subst ht ; simp [hmsg] at hbuf_s'
              · subst ht ; simp [hmsg] at hbuf_s' ; exact absurd hbuf_s' hbuf_s
            | decide j mv => subst ht ; exact absurd hbuf_s' hbuf_s)
    e hsafety
  exact hinv k

/-- Safety corollary: if a correct process `p` shows up in any peer's
    `voteRecv` for value `v`, then `p.voted v = true`. For binary `v`,
    pulls out `bca_inv` conjunct 4 (vote trace). For `v = none`, the
    result would come from a similar invariant — sorried here pending
    extension of `bca_inv`. -/
theorem voted_from_voteRecv (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p q : Fin n) (v : Val)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hvr : ((exec.drop k e 0).local_ q).voteRecv p v = true) :
    ((exec.drop k e 0).local_ p).voted v = true := by
  cases v with
  | some b =>
    -- Use bca_inv conjunct 4 (vote trace, binary).
    have hinv := init_invariant
      (bca_inv_init n f input)
      (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
      e hsafety
    obtain ⟨_, _, _, hvtrace, _, _, _, _, _, _, _, _⟩ := hinv k
    exact hvtrace q p b hcp hvr
  | none =>
    exact (vote_none_trace n f input e hsafety k).1 p q hcp hvr

/-- Safety corollary of `bca_inv` conjunct 8 (vote agreement): any two
    correct processes that have voted binary values have voted the same
    value. -/
theorem voted_binary_agree (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p q : Fin n) (b₁ b₂ : Bool)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hcq : isCorrect n (exec.drop k e 0) q)
    (hvp : ((exec.drop k e 0).local_ p).voted (some b₁) = true)
    (hvq : ((exec.drop k e 0).local_ q).voted (some b₂) = true) :
    b₁ = b₂ := by
  have hinv := init_invariant
    (bca_inv_init n f input)
    (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
    e hsafety
  obtain ⟨_, _, _, _, _, _, _, _, hvagree, _, _, _⟩ := hinv k
  exact hvagree p q b₁ b₂ hcp hcq hvp hvq

/-- **Vote is single-shot**: a correct process votes at most one value.
    Enforced by the vote send gate's vote-once clause. Inductive invariant. -/
theorem voted_unique (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p : Fin n) (w w' : Val)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hv : ((exec.drop k e 0).local_ p).voted w = true)
    (hv' : ((exec.drop k e 0).local_ p).voted w' = true) :
    w = w' := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p w w', isCorrect n s p →
      (s.local_ p).voted w = true → (s.local_ p).voted w' = true → w = w')
    (by -- hinit: initial state has voted = fun _ => false.
      intro s ⟨hlocal, _, _, _⟩ p w w' _ hv _
      rw [hlocal p] at hv ; exact absurd hv Bool.false_ne_true)
    (by -- hnext: vote-once is preserved. The vote gate requires ∀ w, voted w → w = mv.
      intro s s' hnext hinv_s p w w' hcp_s' hv_s' hv'_s'
      obtain ⟨i, hfire⟩ := hnext
      have hcp_s : isCorrect n s p :=
        fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
      -- Case-split on the action. Only vote send from correct p changes voted.
      simp only [bca, GatedAction.fires] at hfire
      obtain ⟨hg, ht⟩ := hfire
      cases i with
      | corrupt j =>
        subst ht
        -- corrupt doesn't change voted. Both were old. IH.
        exact hinv_s p w w' hcp_s hv_s' hv'_s'
      | send src' dst' t' mv =>
        by_cases hp : p = src'
        · subst hp
          cases t' with
          | vote =>
            -- vote send from p. Transition: voted x := if x = mv then true else old.
            -- Gate requires ∀ x, voted x → x = mv (vote-once at s).
            subst ht ; simp at hv_s' hv'_s'
            -- hv_s' : w = mv ∨ old_voted w. hv'_s' : w' = mv ∨ old_voted w'.
            simp only [isCorrect] at hcp_s
            simp [hcp_s] at hv_s' hv'_s'
            -- After simp: hv_s' : w = mv ∨ voted w at s. Same for w'.
            rcases hg with hcor | ⟨_, _, hvonce, _⟩
            · exact absurd hcor hcp_s
            · rcases hv_s' with rfl | hold
              · rcases hv'_s' with rfl | hold'
                · rfl
                · exact (hvonce w' hold').symm
              · rcases hv'_s' with rfl | hold'
                · exact hvonce w hold
                · exact hinv_s p w w' hcp_s hold hold'
          | init => subst ht ; simp at hv_s' hv'_s' ; exact hinv_s p w w' hcp_s hv_s' hv'_s'
          | echo => subst ht ; simp at hv_s' hv'_s' ; exact hinv_s p w w' hcp_s hv_s' hv'_s'
        · -- Different process: voted at p unchanged.
          subst ht ; simp [hp] at hv_s' hv'_s'
          exact hinv_s p w w' hcp_s hv_s' hv'_s'
      | recv src' dst' t' mv =>
        -- recv doesn't change voted. Show voted at s' = voted at s.
        subst ht ; simp only at hv_s' hv'_s'
        by_cases hp : p = dst'
        · subst hp ; simp at hv_s' hv'_s'
          -- After simp, the recv-modified LocalState still has same voted.
          -- Need to show voted is preserved through all recv variants.
          cases t' <;> (try cases mv) <;> simp at hv_s' hv'_s' <;>
            (try (split at hv_s' ; split at hv'_s')) <;> simp_all <;>
            exact hinv_s p w w' hcp_s hv_s' hv'_s'
        · simp [hp] at hv_s' hv'_s'
          exact hinv_s p w w' hcp_s hv_s' hv'_s'
      | decide j mv =>
        subst ht ; simp only at hv_s' hv'_s'
        by_cases hp : p = j
        · subst hp ; simp at hv_s' hv'_s'
          exact hinv_s p w w' hcp_s hv_s' hv'_s'
        · simp [hp] at hv_s' hv'_s'
          exact hinv_s p w w' hcp_s hv_s' hv'_s')
    e hsafety
  exact hinv k p w w' hcp hv hv'

/-- A correct process that has voted a binary value `b` has ≥ `n − f`
    echo receipts for `b`. Follows from `bca_inv` conjunct 9 (echo
    backing). -/
theorem voted_binary_implies_echo_quorum (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p : Fin n) (b : Bool)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hv : ((exec.drop k e 0).local_ p).voted (some b) = true) :
    countEchoRecv n ((exec.drop k e 0).local_ p) b ≥ n - f := by
  have hinv := init_invariant
    (bca_inv_init n f input)
    (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
    e hsafety
  obtain ⟨_, _, _, _, _, _, _, _, _, hecho_back, _, _⟩ := hinv k
  have := hecho_back p b hcp hv
  unfold echoThreshold at this
  exact this

/-- A correct process that has voted `⊥` has approved both values.
    Follows from the vote-`none` send gate's requirement at time of
    voting plus monotonicity of `approved`. -/
theorem voted_none_implies_both_approved (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p : Fin n)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hv : ((exec.drop k e 0).local_ p).voted none = true) :
    ((exec.drop k e 0).local_ p).approved false = true ∧
    ((exec.drop k e 0).local_ p).approved true = true := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p, isCorrect n s p →
      (s.local_ p).voted none = true →
      (s.local_ p).approved false = true ∧ (s.local_ p).approved true = true)
    (by -- hinit: voted = false initially.
      intro s ⟨hlocal, _, _, _⟩ p _ hv
      rw [hlocal p] at hv ; exact absurd hv Bool.false_ne_true)
    (by -- hnext: if voted none at s' and correct, then both approved at s'.
      -- Either voted none was already at s (IH + approved_step_mono)
      -- or it was just set (vote gate requires both approved + approved_step_mono).
      intro s s' hnext hinv_s p hcp_s' hv_s'
      obtain ⟨i, hfire⟩ := hnext
      have hcp_s : isCorrect n s p :=
        fun hmem => hcp_s' (corrupted_step_mono n f input s s' i hfire p hmem)
      by_cases hv_s : (s.local_ p).voted none = true
      · -- Already voted none at s. Both approved at s by IH. Persist.
        obtain ⟨haf, hat⟩ := hinv_s p hcp_s hv_s
        exact ⟨approved_step_mono n f input s s' i hfire p false haf,
               approved_step_mono n f input s s' i hfire p true hat⟩
      · -- voted none is new. Find the action that set it.
        -- The gate for vote(none) requires approved false ∧ approved true.
        -- Extract approved from gate, persist via approved_step_mono.
        -- Save the fires proof before destructuring.
        have hfire_saved := hfire
        simp only [bca, GatedAction.fires] at hfire
        obtain ⟨hg, ht⟩ := hfire
        cases i with
        | corrupt j => subst ht ; exact absurd hv_s' hv_s
        | send src' dst' t' mv =>
          by_cases hp : p = src'
          · subst hp
            cases t' with
            | vote =>
              subst ht ; simp only at hv_s'
              simp only [isCorrect] at hcp_s ; simp [hcp_s] at hv_s'
              rcases hv_s' with rfl | hold
              · -- mv = none. Gate requires both approved.
                rcases hg with hcor | ⟨_, _, _, haf, hat⟩
                · exact absurd hcor hcp_s
                · exact ⟨approved_step_mono n f input s _ (.send p dst' .vote none)
                    hfire_saved p false haf,
                  approved_step_mono n f input s _ (.send p dst' .vote none)
                    hfire_saved p true hat⟩
              · exact absurd hold hv_s
            | init => subst ht ; simp at hv_s' ; exact absurd hv_s' hv_s
            | echo => subst ht ; simp at hv_s' ; exact absurd hv_s' hv_s
          · subst ht ; simp [hp] at hv_s' ; exact absurd hv_s' hv_s
        | recv src' dst' t' mv =>
          subst ht ; simp only at hv_s'
          by_cases hp : p = dst'
          · subst hp ; simp at hv_s'
            cases t' <;> (try cases mv) <;> simp at hv_s' <;>
              (try (split at hv_s' <;> simp_all)) <;> exact absurd hv_s' hv_s
          · simp [hp] at hv_s' ; exact absurd hv_s' hv_s
        | decide j mv =>
          subst ht ; simp only at hv_s'
          by_cases hp : p = j
          · subst hp ; simp at hv_s' ; exact absurd hv_s' hv_s
          · simp [hp] at hv_s' ; exact absurd hv_s' hv_s)
    e hsafety
  exact hinv k p hcp hv

/-- Vote send gate from an echo quorum (binary vote case): if `p` is
    correct, has ≥ `n − f` echoes for `b`, has not yet sent the specific
    vote, and every previously-voted value is `some b`, then the vote
    send gate for `.send p r .vote (some b)` holds. -/
theorem vote_send_gate_from_echo_quorum (input : Fin n → Bool)
    (p r : Fin n) (b : Bool) (s : State n)
    (hcp : isCorrect n s p)
    (hsent_false : (s.local_ p).sent r .vote (some b) = false)
    (hecho_quorum : countEchoRecv n (s.local_ p) b ≥ n - f)
    (hvote_once : ∀ w, (s.local_ p).voted w = true → w = some b) :
    ((bca n f input).actions (.send p r .vote (some b))).gate s := by
  refine Or.inr ⟨hcp, hsent_false, hvote_once, ?_⟩
  show countEchoRecv n (s.local_ p) b ≥ echoThreshold n f
  unfold echoThreshold ; exact hecho_quorum

/-- Vote send gate from both-approved (⊥ vote case): if `p` is correct,
    has approved both values, has not yet sent the specific vote, and
    every previously-voted value is `none`, then the vote send gate for
    `.send p r .vote none` holds. -/
theorem vote_send_gate_from_both_approved (input : Fin n → Bool)
    (p r : Fin n) (s : State n)
    (hcp : isCorrect n s p)
    (hsent_false : (s.local_ p).sent r .vote none = false)
    (happ_f : (s.local_ p).approved false = true)
    (happ_t : (s.local_ p).approved true = true)
    (hvote_once : ∀ w, (s.local_ p).voted w = true → w = none) :
    ((bca n f input).actions (.send p r .vote none)).gate s := by
  exact Or.inr ⟨hcp, hsent_false, hvote_once, happ_f, happ_t⟩

/-- Vote message tracking: if `p` has the `sent` flag for `vote(v) → q`,
    then either the message is in the buffer or `q` has already recorded
    it. Vote-analog of `init_msg_tracking`. -/
theorem vote_msg_tracking (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (k : Nat) (p q : Fin n) (v : Val) :
    ((exec.drop k e 0).local_ p).sent q .vote v = true →
    (exec.drop k e 0).buffer ⟨p, q, .vote, v⟩ = true ∨
    ((exec.drop k e 0).local_ q).voteRecv p v = true := by
  have hinv := init_invariant
    (init := (bca n f input).init)
    (next := (bca n f input).next)
    (inv := fun s => ∀ p q v,
      (s.local_ p).sent q .vote v = true →
      s.buffer ⟨p, q, .vote, v⟩ = true ∨ (s.local_ q).voteRecv p v = true)
    (by intro s ⟨hlocal, _, _, _⟩ p q v hsent
        rw [hlocal p] at hsent ; exact absurd hsent Bool.false_ne_true)
    (by intro s s' hnext hinv_s p q v hsent_s'
        obtain ⟨i, hfire⟩ := hnext
        by_cases hsent_s : (s.local_ p).sent q .vote v = true
        · rcases hinv_s p q v hsent_s with hbuf | hrcv
          · by_cases hbuf_s' : s'.buffer ⟨p, q, .vote, v⟩ = true
            · exact Or.inl hbuf_s'
            · simp only [bca, GatedAction.fires] at hfire
              obtain ⟨hg, ht⟩ := hfire
              cases i with
              | corrupt j => subst ht ; simp_all
              | send src' dst' t' mv =>
                by_cases hmsg : (⟨p, q, .vote, v⟩ : Message n) = ⟨src', dst', t', mv⟩
                · have := Message.mk.inj hmsg ; obtain ⟨rfl, rfl, rfl, rfl⟩ := this
                  subst ht ; simp at hbuf_s'
                · subst ht ; simp [hmsg] at hbuf_s' ; rw [hbuf] at hbuf_s' ; simp at hbuf_s'
              | recv src' dst' t' mv =>
                by_cases hmsg : (⟨p, q, .vote, v⟩ : Message n) = ⟨src', dst', t', mv⟩
                · have := Message.mk.inj hmsg ; obtain ⟨rfl, rfl, rfl, rfl⟩ := this
                  right ; subst ht ; simp
                  by_cases halready : (s.local_ q).voteRecv p v = false
                  · rw [if_pos halready] ; simp
                  · rw [if_neg halready]
                    cases hv : (s.local_ q).voteRecv p v
                    · exact absurd hv halready
                    · exact rfl
                · subst ht ; simp [hmsg] at hbuf_s' ; rw [hbuf] at hbuf_s' ; simp at hbuf_s'
              | decide j mv => subst ht ; simp_all
          · exact Or.inr (voteRecv_step_mono n f input s s' i hfire q p v hrcv)
        · have hsent_false : (s.local_ p).sent q .vote v = false := by
            cases hv : (s.local_ p).sent q .vote v
            · rfl
            · exact absurd hv hsent_s
          obtain ⟨_, hfires_send⟩ :=
            sent_false_true_implies_send n f input s s' i hfire p q .vote v hsent_false hsent_s'
          simp only [bca, GatedAction.fires] at hfires_send
          obtain ⟨_, ht⟩ := hfires_send
          left ; subst ht ; simp)
    e hsafety
  exact hinv k p q v

/-- Vote buffer-clear: if `vote(v)` was in the buffer at step `k` and is
    no longer at step `k+d`, then `q` has recorded it. -/
theorem vote_buffer_cleared (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (p q : Fin n) (v : Val) (k d : Nat) :
    (exec.drop k e 0).buffer ⟨p, q, .vote, v⟩ = true →
    (exec.drop (k + d) e 0).buffer ⟨p, q, .vote, v⟩ = false →
    ((exec.drop (k + d) e 0).local_ q).voteRecv p v = true := by
  intro hbuf_k hbuf_kd
  have hsent_k := buffer_implies_sent n f input e hsafety k p q .vote v hbuf_k
  have hsent_kd := sent_persist n f input e hsafety p q .vote v k d hsent_k
  rcases vote_msg_tracking n f input e hsafety (k + d) p q v hsent_kd with hbuf | hrcv
  · exact absurd hbuf (by rw [hbuf_kd] ; exact Bool.false_ne_true)
  · exact hrcv

/-! ## Gate persistence lemmas

    Send-gate persistence: the gate stays enabled as long as the specific
    send has not yet fired, provided the safety-style premises of the
    gate (honest condition, approved flags, etc.) remain true — which
    they do by monotonicity of the underlying fields.

    Per-value persistence (`init_send_gate_persist`) is used for init.
    Type-level persistence (`echo_send_gate_type_persist`,
    `vote_send_gate_type_persist`) is used for echo/vote via
    `wf_chain_type`. The cross-commit lemma
    (`send_gate_persist_across_commit`) handles the case where a send to
    another destination commits `echoed`/`voted`. -/

/-- The init send gate `((bca).actions (.send s r .init (some b))).gate`
    is monotone in time *while the specific send has not yet fired*
    (`sent r .init (some b) = false`). Three cases at the later step:
    `s` corrupt → left disjunct; `s` correct and `sent = false` →
    honest-cond persists via `initRecv_persist` +
    `correct_initRecv_implies_honest_cond`. Matches the wf1-style
    persistence premise of `wf_send`. -/
theorem init_send_gate_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (s r p : Fin n) (b : Bool) (k d : Nat)
    (hir : ((exec.drop k e 0).local_ p).initRecv s b = true)
    (hsent_false : ((exec.drop (k + d) e 0).local_ s).sent r .init (some b) = false) :
    ((bca n f input).actions (.send s r .init (some b))).gate (exec.drop k e 0) →
    ((bca n f input).actions (.send s r .init (some b))).gate (exec.drop (k + d) e 0) := by
  intro _
  by_cases hcs : isCorrect n (exec.drop (k + d) e 0) s
  · -- Correct s at k+d; honest-cond from initRecv (persisted) at s
    have hir_d : ((exec.drop (k + d) e 0).local_ p).initRecv s b = true :=
      initRecv_persist n f input e hsafety p s b k d hir
    have hhonest := correct_initRecv_implies_honest_cond n f input e hsafety
      (k + d) s p b hcs hir_d
    exact Or.inr ⟨hcs, hsent_false, hhonest⟩
  · -- Faulty s at k+d: gate via `src ∈ corrupted` disjunct
    exact Or.inl (by simpa [isCorrect] using hcs)

/-- **Send gate persists across commit**: once a process commits to sending
    `(t, w₀)` by firing a send to some destination `dst₀`, the gate for
    sending the same `(t, w₀)` to any other destination `dst` remains open
    — because `echoed`/`voted` locks to `w₀` and all other gate conditions
    (approved, echo quorum, etc.) are monotone. -/
private theorem send_gate_persist_across_commit (input : Fin n → Bool)
    (src dst dst₀ : Fin n) (t : MsgType) (w₀ : Val)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (j d : Nat)
    (hcorr_j : isCorrect n (e j) src)
    (hcorr_future : isCorrect n (e (j + 1 + d)) src)
    (hsf_future : ((e (j + 1 + d)).local_ src).sent dst t w₀ = false)
    (hgate_j : ((bca n f input).actions (.send src dst₀ t w₀)).gate (e j))
    (hfires : ((bca n f input).actions (.send src dst₀ t w₀)).fires (e j) (e (j + 1))) :
    ((bca n f input).actions (.send src dst t w₀)).gate (e (j + 1 + d)) := by
  apply Or.inr
  refine ⟨hcorr_future, hsf_future, ?_⟩
  have hgate_right := hgate_j.resolve_left (by exact hcorr_j)
  obtain ⟨_, _, htype_cond⟩ := hgate_right
  simp only [bca, GatedAction.fires] at hfires
  obtain ⟨_, ht⟩ := hfires
  cases t with
  | init =>
    cases w₀ with
    | none => exact htype_cond
    | some b =>
      rcases htype_cond with hinput | hcount
      · exact Or.inl hinput
      · exact Or.inr (by
          have := countInitRecv_persist n f input e hsafety src b
            (amplifyThreshold f) j (1 + d)
            (by simp only [exec.drop, Nat.zero_add] ; exact hcount)
          simp only [exec.drop, Nat.zero_add] at this
          rwa [show j + (1 + d) = j + 1 + d from by omega] at this)
  | echo =>
    cases w₀ with
    | none => exact (htype_cond : False).elim
    | some b =>
      obtain ⟨happ, _⟩ := htype_cond
      constructor
      · have := approved_persist n f input e hsafety src b j (1 + d)
          (by simp only [exec.drop, Nat.zero_add] ; exact happ)
        simp only [exec.drop, Nat.zero_add] at this
        rwa [show j + (1 + d) = j + 1 + d from by omega] at this
      · right
        have hechoed_commit : ((e (j + 1)).local_ src).echoed = some b := by
          rw [ht] ; simp only [ite_true]
          simp only [isCorrect] at hcorr_j ; simp [hcorr_j]
        have := echoed_persist n f input e hsafety src b (j + 1) d
          (by simp only [exec.drop, Nat.zero_add] ; exact hechoed_commit)
        simp only [exec.drop, Nat.zero_add] at this ; exact this
  | vote =>
    obtain ⟨hvonce, hvcond⟩ := htype_cond
    constructor
    · intro w hvw
      have hvoted_commit : ((e (j + 1)).local_ src).voted w₀ = true := by
        rw [ht] ; simp only [ite_true]
        simp only [isCorrect] at hcorr_j ; simp [hcorr_j]
      have hvoted_w₀ := voted_persist n f input e hsafety src w₀ (j + 1) d
        (by simp only [exec.drop, Nat.zero_add] ; exact hvoted_commit)
      simp only [exec.drop, Nat.zero_add] at hvoted_w₀
      exact voted_unique n f input e hsafety (j + 1 + d) src w w₀
        (by simp only [exec.drop, Nat.zero_add] ; exact hcorr_future)
        (by simp only [exec.drop, Nat.zero_add] ; exact hvw)
        (by simp only [exec.drop, Nat.zero_add] ; exact hvoted_w₀)
    · cases w₀ with
      | some b =>
        have := countEchoRecv_persist n f input e hsafety src b
          (echoThreshold n f) j (1 + d)
          (by simp only [exec.drop, Nat.zero_add] ; exact hvcond)
        simp only [exec.drop, Nat.zero_add] at this
        rwa [show j + (1 + d) = j + 1 + d from by omega] at this
      | none =>
        obtain ⟨haf, hat⟩ := hvcond
        exact ⟨by have := approved_persist n f input e hsafety src false j (1 + d)
                    (by simp only [exec.drop, Nat.zero_add] ; exact haf)
                  simp only [exec.drop, Nat.zero_add] at this
                  rwa [show j + (1 + d) = j + 1 + d from by omega] at this,
               by have := approved_persist n f input e hsafety src true j (1 + d)
                    (by simp only [exec.drop, Nat.zero_add] ; exact hat)
                  simp only [exec.drop, Nat.zero_add] at this
                  rwa [show j + (1 + d) = j + 1 + d from by omega] at this⟩

/-- If no echo send from `src` fires at step `k` (echo sent flags unchanged),
    then `echoed` at `src` is unchanged at step `k+1`. -/
private theorem echoed_unch_when_no_echo_send (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (src : Fin n) (k : Nat)
    (hsent_eq : ∀ dst' w,
      ((exec.drop (k + 1) e 0).local_ src).sent dst' .echo w =
      ((exec.drop k e 0).local_ src).sent dst' .echo w)
    (hfire' : ((bca n f input).actions i).fires (e k) (e (k + 1))) :
    ((e (k + 1)).local_ src).echoed = ((e k).local_ src).echoed := by
  simp only [bca, GatedAction.fires] at hfire'
  obtain ⟨hg, ht⟩ := hfire'
  cases i with
  | corrupt j => rw [ht]
  | send src' dst' t' mv =>
    rw [ht] ; simp only
    by_cases hp : src' = src
    · rw [hp] at ht hg ⊢ ; simp
      cases t' with
      | echo =>
        -- For corrupt src: echoed = if ¬src ∈ corrupted then some b else old = old.
        -- For correct src: sent changes, contradicting hsent_eq.
        -- Check: is src corrupt?
        cases mv with
        | none => rfl  -- echo none: echoed unchanged regardless
        | some b =>
          by_cases hcor : src ∈ (e k).corrupted
          · -- corrupt src: echoed unchanged.
            simp [hcor]
          · -- correct src: echoed = some b. But sent changed, contradiction.
            exfalso
            have hfires : ((bca n f input).actions (.send src dst' .echo (some b))).fires
                (e k) (e (k + 1)) := by
              simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩
            have h1 := sent_true_after_send n f input _ _ src dst' .echo (some b) hfires
            have h2 := hsent_eq dst' (some b)
            simp only [exec.drop, Nat.zero_add] at h2
            -- h1 : (e (k+1)).local_ src .sent = true.
            -- h2 : (e (k+1)).sent = (e k).sent (after exec.drop simplification).
            -- Gate (correct case) requires sent = false at k.
            simp only [bca, GatedAction.fires] at hfires
            obtain ⟨hg', _⟩ := hfires
            rcases hg' with hcor' | ⟨_, hsf, _⟩
            · exact absurd hcor' hcor
            · -- hsf : sent = false at k. h2 : sent at k+1 = sent at k. h1 : sent at k+1 = true.
              -- So false = true. Contradiction.
              rw [h1] at h2 ; rw [← h2] at hsf
              exact absurd hsf (by simp)
      | init => rfl
      | vote => rfl
    · simp [Ne.symm hp]
  | recv src' dst' t' mv =>
    rw [ht] ; simp only
    by_cases hp : dst' = src
    · subst hp ; simp
      cases t' <;> (try cases mv) <;> simp <;> (try split <;> simp)
    · simp [Ne.symm hp]
  | decide j mv =>
    rw [ht] ; simp only
    by_cases hp : j = src
    · subst hp ; simp
    · simp [Ne.symm hp]

/-- **Type-level echo gate persistence**: if all echo gates in `X` are open
    and no echo send fires from `src` (sent unchanged for echo type), then
    all echo gates in `X` stay open.  When no echo send fires, `echoed` and
    `sent` are unchanged and `approved` only grows. -/
theorem echo_send_gate_type_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (src dst : Fin n) (X : Val → Prop) (k : Nat)
    (hgates : ∀ v, X v →
      ((bca n f input).actions (.send src dst .echo v)).gate (exec.drop k e 0))
    (hsent_eq : ∀ dst' w,
      ((exec.drop (k + 1) e 0).local_ src).sent dst' .echo w =
      ((exec.drop k e 0).local_ src).sent dst' .echo w) :
    ∀ v, X v →
      ((bca n f input).actions (.send src dst .echo v)).gate (exec.drop (k + 1) e 0) := by
  obtain ⟨i, hfire⟩ := hsafety.2 k
  have hfire' : ((bca n f input).actions i).fires (e k) (e (k + 1)) := by
    have := hfire ; simp only [exec.drop, Nat.zero_add] at this
    rwa [show 1 + k = k + 1 from by omega] at this
  -- echoed unchanged when no echo send fires from src.
  have hecho_unch : ((e (k + 1)).local_ src).echoed = ((e k).local_ src).echoed :=
    echoed_unch_when_no_echo_send n f input e hsafety src k hsent_eq hfire'
  -- Now prove for each v ∈ X.
  intro v hv
  cases v with
  | none =>
    rcases hgates none hv with hcorrupt | ⟨_, _, hfalse⟩
    · left ; simp only [exec.drop, Nat.zero_add] at hcorrupt ⊢
      exact corrupted_step_mono n f input _ _ i hfire' src hcorrupt
    · exact hfalse.elim
  | some b =>
    rcases hgates (some b) hv with hcorrupt | ⟨hcp, hsf, happ, hecho⟩
    · left ; simp only [exec.drop, Nat.zero_add] at hcorrupt ⊢
      exact corrupted_step_mono n f input _ _ i hfire' src hcorrupt
    · by_cases hcp1 : isCorrect n (exec.drop (k + 1) e 0) src
      · -- Still correct at k+1. Build right disjunct.
        apply Or.inr
        have hsf' : ((exec.drop (k + 1) e 0).local_ src).sent dst .echo (some b) = false := by
          rw [hsent_eq dst (some b)] ; exact hsf
        simp only [exec.drop, Nat.zero_add] at hcp1 hsf' happ hecho ⊢
        have happ' : ((e (k + 1)).local_ src).approved b = true := by
          have := approved_persist n f input e hsafety src b k 1
            (by simp only [exec.drop, Nat.zero_add] ; exact happ)
          simp only [exec.drop, Nat.zero_add] at this ; exact this
        have hecho' : ((e (k + 1)).local_ src).echoed = none ∨
            ((e (k + 1)).local_ src).echoed = some b := by
          rw [hecho_unch] ; exact hecho
        exact ⟨hcp1, hsf', happ', hecho'⟩
      · -- Corrupted at k+1: left disjunct.
        exact Or.inl (by simp only [exec.drop, Nat.zero_add, isCorrect, Classical.not_not] at hcp1 ⊢ ; exact hcp1)

/-- If no vote send from `src` fires at step `k` (vote sent flags unchanged),
    then `voted` at `src` is unchanged at step `k+1`. -/
private theorem voted_unch_when_no_vote_send (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (src : Fin n) (k : Nat)
    (hsent_eq : ∀ dst' w,
      ((exec.drop (k + 1) e 0).local_ src).sent dst' .vote w =
      ((exec.drop k e 0).local_ src).sent dst' .vote w)
    (hfire' : ((bca n f input).actions i).fires (e k) (e (k + 1))) :
    ∀ w, ((e (k + 1)).local_ src).voted w = ((e k).local_ src).voted w := by
  simp only [bca, GatedAction.fires] at hfire'
  obtain ⟨hg, ht⟩ := hfire'
  intro w
  cases i with
  | corrupt j => rw [ht]
  | send src' dst' t' mv =>
    rw [ht] ; simp only
    by_cases hp : src' = src
    · rw [hp] at ht hg ⊢ ; simp
      cases t' with
      | vote =>
        -- For corrupt src: voted = if src ∉ corrupted then updated else old = old.
        -- For correct src: sent changes, contradicting hsent_eq.
        by_cases hcor : src ∈ (e k).corrupted
        · -- corrupt: voted unchanged
          simp [hcor]
        · -- correct: sent changes → contradiction
          exfalso
          have hfires : ((bca n f input).actions (.send src dst' .vote mv)).fires
              (e k) (e (k + 1)) := by
            simp only [bca, GatedAction.fires] ; exact ⟨hg, ht⟩
          have h1 := sent_true_after_send n f input _ _ src dst' .vote mv hfires
          have h2 := hsent_eq dst' mv
          simp only [exec.drop, Nat.zero_add] at h2
          simp only [bca, GatedAction.fires] at hfires
          obtain ⟨hg', _⟩ := hfires
          rcases hg' with hcor' | ⟨_, hsf, _⟩
          · exact absurd hcor' hcor
          · rw [h1] at h2 ; rw [← h2] at hsf
            exact absurd hsf (by simp)
      | init => rfl
      | echo => rfl
    · simp [Ne.symm hp]
  | recv src' dst' t' mv =>
    rw [ht] ; simp only
    by_cases hp : dst' = src
    · subst hp ; simp
      cases t' <;> (try cases mv) <;> simp <;> (try split <;> simp)
    · simp [Ne.symm hp]
  | decide j mv =>
    rw [ht] ; simp only
    by_cases hp : j = src
    · subst hp ; simp
    · simp [Ne.symm hp]

/-- **Type-level vote gate persistence**: if all vote gates in `X` are open
    and no vote send fires from `src` (sent unchanged for vote type), then
    all vote gates in `X` stay open.  When no vote send fires, `voted` and
    `sent` are unchanged and echo counts / approved only grow. -/
theorem vote_send_gate_type_persist (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : (bca n f input).safety e)
    (src dst : Fin n) (X : Val → Prop) (k : Nat)
    (hgates : ∀ v, X v →
      ((bca n f input).actions (.send src dst .vote v)).gate (exec.drop k e 0))
    (hsent_eq : ∀ dst' w,
      ((exec.drop (k + 1) e 0).local_ src).sent dst' .vote w =
      ((exec.drop k e 0).local_ src).sent dst' .vote w) :
    ∀ v, X v →
      ((bca n f input).actions (.send src dst .vote v)).gate (exec.drop (k + 1) e 0) := by
  obtain ⟨i, hfire⟩ := hsafety.2 k
  have hfire' : ((bca n f input).actions i).fires (e k) (e (k + 1)) := by
    have := hfire ; simp only [exec.drop, Nat.zero_add] at this
    rwa [show 1 + k = k + 1 from by omega] at this
  -- voted unchanged when no vote send fires from src.
  have hvoted_unch := voted_unch_when_no_vote_send n f input e hsafety src k hsent_eq hfire'
  -- Now prove for each v ∈ X.
  intro v hv
  -- Vote gate: src ∈ corrupted ∨ (isCorrect ∧ sent_false ∧ vote_once ∧ type_cond).
  rcases hgates v hv with hcorrupt | ⟨hcp, hsf, hvonce, hvcond⟩
  · -- corrupt at k → corrupt at k+1.
    left ; simp only [exec.drop, Nat.zero_add] at hcorrupt ⊢
    exact corrupted_step_mono n f input _ _ i hfire' src hcorrupt
  · by_cases hcp1 : isCorrect n (exec.drop (k + 1) e 0) src
    · apply Or.inr
      -- sent unchanged.
      have hsf' : ((exec.drop (k + 1) e 0).local_ src).sent dst .vote v = false := by
        rw [hsent_eq dst v] ; exact hsf
      -- vote-once preserved (voted unchanged).
      have hvonce' : ∀ w, ((exec.drop (k + 1) e 0).local_ src).voted w = true → w = v := by
        intro w hw
        simp only [exec.drop, Nat.zero_add] at hw
        rw [hvoted_unch w] at hw
        exact hvonce w (by simp only [exec.drop, Nat.zero_add] at hw ⊢ ; exact hw)
      -- type_cond preserved (echo counts and approved are monotone).
      simp only [exec.drop, Nat.zero_add] at hcp1 hsf' hvonce' hvcond ⊢
      refine ⟨hcp1, hsf', hvonce', ?_⟩
      cases v with
      | some b =>
        -- countEchoRecv monotone.
        have := countEchoRecv_persist n f input e hsafety src b
          (echoThreshold n f) k 1
          (by simp only [exec.drop, Nat.zero_add] ; exact hvcond)
        simp only [exec.drop, Nat.zero_add] at this ; exact this
      | none =>
        -- both approved monotone.
        obtain ⟨haf, hat⟩ := hvcond
        constructor
        · have := approved_persist n f input e hsafety src false k 1
            (by simp only [exec.drop, Nat.zero_add] ; exact haf)
          simp only [exec.drop, Nat.zero_add] at this ; exact this
        · have := approved_persist n f input e hsafety src true k 1
            (by simp only [exec.drop, Nat.zero_add] ; exact hat)
          simp only [exec.drop, Nat.zero_add] at this ; exact this
    · -- Corrupted at k+1: left disjunct.
      exact Or.inl (by simp only [exec.drop, Nat.zero_add, isCorrect, Classical.not_not] at hcp1 ⊢ ; exact hcp1)

/-! ## Generic fairness primitives -/

/-- If a gate for `send(src, dst, t, v)` is open at every step from `k₀`
    onward, `src` is correct at every step from `k` onward, and `sent dst t`
    is false at every step from `k` onward, then weak fairness derives a
    contradiction (the action eventually fires, setting sent = true). -/
private theorem wf_gate_always_open_contra (input : Fin n → Bool)
    (src dst : Fin n) (t : MsgType) (v : Val)
    (e : exec (State n))
    (hfair : bca_fairness n f input e) (k : Nat)
    (h_sf : ∀ d, ((exec.drop (k + d) e 0).local_ src).sent dst t v = false)
    (h_corr : ∀ d, isCorrect n (exec.drop (k + d) e 0) src)
    (k₀ : Nat) (hk₀ : k₀ ≥ k)
    (hgate_v : ∀ d, ((bca n f input).actions (.send src dst t v)).gate (e (k₀ + d))) :
    False := by
  obtain ⟨hwf_send_all, _, _⟩ := hfair
  have hwf := hwf_send_all src dst t v
  dsimp only [tlasimp_def] at hwf
  specialize hwf k₀
  have h_enabled : ∀ j, tla_enabled
      (fun s s' => isCorrect n s src ∧
        bca_action n f input (.send src dst t v) s s')
      (exec.drop j (exec.drop k₀ e)) := by
    intro j
    simp only [tla_enabled, state_pred, enabled, exec.drop, Nat.zero_add]
    have hg := hgate_v j
    have hc := h_corr (k₀ + j - k)
    simp only [exec.drop, Nat.zero_add] at hc
    rw [show k + (k₀ + j - k) = k₀ + j from by omega] at hc
    rw [show j + k₀ = k₀ + j from by omega]
    simp only [bca_action, GatedAction.fires]
    exact ⟨_, hc, hg, rfl⟩
  obtain ⟨j, hfires⟩ := hwf h_enabled
  simp only [exec.drop, Nat.zero_add] at hfires
  obtain ⟨_, hact⟩ := hfires
  simp only [bca_action, GatedAction.fires, bca] at hact
  obtain ⟨_, htrans⟩ := hact
  have hsent_true : ((e (1 + j + k₀)).local_ src).sent dst t v = true := by
    rw [htrans] ; simp
  have hsent_false := h_sf (1 + j + k₀ - k)
  simp only [exec.drop, Nat.zero_add] at hsent_false
  rw [show k + (1 + j + k₀ - k) = 1 + j + k₀ from by omega] at hsent_false
  exact absurd hsent_true (by rw [hsent_false] ; exact Bool.false_ne_true)

/-- Generic send fairness: any send action a correct sender is currently
    enabled to perform — and whose gate stays enabled while the sender
    is correct — eventually fires (or the sender becomes faulty).
    Postcondition uses the monotone `sent` flag.

    The `hmono` premise expresses gate stability over time, with no
    reference to sender correctness. This matches wf1's persistence step
    and is provable unconditionally for every BCA send gate (input is
    constant; counts and approved/voted flags only grow). -/
theorem wf_send (input : Fin n → Bool)
    (src dst : Fin n) (t : MsgType) (v : Val)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hmono : ∀ d,
      ((exec.drop (k + d) e 0).local_ src).sent dst t v = false →
      ((bca n f input).actions (.send src dst t v)).gate (exec.drop k e 0) →
      ((bca n f input).actions (.send src dst t v)).gate (exec.drop (k + d) e 0)) :
    isCorrect n (exec.drop k e 0) src →
    ((bca n f input).actions (.send src dst t v)).gate (exec.drop k e 0) →
    ∃ k', ((exec.drop (k + k') e 0).local_ src).sent dst t v = true
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) src := by
  intro hcorr hgate
  -- By contradiction: assume sent stays false and process stays correct.
  by_contra h_neg
  have h_sf : ∀ d, ((exec.drop (k + d) e 0).local_ src).sent dst t v = false := by
    intro d ; by_contra hsv
    apply h_neg
    exact ⟨d, Or.inl (by cases ((exec.drop (k + d) e 0).local_ src).sent dst t v <;> simp_all)⟩
  have h_corr : ∀ d, isCorrect n (exec.drop (k + d) e 0) src := by
    intro d ; by_contra hc ; apply h_neg ; exact ⟨d, Or.inr hc⟩
  -- By hmono, gate is open at every step from k (while sent stays false).
  have hgate_all : ∀ d, ((bca n f input).actions (.send src dst t v)).gate
      (exec.drop (k + d) e 0) := by
    intro d ; exact hmono d (h_sf d) hgate
  -- Apply wf_gate_always_open_contra: gate open forever → WF fires → contradiction.
  exact wf_gate_always_open_contra n f input src dst t v e hfair k
    h_sf h_corr k (Nat.le_refl k) (fun d => by
      have := hgate_all d ; simp only [exec.drop, Nat.zero_add] at this ; exact this)

/-- **Type-level weak fairness for send**: if all gates in `X` are open at
    step `k` and are preserved whenever the sender fires no type-`t`
    action, then eventually some value gets sent to `dst` (or the sender
    becomes faulty).

    **hmono** says: "if a process can send a message of type `t` for
    all values in `X`, and it does not send any message of type `t`,
    then it can still send a message of type `t` for all values in `X`."
    The condition "does not send" is encoded as: `sent dst' t w` is
    unchanged for every destination `dst'` and value `w`.

    The proof by contradiction establishes two cases:
    • If no type-`t` send ever fires: `hmono` + induction preserves
      every gate in `X`; weak fairness fires one to `dst`.
    • If a type-`t` send fires to another destination: the single-shot
      commit (`echoed`/`voted`) locks a value whose gate for `dst` is
      then permanently open; weak fairness fires it to `dst`. -/
theorem wf_send_type (input : Fin n → Bool)
    (src dst : Fin n) (t : MsgType) (X : Val → Prop)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hX : ∃ v, X v)
    (hgate : ∀ v, X v →
      ((bca n f input).actions (.send src dst t v)).gate (exec.drop k e 0))
    (hmono : ∀ d,
      (∀ v, X v →
        ((bca n f input).actions (.send src dst t v)).gate
          (exec.drop (k + d) e 0)) →
      (∀ dst' w, ((exec.drop (k + d + 1) e 0).local_ src).sent dst' t w =
                 ((exec.drop (k + d) e 0).local_ src).sent dst' t w) →
      (∀ v, X v →
        ((bca n f input).actions (.send src dst t v)).gate
          (exec.drop (k + d + 1) e 0)))
    (hcorr : isCorrect n (exec.drop k e 0) src) :
    ∃ k', (∃ v, ((exec.drop (k + k') e 0).local_ src).sent dst t v = true)
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) src := by
  --
  -- Classical contradiction: assume the conclusion never holds.
  by_contra h_neg
  -- h_neg : ¬∃ k', (∃ v, sent = true) ∨ ¬isCorrect
  -- Derive: at every future step, sent is false and src is correct.
  have h_sf : ∀ d v,
      ((exec.drop (k + d) e 0).local_ src).sent dst t v = false := by
    intro d v
    by_contra hsv
    apply h_neg
    exact ⟨d, Or.inl ⟨v, by cases ((exec.drop (k + d) e 0).local_ src).sent dst t v <;> simp_all⟩⟩
  have h_corr : ∀ d, isCorrect n (exec.drop (k + d) e 0) src := by
    intro d
    by_contra hc
    apply h_neg
    exact ⟨d, Or.inr hc⟩
  -- Case split: does src ever fire a type-t send (to any destination)?
  by_cases h_no_send : ∀ d dst' w,
      ((exec.drop (k + d + 1) e 0).local_ src).sent dst' t w =
      ((exec.drop (k + d) e 0).local_ src).sent dst' t w
  · /-  Case 1 — no type-t send from src ever fires.
        By hmono + induction every gate in X is preserved at every step.
        Pick v₀ ∈ X; weak fairness fires send(src, dst, t, v₀).
        The transition sets sent(dst, t, v₀) = true, contradicting h_sf. -/
    have hgate_all : ∀ d v, X v →
        ((bca n f input).actions (.send src dst t v)).gate
          (exec.drop (k + d) e 0) := by
      intro d ; induction d with
      | zero => simpa using hgate
      | succ d ih =>
        intro v hv
        rw [show k + (d + 1) = k + d + 1 from by omega]
        exact hmono d ih (h_no_send d) v hv
    obtain ⟨v₀, hv₀⟩ := hX
    exact wf_gate_always_open_contra n f input src dst t v₀ e hfair k
      (fun d => h_sf d v₀) h_corr k (Nat.le_refl k) (fun d => by
        have hg := hgate_all d v₀ hv₀
        simp only [exec.drop, Nat.zero_add] at hg ; exact hg)
  · /- Case 2 — a type-t send fires from src to some destination.
        If it targets dst: sent = true, contradicting h_sf.
        If it targets dst' ≠ dst: after the commit, echoed/voted locks
        a value v* whose gate for dst is permanently open. Weak fairness
        fires send(src, dst, t, v*), contradicting h_sf.
        This case requires BCA-specific single-shot reasoning. -/
    -- h_no_send is ¬∀ d dst' w, sent = sent. Negate to get ∃.
    have h_ex : ∃ d dst' w,
        ((exec.drop (k + d + 1) e 0).local_ src).sent dst' t w ≠
        ((exec.drop (k + d) e 0).local_ src).sent dst' t w := by
      by_contra hall
      apply h_no_send ; intro d dst' w
      by_contra hne
      apply hall ; exact ⟨d, dst', w, hne⟩
    obtain ⟨d₀, dst₀, w₀, h_sent_changed⟩ := h_ex
    -- The sent flag changed: some type-t send fired at step k + d₀.
    -- Since sent is monotone (false→true only), the new value is true.
    have h_sent_true : ((exec.drop (k + d₀ + 1) e 0).local_ src).sent
        dst₀ t w₀ = true := by
      cases h_old : ((exec.drop (k + d₀) e 0).local_ src).sent dst₀ t w₀ with
      | false =>
        -- was false, became different ⟹ must be true
        cases h_new : ((exec.drop (k + d₀ + 1) e 0).local_ src).sent dst₀ t w₀ with
        | false => exact absurd (h_old ▸ h_new ▸ rfl) h_sent_changed
        | true => rfl
      | true =>
        -- was true, monotonicity: sent only goes false→true, never true→false.
        obtain ⟨i, hfire⟩ := hsafety.2 (k + d₀)
        have hfire' : ((bca n f input).actions i).fires
            (e (k + d₀)) (e (k + d₀ + 1)) := by
          have := hfire
          simp only [exec.drop, Nat.zero_add] at this
          rwa [show 1 + (k + d₀) = k + d₀ + 1 from by omega] at this
        simp only [exec.drop, Nat.zero_add] at h_old ⊢
        exact sent_step_mono n f input _ _ i hfire' src dst₀ t w₀ h_old
    -- If dst₀ = dst: directly contradicts h_sf.
    by_cases hdst : dst₀ = dst
    · subst hdst
      exact absurd h_sent_true (by
        have := h_sf (d₀ + 1) w₀
        simp only [exec.drop, Nat.zero_add] at this ⊢
        rw [show k + (d₀ + 1) = k + d₀ + 1 from by omega] at this
        simp [this])
    · -- dst₀ ≠ dst: a type-t send fired from src to dst₀ at step k + d₀.
      -- Extract the action from safety and show it must be send(src, dst₀, t, w₀).
      obtain ⟨i, hfire⟩ := hsafety.2 (k + d₀)
      have hfire' : ((bca n f input).actions i).fires
          (e (k + d₀)) (e (k + d₀ + 1)) := by
        have := hfire
        simp only [exec.drop, Nat.zero_add] at this
        rwa [show 1 + (k + d₀) = k + d₀ + 1 from by omega] at this
      -- The action must be send(src, dst₀, t, w₀) because that's the only
      -- action that changes sent(dst₀, t, w₀) from false to true.
      -- Extract the gate conditions at step k + d₀.
      have h_old_false : ((e (k + d₀)).local_ src).sent dst₀ t w₀ = false := by
        cases hv : ((e (k + d₀)).local_ src).sent dst₀ t w₀ with
        | false => rfl
        | true =>
          -- If already true, sent_step_mono gives true at k+d₀+1, so
          -- sent didn't change — contradicting h_sent_changed.
          have h_still := sent_step_mono n f input _ _ i hfire' src dst₀ t w₀ hv
          simp only [exec.drop, Nat.zero_add] at h_sent_changed
          exact absurd (by rw [show k + d₀ + 1 = k + d₀ + 1 from rfl] at h_still
                           rw [hv, h_still]) h_sent_changed
      -- The action i changed sent(dst₀, t, w₀) from false to true.
      -- Case-split on i to show it must be send(src, dst₀, t, w₀)
      -- and extract the gate conditions.
      -- For any other action, sent is unchanged — contradiction.
      -- The action i changed sent(src, dst₀, t, w₀) from false to true.
      -- For any action other than send(src, dst₀, t, w₀), sent_step_mono
      -- would give sent = false in the next state — contradicting h_sent_true.
      -- So i must be send(src, dst₀, t, w₀), and its gate was open.
      -- The action i must be send(src, dst₀, t, w₀). Use sent_false_true_implies_send.
      obtain ⟨hgate_send, hfires_send⟩ :=
        sent_false_true_implies_send n f input _ _ i hfire' src dst₀ t w₀
          h_old_false
          (by simp only [exec.drop, Nat.zero_add] at h_sent_true ; exact h_sent_true)
      -- From hgate_send, extract the type-specific conditions.
      -- The gate is: src ∈ corrupted ∨ (isCorrect ∧ sent_false ∧ type_cond).
      have hcorr_d₀ := h_corr d₀
      simp only [exec.drop, Nat.zero_add] at hcorr_d₀
      have hgate_right := hgate_send.resolve_left (by
        exact hcorr_d₀)
      obtain ⟨_, _, htype_cond⟩ := hgate_right
      -- Sub-step 2: show gate(t, w₀) for dst is open at every step
      -- from k + d₀ + 1 onward.  The gate requires:
      --   (a) isCorrect — from h_corr
      --   (b) sent(dst, t, w₀) = false — from h_sf
      --   (c) type-specific condition — persists from htype_cond
      -- Then apply wf_contra.
      apply wf_gate_always_open_contra n f input src dst t w₀ e hfair k
        (fun d => h_sf d w₀) h_corr (k + d₀ + 1) (by omega)
      intro d
      -- Use send_gate_persist_across_commit.
      have hc_future := h_corr (d₀ + 1 + d)
      simp only [exec.drop, Nat.zero_add] at hc_future
      rw [show k + (d₀ + 1 + d) = k + d₀ + 1 + d from by omega] at hc_future
      have hsf_future := h_sf (d₀ + 1 + d) w₀
      simp only [exec.drop, Nat.zero_add] at hsf_future
      rw [show k + (d₀ + 1 + d) = k + d₀ + 1 + d from by omega] at hsf_future
      exact send_gate_persist_across_commit n f input src dst dst₀ t w₀ e hsafety
        (k + d₀) d hcorr_d₀ hc_future hsf_future hgate_send hfires_send

/-- Generic delivery fairness: any message in the buffer is eventually
    consumed by a `recv` action (which clears it from the buffer).
    Proved via `wf1` applied to the recv action. -/
theorem wf_recv (input : Fin n → Bool) (m : Message n)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat) :
    (exec.drop k e 0).buffer m = true →
    ∃ k', (exec.drop (k + k') e 0).buffer m = false := by
  intro hbuf_k
  obtain ⟨_, hwf_recv_all, _⟩ := hfair
  have hleads :=
    wf1 (state_pred (fun s => s.buffer m = true))
        (state_pred (fun s => s.buffer m = false))
        ((bca n f input).next)
        (bca_action n f input (.recv m.src m.dst m.type m.val))
        e
        ⟨by -- Persistence: p ∧ ⟨next⟩ ⇒ ◯p ∨ ◯q
            intro j
            dsimp only [tlasimp_def]
            intro ⟨hbuf, hnext_j⟩
            simp only [exec.drop, ActionSpec.next, GatedAction.fires,
              Nat.zero_add] at hbuf hnext_j ⊢
            obtain ⟨action, _, htrans⟩ := hnext_j
            cases action with
            | corrupt i =>
              left ; simp only [bca] at htrans ; rw [htrans] ; exact hbuf
            | send src dst t mv =>
              left ; simp only [bca] at htrans ; rw [htrans]
              simp only
              by_cases hm : m = ⟨src, dst, t, mv⟩
              · simp [hm]
              · simp [hm] ; exact hbuf
            | recv src dst t mv =>
              simp only [bca] at htrans
              by_cases hmeq : ({src := src, dst := dst, type := t, val := mv} : Message n) = m
              · right ; rw [htrans] ; simp
                rw [hmeq] ; simp
              · left ; rw [htrans] ; simp
                by_cases h : m = ⟨src, dst, t, mv⟩
                · exact absurd h.symm hmeq
                · simp [h] ; exact hbuf
            | decide i mv =>
              left ; simp only [bca] at htrans ; rw [htrans] ; exact hbuf,
         by -- Progress: p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯q
            intro j
            dsimp only [tlasimp_def]
            intro ⟨_, _, ha⟩
            simp only [exec.drop, bca_action, GatedAction.fires, Nat.zero_add] at ha ⊢
            obtain ⟨_, htrans⟩ := ha
            simp only [bca] at htrans
            rw [htrans] ; simp,
         by -- Enabledness: p ⇒ Enabled a ∨ q
            intro j
            dsimp only [tlasimp_def]
            intro hbuf ; left
            simp only [tla_enabled, enabled, state_pred, exec.drop,
              bca_action, GatedAction.fires, bca, Nat.zero_add] at hbuf ⊢
            exact ⟨_, hbuf, rfl⟩,
         hsafety.2,
         hwf_recv_all m.src m.dst m.type m.val⟩
  -- Extract the ∃ k' from the leads_to at step k.
  have := hleads k hbuf_k
  obtain ⟨k', hq⟩ := this
  refine ⟨k', ?_⟩
  simp only [state_pred, exec.drop_drop] at hq
  exact hq

/-- Generic decide fairness: if the `.decide i v` gate is enabled at a
    correct process `i` and stays enabled while `i` has not yet decided
    *and remains correct*, then `i` eventually has `decided = some _`.
    The `hmono` premise takes both `isCorrect i at k+d` and
    `decided = none at k+d` as "p still holds" witnesses. -/
theorem wf_decide (input : Fin n → Bool)
    (i : Fin n) (v : Val)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hmono : ∀ d,
      isCorrect n (exec.drop (k + d) e 0) i →
      ((exec.drop (k + d) e 0).local_ i).decided = none →
      ((bca n f input).actions (.decide i v)).gate (exec.drop k e 0) →
      ((bca n f input).actions (.decide i v)).gate (exec.drop (k + d) e 0)) :
    isCorrect n (exec.drop k e 0) i →
    ((bca n f input).actions (.decide i v)).gate (exec.drop k e 0) →
    ∃ k', (∃ v', ((exec.drop (k + k') e 0).local_ i).decided = some v')
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) i := by
  intro hcorr hgate
  obtain ⟨_, _, hwf_decide_all⟩ := hfair
  -- By contradiction: assume decided never becomes some and process stays correct.
  by_contra h_neg
  have h_none : ∀ d, ((exec.drop (k + d) e 0).local_ i).decided = none := by
    intro d ; by_contra hd
    apply h_neg
    cases hv : ((exec.drop (k + d) e 0).local_ i).decided with
    | none => exact absurd hv hd
    | some v' => exact ⟨d, Or.inl ⟨v', hv⟩⟩
  have h_corr : ∀ d, isCorrect n (exec.drop (k + d) e 0) i := by
    intro d ; by_contra hc ; apply h_neg ; exact ⟨d, Or.inr hc⟩
  -- By hmono, gate is open at every step from k.
  have hgate_all : ∀ d, ((bca n f input).actions (.decide i v)).gate
      (exec.drop (k + d) e 0) := by
    intro d ; exact hmono d (h_corr d) (h_none d) hgate
  -- Apply 𝒲ℱ for decide(i, v). Same technique as wf_gate_always_open_contra.
  have hwf := hwf_decide_all i v
  dsimp only [tlasimp_def] at hwf
  specialize hwf k
  have h_enabled : ∀ j, tla_enabled
      (bca_action n f input (.decide i v))
      (exec.drop j (exec.drop k e)) := by
    intro j
    simp only [tla_enabled, state_pred, enabled, exec.drop, Nat.zero_add]
    have hg := hgate_all j
    simp only [exec.drop, Nat.zero_add] at hg
    rw [show j + k = k + j from by omega]
    simp only [bca_action, GatedAction.fires]
    exact ⟨_, hg, rfl⟩
  obtain ⟨j, hfires⟩ := hwf h_enabled
  simp only [exec.drop, Nat.zero_add] at hfires
  simp only [bca_action, GatedAction.fires, bca] at hfires
  obtain ⟨_, htrans⟩ := hfires
  -- The transition sets decided = some v.
  have hdec : ((e (1 + j + k)).local_ i).decided = some v := by
    rw [htrans] ; simp
  -- But h_none says decided = none at every step.
  have hdec_none := h_none (1 + j + k - k)
  simp only [exec.drop, Nat.zero_add] at hdec_none
  rw [show k + (1 + j + k - k) = 1 + j + k from by omega] at hdec_none
  rw [hdec_none] at hdec ; exact absurd hdec (by simp)

/-! ## Generic delivery chain -/

/-- Generic delivery chain: combines `wf_send` + per-type tracking bridge
    + `wf_recv` + per-type buffer-clear bridge into a single
    "if it can be sent, it gets delivered to the receiver's slot"
    lemma. The "received" predicate is abstract and the two bridges are
    passed in as premises, so this lemma is reusable for init / echo /
    vote with the appropriate per-type bridges. -/
theorem wf_chain (input : Fin n → Bool)
    (src dst : Fin n) (t : MsgType) (v : Val)
    (received : State n → Prop)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hmono : ∀ d,
      ((exec.drop (k + d) e 0).local_ src).sent dst t v = false →
      ((bca n f input).actions (.send src dst t v)).gate (exec.drop k e 0) →
      ((bca n f input).actions (.send src dst t v)).gate (exec.drop (k + d) e 0))
    (htracking : ∀ j, ((exec.drop j e 0).local_ src).sent dst t v = true →
      (exec.drop j e 0).buffer ⟨src, dst, t, v⟩ = true ∨ received (exec.drop j e 0))
    (hcleared : ∀ j d, (exec.drop j e 0).buffer ⟨src, dst, t, v⟩ = true →
      (exec.drop (j + d) e 0).buffer ⟨src, dst, t, v⟩ = false →
      received (exec.drop (j + d) e 0)) :
    isCorrect n (exec.drop k e 0) src →
    ((bca n f input).actions (.send src dst t v)).gate (exec.drop k e 0) →
    ∃ k', received (exec.drop (k + k') e 0)
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) src := by
  intro hcorr hgate
  obtain ⟨k1, hsent_or⟩ :=
    wf_send n f input src dst t v e hsafety hfair k hmono hcorr hgate
  rcases hsent_or with hsent | hnc
  · rcases htracking (k + k1) hsent with hbuf | hrcv
    · obtain ⟨k2, hbuf_clear⟩ :=
        wf_recv n f input ⟨src, dst, t, v⟩ e hsafety hfair (k + k1) hbuf
      refine ⟨k1 + k2, Or.inl ?_⟩
      rw [show k + (k1 + k2) = (k + k1) + k2 from by omega]
      exact hcleared (k + k1) k2 hbuf hbuf_clear
    · exact ⟨k1, Or.inl hrcv⟩
  · exact ⟨k1, Or.inr hnc⟩

/-- Type-level delivery chain: combines `wf_send_type` + per-value tracking
    + `wf_recv` + per-value buffer-clearing.  Like `wf_chain` but the value
    sent is chosen by the protocol (existentially quantified in the
    conclusion), not fixed by the caller.  The `received` predicate is
    parameterized by the value that was actually sent. -/
theorem wf_chain_type (input : Fin n → Bool)
    (src dst : Fin n) (t : MsgType) (X : Val → Prop)
    (received : Val → State n → Prop)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hmono : ∀ d,
      (∀ v, X v →
        ((bca n f input).actions (.send src dst t v)).gate
          (exec.drop (k + d) e 0)) →
      (∀ dst' w, ((exec.drop (k + d + 1) e 0).local_ src).sent dst' t w =
                 ((exec.drop (k + d) e 0).local_ src).sent dst' t w) →
      (∀ v, X v →
        ((bca n f input).actions (.send src dst t v)).gate
          (exec.drop (k + d + 1) e 0)))
    (htracking : ∀ v j,
      isCorrect n (exec.drop j e 0) src →
      ((exec.drop j e 0).local_ src).sent dst t v = true →
      (exec.drop j e 0).buffer ⟨src, dst, t, v⟩ = true ∨ received v (exec.drop j e 0))
    (hcleared : ∀ v j d,
      isCorrect n (exec.drop j e 0) src →
      (exec.drop j e 0).buffer ⟨src, dst, t, v⟩ = true →
      (exec.drop (j + d) e 0).buffer ⟨src, dst, t, v⟩ = false →
      received v (exec.drop (j + d) e 0)) :
    isCorrect n (exec.drop k e 0) src →
    (∃ v, X v) →
    (∀ v, X v → ((bca n f input).actions (.send src dst t v)).gate (exec.drop k e 0)) →
    ∃ k', (∃ v, received v (exec.drop (k + k') e 0))
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) src := by
  intro hcorr hX hgate
  obtain ⟨k1, hsent_or⟩ :=
    wf_send_type n f input src dst t X e hsafety hfair k hX hgate hmono hcorr
  rcases hsent_or with ⟨v, hsent⟩ | hnc
  · -- sent dst t v = true at step k + k₁.
    -- Either src is still correct (use tracking) or corrupt (return right disjunct).
    by_cases hc1 : isCorrect n (exec.drop (k + k1) e 0) src
    · rcases htracking v (k + k1) hc1 hsent with hbuf | hrcv
      · obtain ⟨k2, hbuf_clear⟩ :=
          wf_recv n f input ⟨src, dst, t, v⟩ e hsafety hfair (k + k1) hbuf
        refine ⟨k1 + k2, Or.inl ⟨v, ?_⟩⟩
        rw [show k + (k1 + k2) = (k + k1) + k2 from by omega]
        exact hcleared v (k + k1) k2 hc1 hbuf hbuf_clear
      · exact ⟨k1, Or.inl ⟨v, hrcv⟩⟩
    · exact ⟨k1, Or.inr hc1⟩
  · exact ⟨k1, Or.inr hnc⟩

/-- Generic multi-sender / one-receiver combine. Given a per-sender
    delivery primitive `hdel` and a per-sender persistence primitive
    `hpersist` for the "received" predicate, builds a single step `k`
    after which every sender in the list `l` has either delivered to
    the receiver or become faulty. -/
theorem combine_senders (input : Fin n → Bool)
    (received : Fin n → State n → Prop)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e)
    (hdel : ∀ p (k : Nat), ∃ k', received p (exec.drop (k + k') e 0)
              ∨ ¬isCorrect n (exec.drop (k + k') e 0) p)
    (hpersist : ∀ p (j d : Nat),
      received p (exec.drop j e 0) → received p (exec.drop (j + d) e 0))
    (l : List (Fin n)) (k : Nat) :
    ∃ k', ∀ p ∈ l, received p (exec.drop (k + k') e 0)
                    ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
  induction l with
  | nil => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | cons p₀ ps ih =>
    obtain ⟨k', hps⟩ := ih
    obtain ⟨k₀, hp₀⟩ := hdel p₀ (k + k')
    refine ⟨k' + k₀, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [show k + (k' + k₀) = (k + k') + k₀ from by omega] ; exact hp₀
    · rcases hps p hp' with hir | hnc
      · left
        rw [show k + (k' + k₀) = (k + k') + k₀ from by omega]
        exact hpersist p (k + k') k₀ hir
      · right
        rw [show k + (k' + k₀) = (k + k') + k₀ from by omega]
        exact isCorrect_persist n f input e hsafety p (k + k') k₀ hnc

/-- Generic multi-sender / multi-receiver combine. Given a per-(sender,
    receiver) delivery primitive and persistence primitive, builds a
    single step `k` after which every sender in `senders` has delivered
    to every receiver in `receivers` (or become faulty). -/
theorem combine_senders_receivers (input : Fin n → Bool)
    (received : Fin n → Fin n → State n → Prop)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e)
    (hdel : ∀ p r (k : Nat), ∃ k', received p r (exec.drop (k + k') e 0)
              ∨ ¬isCorrect n (exec.drop (k + k') e 0) p)
    (hpersist : ∀ p r (j d : Nat),
      received p r (exec.drop j e 0) → received p r (exec.drop (j + d) e 0))
    (senders receivers : List (Fin n)) (k : Nat) :
    ∃ k', ∀ r ∈ receivers, ∀ p ∈ senders,
            received p r (exec.drop (k + k') e 0)
              ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
  induction receivers with
  | nil => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | cons r₀ rs ih =>
    obtain ⟨k', hall'⟩ := ih
    -- Get senders → r₀ at step k+k'
    obtain ⟨k₀, hr₀⟩ := combine_senders n f input (received · r₀)
      e hsafety hfair (fun p k => hdel p r₀ k)
      (fun p j d => hpersist p r₀ j d) senders (k + k')
    refine ⟨k' + k₀, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr'
    · intro p hp
      rw [show k + (k' + k₀) = (k + k') + k₀ from by omega]
      exact hr₀ p hp
    · intro p hp
      rcases hall' r hr' p hp with hir | hnc
      · left
        rw [show k + (k' + k₀) = (k + k') + k₀ from by omega]
        exact hpersist p r (k + k') k₀ hir
      · right
        rw [show k + (k' + k₀) = (k + k') + k₀ from by omega]
        exact isCorrect_persist n f input e hsafety p (k + k') k₀ hnc

/-! ## Specialisation lemmas -/

/-- Every correct sender's `init(input p)` is eventually delivered to every
    `q` (or the sender becomes faulty first). Now an instance of `wf_chain`
    with the init-specific bridges. -/
theorem init_delivery_correct_sender (input : Fin n → Bool)
    (p q : Fin n)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e)
    (k : Nat) :
    ∃ k', ((exec.drop (k + k') e 0).local_ q).initRecv p (input p) = true
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
  by_cases hcp : isCorrect n (exec.drop k e 0) p
  · -- Case-split on whether p has already sent `init (input p)` to q.
    by_cases hsent_now :
        ((exec.drop k e 0).local_ p).sent q .init (some (input p)) = true
    · -- Already sent: use msg_tracking + wf_recv bridges directly.
      rcases init_msg_tracking n f input e hsafety k p q (input p) hsent_now with hbuf | hir
      · obtain ⟨k', hbuf_clear⟩ :=
          wf_recv n f input ⟨p, q, .init, some (input p)⟩ e hsafety hfair k hbuf
        refine ⟨k', Or.inl ?_⟩
        exact init_buffer_cleared n f input e hsafety p q (input p) k k' hbuf hbuf_clear
      · exact ⟨0, Or.inl (by simpa using hir)⟩
    · -- Not yet sent: fire wf_chain with the trivial init gate.
      have hsent_false : ((exec.drop k e 0).local_ p).sent q .init (some (input p)) = false := by
        cases h : ((exec.drop k e 0).local_ p).sent q .init (some (input p))
        · rfl
        · exact absurd h hsent_now
      exact wf_chain n f input p q .init (some (input p))
        (fun s => (s.local_ q).initRecv p (input p) = true)
        e hsafety hfair k
        (fun d hsf _ =>
          init_send_gate_trivial n f input p q (exec.drop (k + d) e 0) hsf)
        (fun j hsent => init_msg_tracking n f input e hsafety j p q (input p) hsent)
        (fun j d hbuf hbuf' => init_buffer_cleared n f input e hsafety p q (input p) j d hbuf hbuf')
        hcp
        (init_send_gate_trivial n f input p q (exec.drop k e 0) hsent_false)
  · exact ⟨0, Or.inr (by simpa using hcp)⟩

/-- Init delivery triggered by a witness in some peer's `initRecv`:
    if at step `k` some process `p` already has `p.initRecv s b = true`,
    then `s` will eventually deliver `init(b)` to every receiver `r`
    (or `s` becomes faulty first). Wraps `wf_chain` with the init bridges
    and `init_send_gate_persist`. Used to propagate `init(b)` outward
    from the `initRecv` frontier of a process that has already approved. -/
theorem init_delivery_from_initRecv (input : Fin n → Bool)
    (p s r : Fin n) (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e)
    (k : Nat)
    (hir : ((exec.drop k e 0).local_ p).initRecv s b = true) :
    ∃ k', ((exec.drop (k + k') e 0).local_ r).initRecv s b = true
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) s := by
  by_cases hcs : isCorrect n (exec.drop k e 0) s
  · -- s correct at k. Case-split on whether s has already sent init(b) to r.
    by_cases hsent_now :
        ((exec.drop k e 0).local_ s).sent r .init (some b) = true
    · -- Already sent: bypass wf_send, use msg_tracking + wf_recv directly.
      rcases init_msg_tracking n f input e hsafety k s r b hsent_now with hbuf | hir_r
      · obtain ⟨k', hbuf_clear⟩ :=
          wf_recv n f input ⟨s, r, .init, some b⟩ e hsafety hfair k hbuf
        refine ⟨k', Or.inl ?_⟩
        exact init_buffer_cleared n f input e hsafety s r b k k' hbuf hbuf_clear
      · exact ⟨0, Or.inl (by simpa using hir_r)⟩
    · -- Not yet sent: build the full gate and fire wf_chain.
      have hsent_false : ((exec.drop k e 0).local_ s).sent r .init (some b) = false := by
        cases h : ((exec.drop k e 0).local_ s).sent r .init (some b)
        · rfl
        · exact absurd h hsent_now
      have hhonest := correct_initRecv_implies_honest_cond n f input e hsafety k s p b hcs hir
      have hgate : ((bca n f input).actions (.send s r .init (some b))).gate
          (exec.drop k e 0) :=
        Or.inr ⟨hcs, hsent_false, hhonest⟩
      have hmono : ∀ d,
          ((exec.drop (k + d) e 0).local_ s).sent r .init (some b) = false →
          ((bca n f input).actions (.send s r .init (some b))).gate (exec.drop k e 0) →
          ((bca n f input).actions (.send s r .init (some b))).gate (exec.drop (k + d) e 0) :=
        fun d hsent_false =>
          init_send_gate_persist n f input e hsafety s r p b k d hir hsent_false
      exact wf_chain n f input s r .init (some b)
        (fun state => (state.local_ r).initRecv s b = true)
        e hsafety hfair k hmono
        (fun j hsent => init_msg_tracking n f input e hsafety j s r b hsent)
        (fun j d hbuf hbuf' => init_buffer_cleared n f input e hsafety s r b j d hbuf hbuf')
        hcs hgate
  · -- s already faulty at k
    exact ⟨0, Or.inr (by simpa using hcs)⟩

/-- Amplify-init delivery: if `p` has crossed the amplify threshold for
    `b` at step `k`, then `init(b)` is eventually delivered to every
    receiver `q` (or `p` becomes faulty first). Instance of `wf_chain`
    with the amplify-gate bridge. -/
theorem amplify_init_delivery (input : Fin n → Bool)
    (p q : Fin n) (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e)
    (k : Nat)
    (hcount : countInitRecv n ((exec.drop k e 0).local_ p) b ≥ f + 1) :
    ∃ k', ((exec.drop (k + k') e 0).local_ q).initRecv p b = true
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
  by_cases hcp : isCorrect n (exec.drop k e 0) p
  · -- Case-split on whether p has already sent `init (some b)` to q.
    by_cases hsent_now :
        ((exec.drop k e 0).local_ p).sent q .init (some b) = true
    · rcases init_msg_tracking n f input e hsafety k p q b hsent_now with hbuf | hir
      · obtain ⟨k', hbuf_clear⟩ :=
          wf_recv n f input ⟨p, q, .init, some b⟩ e hsafety hfair k hbuf
        refine ⟨k', Or.inl ?_⟩
        exact init_buffer_cleared n f input e hsafety p q b k k' hbuf hbuf_clear
      · exact ⟨0, Or.inl (by simpa using hir)⟩
    · have hsent_false : ((exec.drop k e 0).local_ p).sent q .init (some b) = false := by
        cases h : ((exec.drop k e 0).local_ p).sent q .init (some b)
        · rfl
        · exact absurd h hsent_now
      exact wf_chain n f input p q .init (some b)
        (fun s => (s.local_ q).initRecv p b = true)
        e hsafety hfair k
        (fun d hsf _ =>
          init_send_gate_amplify n f input p q b (exec.drop (k + d) e 0) hsf
            (countInitRecv_persist n f input e hsafety p b (f + 1) k d hcount))
        (fun j hsent => init_msg_tracking n f input e hsafety j p q b hsent)
        (fun j d hbuf hbuf' => init_buffer_cleared n f input e hsafety p q b j d hbuf hbuf')
        hcp
        (init_send_gate_amplify n f input p q b (exec.drop k e 0) hsent_false hcount)
  · exact ⟨0, Or.inr (by simpa using hcp)⟩

/-- Echo delivery from approved: if a correct `p` has `approved b` at
    step `k`, then eventually `echo(b')` (for some `b'`) is delivered
    to every receiver `q` (or `p` becomes faulty first). Echo-analog
    of `init_delivery_from_initRecv`: case-splits on whether `p` has
    already committed an echo value (`echoed`), and on whether the
    specific send has already fired. -/
theorem echo_delivery_from_approved (input : Fin n → Bool)
    (p q : Fin n) (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e)
    (k : Nat)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (happ : ((exec.drop k e 0).local_ p).approved b = true) :
    ∃ k', (∃ b', ((exec.drop (k + k') e 0).local_ q).echoRecv p b' = true)
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
  -- Determine the value `b'` that `p` will echo: either the one already
  -- committed (`echoed = some b'`) or `b` itself if not yet echoed.
  let b' : Bool :=
    match ((exec.drop k e 0).local_ p).echoed with
    | some v => v
    | none => b
  -- p.approved b' holds: either via echoed_implies_approved (echoed = some b')
  -- or directly from happ (echoed = none → b' = b).
  have happ_b' : ((exec.drop k e 0).local_ p).approved b' = true := by
    show ((exec.drop k e 0).local_ p).approved
      (match ((exec.drop k e 0).local_ p).echoed with | some v => v | none => b) = true
    cases hecho : ((exec.drop k e 0).local_ p).echoed with
    | some v =>
      simp
      exact echoed_implies_approved n f input e hsafety k p v hcp hecho
    | none => simp; exact happ
  have hecho_ok : ((exec.drop k e 0).local_ p).echoed = none ∨
      ((exec.drop k e 0).local_ p).echoed = some b' := by
    show ((exec.drop k e 0).local_ p).echoed = none ∨
      ((exec.drop k e 0).local_ p).echoed = some
        (match ((exec.drop k e 0).local_ p).echoed with | some v => v | none => b)
    cases hecho : ((exec.drop k e 0).local_ p).echoed with
    | some v => right ; rfl
    | none => left ; rfl
  -- Now case-split on whether p has already sent echo(b') to q.
  by_cases hsent_now :
      ((exec.drop k e 0).local_ p).sent q .echo (some b') = true
  · -- Already sent: use echo_msg_tracking + wf_recv directly.
    rcases echo_msg_tracking n f input e hsafety k p q b' hsent_now with hbuf | her
    · obtain ⟨k', hbuf_clear⟩ :=
        wf_recv n f input ⟨p, q, .echo, some b'⟩ e hsafety hfair k hbuf
      refine ⟨k', Or.inl ⟨b', ?_⟩⟩
      exact echo_buffer_cleared n f input e hsafety p q b' k k' hbuf hbuf_clear
    · exact ⟨0, Or.inl ⟨b', by simpa using her⟩⟩
  · -- Not yet sent: fire wf_chain_type with the echo gate.
    -- X = set of echo values whose gate is open at step k.
    let X : Val → Prop := fun w =>
      ∃ bv, w = some bv ∧
        ((exec.drop k e 0).local_ p).approved bv = true ∧
        (((exec.drop k e 0).local_ p).echoed = none ∨
         ((exec.drop k e 0).local_ p).echoed = some bv)
    have hX : ∃ v, X v := ⟨some b', b', rfl, happ_b', hecho_ok⟩
    have hgate_all : ∀ v, X v →
        ((bca n f input).actions (.send p q .echo v)).gate (exec.drop k e 0) := by
      intro v hv
      obtain ⟨bv, rfl, happ_bv, hecho_bv⟩ := hv
      apply Or.inr
      refine ⟨hcp, ?_, happ_bv, hecho_bv⟩
      -- sent q echo (some bv) = false.
      -- If sent were true, sent_echo_implies_echoed gives echoed = some bv.
      -- From hecho_ok: echoed = none ∨ echoed = some b'.
      -- Case echoed = none: contradicts echoed = some bv.
      -- Case echoed = some b': then bv = b', so sent q echo (some b') = true,
      --   contradicting hsent_now.
      by_contra hsent_bv
      have hsent_true : ((exec.drop k e 0).local_ p).sent q .echo (some bv) = true := by
        cases h : ((exec.drop k e 0).local_ p).sent q .echo (some bv) <;> simp_all
      have hechoed := sent_echo_implies_echoed n f input e hsafety k p q bv hcp hsent_true
      rcases hecho_ok with hnone | hsome
      · rw [hnone] at hechoed ; exact absurd hechoed (by simp)
      · rw [hsome] at hechoed ; injection hechoed with h
        subst h ; exact hsent_now hsent_true
    -- Type-level hmono via echo_send_gate_type_persist.
    have hmono_type : ∀ d,
        (∀ v, X v → ((bca n f input).actions (.send p q .echo v)).gate
          (exec.drop (k + d) e 0)) →
        (∀ dst' w, ((exec.drop (k + d + 1) e 0).local_ p).sent dst' MsgType.echo w =
                   ((exec.drop (k + d) e 0).local_ p).sent dst' MsgType.echo w) →
        (∀ v, X v → ((bca n f input).actions (.send p q .echo v)).gate
          (exec.drop (k + d + 1) e 0)) := by
      intro d hg hs
      rw [show k + d + 1 = k + d + 1 from rfl] at hs
      exact echo_send_gate_type_persist n f input e hsafety p q X (k + d) hg
        (by rwa [show k + d + 1 = k + d + 1 from rfl])
    obtain ⟨k', hres⟩ := wf_chain_type n f input p q .echo X
      (fun v state => match v with
        | some bv => (state.local_ q).echoRecv p bv = true
        | none => False)
      e hsafety hfair k hmono_type
      (fun v j hcj hsent => by
        cases v with
        | none =>
          exact absurd hsent (by
            rw [sent_echo_none_false_correct n f input e hsafety j p q hcj]
            exact Bool.false_ne_true)
        | some bv => exact echo_msg_tracking n f input e hsafety j p q bv hsent)
      (fun v j d hcj hbuf hbuf' => by
        cases v with
        | none =>
          exact absurd hbuf (by
            rw [buffer_echo_none_false_correct n f input e hsafety j p q hcj]
            exact Bool.false_ne_true)
        | some bv => exact echo_buffer_cleared n f input e hsafety p q bv j d hbuf hbuf')
      hcp hX hgate_all
    rcases hres with ⟨v, hrcv⟩ | hnc
    · cases v with
      | none => exact absurd hrcv (by simp)
      | some bv => exact ⟨k', Or.inl ⟨bv, hrcv⟩⟩
    · exact ⟨k', Or.inr hnc⟩

/-- Vote delivery from a ready-to-vote premise: if at step `k` a correct
    `p` has either (A) an echo quorum for some `b` or (B) both values
    approved, then eventually some vote is delivered to every receiver
    `q` (or `p` becomes faulty first). The value delivered is determined
    by `p`'s current `voted` state (vote-once) with a fallback to `hready`
    when `p` has not yet voted. -/
theorem vote_delivery_from_ready (input : Fin n → Bool) (hn : n > 3 * f)
    (p q : Fin n)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e)
    (k : Nat)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (hready :
      (∃ b, countEchoRecv n ((exec.drop k e 0).local_ p) b ≥ n - f) ∨
      (((exec.drop k e 0).local_ p).approved false = true ∧
       ((exec.drop k e 0).local_ p).approved true = true)) :
    ∃ k', (∃ v, ((exec.drop (k + k') e 0).local_ q).voteRecv p v = true)
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
  -- Type-level delivery: given X with gates open, fire wf_chain_type.
  have deliver_type :
      ∀ (X : Val → Prop),
        (∃ v, X v) →
        (∀ v, X v → ((bca n f input).actions (.send p q .vote v)).gate (exec.drop k e 0)) →
        ∃ k', (∃ v, ((exec.drop (k + k') e 0).local_ q).voteRecv p v = true)
              ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
    intro X hXne hXgate
    -- Type-level hmono via vote_send_gate_type_persist.
    have hmono_vote : ∀ d,
        (∀ v, X v → ((bca n f input).actions (.send p q .vote v)).gate
          (exec.drop (k + d) e 0)) →
        (∀ dst' w, ((exec.drop (k + d + 1) e 0).local_ p).sent dst' MsgType.vote w =
                   ((exec.drop (k + d) e 0).local_ p).sent dst' MsgType.vote w) →
        (∀ v, X v → ((bca n f input).actions (.send p q .vote v)).gate
          (exec.drop (k + d + 1) e 0)) := by
      intro d hg hs
      exact vote_send_gate_type_persist n f input e hsafety p q X (k + d) hg
        (by rwa [show k + d + 1 = k + d + 1 from rfl])
    obtain ⟨k', hres⟩ := wf_chain_type n f input p q .vote X
      (fun v state => (state.local_ q).voteRecv p v = true)
      e hsafety hfair k hmono_vote
      (fun v j _hcj hsent => vote_msg_tracking n f input e hsafety j p q v hsent)
      (fun v j d _hcj hbuf hbuf' => vote_buffer_cleared n f input e hsafety p q v j d hbuf hbuf')
      hcp hXne hXgate
    exact ⟨k', hres⟩
  -- Dispatch-via-existing-sent: if p has already sent some vote to q,
  -- bypass wf_send via vote_msg_tracking.
  have already_sent :
      ∀ (v : Val),
        ((exec.drop k e 0).local_ p).sent q .vote v = true →
        ∃ k', (((exec.drop (k + k') e 0).local_ q).voteRecv p v = true)
              ∨ ¬isCorrect n (exec.drop (k + k') e 0) p := by
    intro v hsent_now
    rcases vote_msg_tracking n f input e hsafety k p q v hsent_now with hbuf | hvr
    · obtain ⟨k', hbuf_clear⟩ :=
        wf_recv n f input ⟨p, q, .vote, v⟩ e hsafety hfair k hbuf
      exact ⟨k', Or.inl (vote_buffer_cleared n f input e hsafety p q v k k' hbuf hbuf_clear)⟩
    · exact ⟨0, Or.inl (by simpa using hvr)⟩
  -- Case-split on p's current `voted` state: either already committed to
  -- some value `w`, or not yet voted (use hready to pick).
  by_cases hvf : ((exec.drop k e 0).local_ p).voted (some false) = true
  · -- Committed to vote (some false). Target v = some false.
    have hq : countEchoRecv n ((exec.drop k e 0).local_ p) false ≥ n - f :=
      voted_binary_implies_echo_quorum n f input hn e hsafety k p false hcp hvf
    have hvote_once : ∀ w, ((exec.drop k e 0).local_ p).voted w = true → w = some false := by
      intro w hvw
      exact (voted_unique n f input e hsafety k p w (some false) hcp hvw hvf)
    -- Deliver target (some false)
    by_cases hsent_now :
        ((exec.drop k e 0).local_ p).sent q .vote (some false) = true
    · obtain ⟨k', h⟩ := already_sent (some false) hsent_now
      rcases h with hvr | hnc
      · exact ⟨k', Or.inl ⟨some false, hvr⟩⟩
      · exact ⟨k', Or.inr hnc⟩
    · have hsent_false : ((exec.drop k e 0).local_ p).sent q .vote (some false) = false := by
        cases h : ((exec.drop k e 0).local_ p).sent q .vote (some false)
        · rfl
        · exact absurd h hsent_now
      have hgate := vote_send_gate_from_echo_quorum n f input p q false (exec.drop k e 0)
        hcp hsent_false hq hvote_once
      exact deliver_type (fun w => w = some false) ⟨_, rfl⟩
        (fun w hw => by subst hw ; exact hgate)
  · by_cases hvt : ((exec.drop k e 0).local_ p).voted (some true) = true
    · -- Committed to vote (some true). Target v = some true.
      have hq : countEchoRecv n ((exec.drop k e 0).local_ p) true ≥ n - f :=
        voted_binary_implies_echo_quorum n f input hn e hsafety k p true hcp hvt
      have hvote_once : ∀ w, ((exec.drop k e 0).local_ p).voted w = true → w = some true := by
        intro w hvw
        exact (voted_unique n f input e hsafety k p w (some true) hcp hvw hvt)
      by_cases hsent_now :
          ((exec.drop k e 0).local_ p).sent q .vote (some true) = true
      · obtain ⟨k', h⟩ := already_sent (some true) hsent_now
        rcases h with hvr | hnc
        · exact ⟨k', Or.inl ⟨some true, hvr⟩⟩
        · exact ⟨k', Or.inr hnc⟩
      · have hsent_false : ((exec.drop k e 0).local_ p).sent q .vote (some true) = false := by
          cases h : ((exec.drop k e 0).local_ p).sent q .vote (some true)
          · rfl
          · exact absurd h hsent_now
        have hgate := vote_send_gate_from_echo_quorum n f input p q true (exec.drop k e 0)
          hcp hsent_false hq hvote_once
        exact deliver_type (fun w => w = some true) ⟨_, rfl⟩
          (fun w hw => by subst hw ; exact hgate)
    · by_cases hvn : ((exec.drop k e 0).local_ p).voted none = true
      · -- Committed to vote none. Target v = none.
        obtain ⟨happ_f, happ_t⟩ :=
          voted_none_implies_both_approved n f input e hsafety k p hcp hvn
        have hvote_once : ∀ w, ((exec.drop k e 0).local_ p).voted w = true → w = none := by
          intro w hvw
          exact (voted_unique n f input e hsafety k p w none hcp hvw hvn)
        by_cases hsent_now :
            ((exec.drop k e 0).local_ p).sent q .vote none = true
        · obtain ⟨k', h⟩ := already_sent none hsent_now
          rcases h with hvr | hnc
          · exact ⟨k', Or.inl ⟨none, hvr⟩⟩
          · exact ⟨k', Or.inr hnc⟩
        · have hsent_false : ((exec.drop k e 0).local_ p).sent q .vote none = false := by
            cases h : ((exec.drop k e 0).local_ p).sent q .vote none
            · rfl
            · exact absurd h hsent_now
          have hgate := vote_send_gate_from_both_approved n f input p q (exec.drop k e 0)
            hcp hsent_false happ_f happ_t hvote_once
          exact deliver_type (fun w => w = none) ⟨_, rfl⟩
            (fun w hw => by subst hw ; exact hgate)
      · -- Not yet voted anything. Use hready to pick.
        have hvote_once_vacuous :
            ∀ v_tgt : Val, ∀ w,
              ((exec.drop k e 0).local_ p).voted w = true → w = v_tgt := by
          intro v_tgt w hvw
          cases w with
          | none => exact absurd hvw hvn
          | some b => cases b
                      · exact absurd hvw hvf
                      · exact absurd hvw hvt
        rcases hready with ⟨b, hquorum⟩ | ⟨happ_f, happ_t⟩
        · by_cases hsent_now :
              ((exec.drop k e 0).local_ p).sent q .vote (some b) = true
          · obtain ⟨k', h⟩ := already_sent (some b) hsent_now
            rcases h with hvr | hnc
            · exact ⟨k', Or.inl ⟨some b, hvr⟩⟩
            · exact ⟨k', Or.inr hnc⟩
          · have hsent_false : ((exec.drop k e 0).local_ p).sent q .vote (some b) = false := by
              cases h : ((exec.drop k e 0).local_ p).sent q .vote (some b)
              · rfl
              · exact absurd h hsent_now
            have hgate := vote_send_gate_from_echo_quorum n f input p q b (exec.drop k e 0)
              hcp hsent_false hquorum (hvote_once_vacuous (some b))
            exact deliver_type (fun w => w = some b) ⟨_, rfl⟩
              (fun w hw => by subst hw ; exact hgate)
        · by_cases hsent_now :
              ((exec.drop k e 0).local_ p).sent q .vote none = true
          · obtain ⟨k', h⟩ := already_sent none hsent_now
            rcases h with hvr | hnc
            · exact ⟨k', Or.inl ⟨none, hvr⟩⟩
            · exact ⟨k', Or.inr hnc⟩
          · have hsent_false : ((exec.drop k e 0).local_ p).sent q .vote none = false := by
              cases h : ((exec.drop k e 0).local_ p).sent q .vote none
              · rfl
              · exact absurd h hsent_now
            have hgate := vote_send_gate_from_both_approved n f input p q (exec.drop k e 0)
              hcp hsent_false happ_f happ_t (hvote_once_vacuous none)
            exact deliver_type (fun w => w = none) ⟨_, rfl⟩
              (fun w hw => by subst hw ; exact hgate)

/-- Binary decide delivery: a correct `q` with ≥ `n − f` binary votes
    for some `b` eventually decides (or becomes faulty). Case-splits on
    whether `q` has already decided; otherwise fires `wf_decide` with
    the `decide (some b)` gate. -/
theorem decide_delivery_binary (input : Fin n → Bool) (hn : n > 3 * f)
    (q : Fin n) (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hcq : isCorrect n (exec.drop k e 0) q)
    (hq : countVoteRecv n ((exec.drop k e 0).local_ q) (some b) ≥ n - f) :
    ∃ k', (∃ v, ((exec.drop (k + k') e 0).local_ q).decided = some v)
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) q := by
  by_cases hdec_now : ((exec.drop k e 0).local_ q).decided = none
  · -- Not yet decided: build gate and fire wf_decide.
    have hgate : ((bca n f input).actions (.decide q (some b))).gate
        (exec.drop k e 0) := by
      refine ⟨hcq, hdec_now, ?_⟩
      show countVoteRecv n ((exec.drop k e 0).local_ q) (some b) ≥ returnThreshold n f
      unfold returnThreshold ; exact hq
    have hmono : ∀ d,
        isCorrect n (exec.drop (k + d) e 0) q →
        ((exec.drop (k + d) e 0).local_ q).decided = none →
        ((bca n f input).actions (.decide q (some b))).gate (exec.drop k e 0) →
        ((bca n f input).actions (.decide q (some b))).gate (exec.drop (k + d) e 0) := by
      intro d hc_d hdec_d _
      refine ⟨hc_d, hdec_d, ?_⟩
      show countVoteRecv n ((exec.drop (k + d) e 0).local_ q) (some b) ≥ returnThreshold n f
      unfold returnThreshold
      exact countVoteRecv_persist n f input e hsafety q (some b) (n - f) k d hq
    exact wf_decide n f input q (some b) e hsafety hfair k hmono hcq hgate
  · -- Already decided: extract the value.
    refine ⟨0, Or.inl ?_⟩
    cases hd : ((exec.drop k e 0).local_ q).decided with
    | none => exact absurd hd hdec_now
    | some v => exact ⟨v, hd⟩

/-- `⊥` decide delivery: a correct `q` that has approved both binary
    values and has ≥ `n − f` total vote receipts eventually decides
    (or becomes faulty). Parallel structure to `decide_delivery_binary`. -/
theorem decide_delivery_none (input : Fin n → Bool) (hn : n > 3 * f)
    (q : Fin n)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hcq : isCorrect n (exec.drop k e 0) q)
    (happ_f : ((exec.drop k e 0).local_ q).approved false = true)
    (happ_t : ((exec.drop k e 0).local_ q).approved true = true)
    (hany : countAnyVoteRecv n ((exec.drop k e 0).local_ q) ≥ n - f) :
    ∃ k', (∃ v, ((exec.drop (k + k') e 0).local_ q).decided = some v)
          ∨ ¬isCorrect n (exec.drop (k + k') e 0) q := by
  by_cases hdec_now : ((exec.drop k e 0).local_ q).decided = none
  · have hgate : ((bca n f input).actions (.decide q none)).gate
        (exec.drop k e 0) := by
      refine ⟨hcq, hdec_now, happ_f, happ_t, ?_⟩
      show countAnyVoteRecv n ((exec.drop k e 0).local_ q) ≥ returnThreshold n f
      unfold returnThreshold ; exact hany
    have hmono : ∀ d,
        isCorrect n (exec.drop (k + d) e 0) q →
        ((exec.drop (k + d) e 0).local_ q).decided = none →
        ((bca n f input).actions (.decide q none)).gate (exec.drop k e 0) →
        ((bca n f input).actions (.decide q none)).gate (exec.drop (k + d) e 0) := by
      intro d hc_d hdec_d _
      refine ⟨hc_d, hdec_d, ?_, ?_, ?_⟩
      · exact approved_persist n f input e hsafety q false k d happ_f
      · exact approved_persist n f input e hsafety q true k d happ_t
      · show countAnyVoteRecv n ((exec.drop (k + d) e 0).local_ q) ≥ returnThreshold n f
        unfold returnThreshold
        exact countAnyVoteRecv_persist n f input e hsafety q (n - f) k d hany
    exact wf_decide n f input q none e hsafety hfair k hmono hcq hgate
  · refine ⟨0, Or.inl ?_⟩
    cases hd : ((exec.drop k e 0).local_ q).decided with
    | none => exact absurd hd hdec_now
    | some v => exact ⟨v, hd⟩

/-! ## Cascade lemmas

    Building blocks shared by multiple milestones and convergence lemmas. -/

/-- **Amplification cascade**: if at step `k` every correct process
    already has `countInitRecv b ≥ f + 1`, then at some later step every
    correct receiver has received `init(b)` from every correct sender.
    Shared backbone of milestone 2 and `approve_propagation`. -/
theorem amplify_cascade (input : Fin n → Bool) (hn : n > 3 * f)
    (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hall : ∀ p, isCorrect n (exec.drop k e 0) p →
                  countInitRecv n ((exec.drop k e 0).local_ p) b ≥ f + 1) :
    ∃ k', ∀ q, (∀ p, isCorrect n (exec.drop (k + k') e 0) p →
                      ((exec.drop (k + k') e 0).local_ q).initRecv p b = true)
                ∨ ¬isCorrect n (exec.drop (k + k') e 0) q := by
  -- Per-(sender, receiver) primitive: rebase to step k + k_offset ≥ k.
  have hdel : ∀ p (r : Fin n) (j : Nat), ∃ j',
      ((exec.drop (j + j') e 0).local_ r).initRecv p b = true ∨
      ¬isCorrect n (exec.drop (j + j') e 0) p := by
    intro p r j
    by_cases hcp_eff : isCorrect n (exec.drop (j + k) e 0) p
    · -- correct at j+k → correct at k (corruption monotone forward)
      have hcp_k : isCorrect n (exec.drop k e 0) p :=
        isCorrect_at_earlier n f input e hsafety p k j
          (by rw [show k + j = j + k from by omega] ; exact hcp_eff)
      have hcount_k : countInitRecv n ((exec.drop k e 0).local_ p) b ≥ f + 1 :=
        hall p hcp_k
      have hcount_eff : countInitRecv n ((exec.drop (j + k) e 0).local_ p) b ≥ f + 1 := by
        have := countInitRecv_persist n f input e hsafety p b (f + 1) k j hcount_k
        have heq : k + j = j + k := by omega
        rw [heq] at this ; exact this
      obtain ⟨k_amp, hres⟩ :=
        amplify_init_delivery n f input p r b e hsafety hfair (j + k) hcount_eff
      refine ⟨k + k_amp, ?_⟩
      rw [show j + (k + k_amp) = (j + k) + k_amp from by omega]
      exact hres
    · exact ⟨k, Or.inr hcp_eff⟩
  obtain ⟨k', hgrid⟩ := combine_senders_receivers n f input
    (fun p r s => (s.local_ r).initRecv p b = true)
    e hsafety hfair hdel
    (fun p r j d hir => initRecv_persist n f input e hsafety r p b j d hir)
    (List.finRange n) (List.finRange n) k
  refine ⟨k', fun q => ?_⟩
  by_cases hcq : isCorrect n (exec.drop (k + k') e 0) q
  · left
    intro p hcp
    rcases hgrid q (List.mem_finRange q) p (List.mem_finRange p) with hir | hnc
    · exact hir
    · exact absurd hcp hnc
  · right ; exact hcq

/-! ## Convergence lemmas

    Independent properties that compose with the milestone chain. -/

/-- **Step A** of approve propagation: if some correct `p` has approved `b`
    at step `k`, then at some later step every correct process has crossed
    the amplify threshold for `b`. The argument: `p` has ≥ `n − f` init(b)
    senders, of which ≥ `n − 2f` are correct. Each such correct sender
    will (under fairness) deliver `init(b)` to every receiver, which gives
    every correct receiver count(b) ≥ `n − 2f ≥ f + 1`. -/
theorem approved_to_amplify (input : Fin n → Bool) (hn : n > 3 * f)
    (p : Fin n) (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (happroved : ((exec.drop k e 0).local_ p).approved b = true) :
    ∃ k', ∀ q, isCorrect n (exec.drop (k + k') e 0) q →
                countInitRecv n ((exec.drop (k + k') e 0).local_ q) b ≥ f + 1 := by
  -- Step 1: p has ≥ n - f init(b) senders at step k.
  have hcnt_p : countInitRecv n ((exec.drop k e 0).local_ p) b ≥ approveThreshold n f :=
    approved_implies_countInitRecv n f input e hsafety k p b happroved
  -- Step 2: Per-sender delivery: for s ∈ p.initRecv at k AND correct at k, use wf_chain.
  -- For others, return a trivial witness via the extended `received` predicate.
  let received : Fin n → Fin n → State n → Prop := fun s r state =>
    (state.local_ r).initRecv s b = true ∨
    ((exec.drop k e 0).local_ p).initRecv s b = false
  have hdel : ∀ s (r : Fin n) (j : Nat), ∃ j',
      received s r (exec.drop (j + j') e 0)
        ∨ ¬isCorrect n (exec.drop (j + j') e 0) s := by
    intro s r j
    by_cases hinS : ((exec.drop k e 0).local_ p).initRecv s b = true
    · -- s ∈ p's initRecv at k. Use init_delivery_from_initRecv at step
      -- `k + j` (≥ both j and k) after persisting `hinS`.
      obtain ⟨k_del, hres⟩ :=
        init_delivery_from_initRecv n f input p s r b e hsafety hfair (k + j)
          (initRecv_persist n f input e hsafety p s b k j hinS)
      refine ⟨k + k_del, ?_⟩
      rw [show j + (k + k_del) = (k + j) + k_del from by omega]
      rcases hres with hir | hnc
      · exact Or.inl (Or.inl hir)
      · exact Or.inr hnc
    · -- s ∉ p's initRecv at k: trivial via second disjunct
      exact ⟨0, Or.inl (Or.inr (by
        cases h : ((exec.drop k e 0).local_ p).initRecv s b
        · rfl
        · exact absurd h hinS))⟩
  have hpersist : ∀ s r (j d : Nat),
      received s r (exec.drop j e 0) → received s r (exec.drop (j + d) e 0) := by
    intro s r j d
    intro hrcv
    rcases hrcv with hir | hninS
    · exact Or.inl (initRecv_persist n f input e hsafety r s b j d hir)
    · exact Or.inr hninS
  obtain ⟨k', hgrid⟩ := combine_senders_receivers n f input received
    e hsafety hfair hdel hpersist
    (List.finRange n) (List.finRange n) k
  refine ⟨k', fun q hcq => ?_⟩
  -- Counting: ≥ n - 2f ≥ f + 1 senders delivered to q.
  let sk := exec.drop (k + k') e 0
  let C : Fin n → Bool := fun s => decide (s ∉ sk.corrupted)
  let M : Fin n → Bool := fun s => ((exec.drop k e 0).local_ p).initRecv s b
  let A : Fin n → Bool := fun s => (sk.local_ q).initRecv s b
  -- Every s with M s = true AND C s = true has A s = true
  have hMC_A : ∀ s, M s = true → C s = true → A s = true := by
    intro s hM hC
    simp only [C, decide_eq_true_eq] at hC
    rcases hgrid q (List.mem_finRange q) s (List.mem_finRange s) with hrcv | hnc
    · rcases hrcv with hir | hninS
      · exact hir
      · simp [M] at hM ; rw [hM] at hninS ; exact absurd hninS (by simp)
    · exact absurd hC hnc
  -- |filter M| ≥ n - f (from hcnt_p)
  have hM_ge : ((List.finRange n).filter M).length ≥ n - f := by
    unfold approveThreshold countInitRecv at hcnt_p
    exact hcnt_p
  -- |filter C| ≥ n - f
  have hbudget_k' : sk.corrupted.length ≤ f :=
    corruption_budget n f input hn e hsafety (k + k')
  -- |filter (M ∧ C)| ≥ |filter M| - f via intersect_correct_ge
  have hMC_ge : ((List.finRange n).filter (fun s => M s && C s)).length ≥ n - f - f :=
    intersect_correct_ge sk.corrupted M hbudget_k' hM_ge
  -- |filter A| ≥ |filter (M ∧ C)| ≥ n - 2f
  have hA_ge : ((List.finRange n).filter A).length ≥ n - 2 * f := by
    have h1 : ((List.finRange n).filter (fun s => M s && C s)).length ≤
        ((List.finRange n).filter A).length := by
      apply filter_length_mono
      intro s hMC
      rw [Bool.and_eq_true] at hMC
      exact hMC_A s hMC.1 hMC.2
    omega
  show countInitRecv n (sk.local_ q) b ≥ f + 1
  unfold countInitRecv
  change ((List.finRange n).filter A).length ≥ f + 1
  omega

/-- **Step C** of approve propagation: if at step `k` every correct receiver
    `q` has received `init(b)` from every correct sender, then every
    correct `q` has approved `b`. Pure safety: count(b) ≥ |correct| ≥
    `n − f`, and the safety invariant `count ≥ n − f → approved` finishes. -/
theorem all_init_to_approved (input : Fin n → Bool) (hn : n > 3 * f)
    (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hall : ∀ q, (∀ p, isCorrect n (exec.drop k e 0) p →
                       ((exec.drop k e 0).local_ q).initRecv p b = true)
                  ∨ ¬isCorrect n (exec.drop k e 0) q) :
    ∀ q, ((exec.drop k e 0).local_ q).approved b = true
          ∨ ¬isCorrect n (exec.drop k e 0) q := by
  -- Pull the count → approved invariant out of bca_inv at step k.
  have hinv := init_invariant
    (bca_inv_init n f input)
    (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
    e hsafety
  obtain ⟨hbudget, _, _, _, _, _, _, _, _, _, _, hcount_app⟩ := hinv k
  have hnf : n > f := by omega
  intro q
  rcases hall q with hcorr_recv | hnc
  · left
    let sk := exec.drop k e 0
    let A : Fin n → Bool := fun p => (sk.local_ q).initRecv p b
    have hA_ge : ((List.finRange n).filter A).length ≥ n - f :=
      count_correct_ge sk.corrupted hbudget A hcorr_recv
    have hcnt : countInitRecv n (sk.local_ q) b ≥ approveThreshold n f := by
      unfold countInitRecv approveThreshold
      change ((List.finRange n).filter A).length ≥ n - f
      exact hA_ge
    exact hcount_app hnf q b hcnt
  · right ; exact hnc

/-- If a correct process has approved `b`, then every correct process
    eventually approves `b`. Composes:
    `approved_to_amplify` (round 1) + `amplify_cascade` (round 2) +
    `all_init_to_approved` (final safety step). -/
theorem approve_propagation (input : Fin n → Bool) (hn : n > 3 * f)
    (p : Fin n) (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hcp : isCorrect n (exec.drop k e 0) p)
    (happroved : ((exec.drop k e 0).local_ p).approved b = true) :
    ∃ k', ∀ q, ((exec.drop (k + k') e 0).local_ q).approved b = true
              ∨ ¬isCorrect n (exec.drop (k + k') e 0) q := by
  -- Step A: round 1 → every correct has count(b) ≥ f + 1
  obtain ⟨k₁, hamp⟩ := approved_to_amplify n f input hn p b e hsafety hfair k hcp happroved
  -- Step B: amplify_cascade → every correct receives init(b) from every correct
  obtain ⟨k₂, hgrid⟩ := amplify_cascade n f input hn b e hsafety hfair (k + k₁) hamp
  -- Step C: count → approved
  refine ⟨k₁ + k₂, ?_⟩
  rw [show k + (k₁ + k₂) = (k + k₁) + k₂ from by omega]
  exact all_init_to_approved n f input hn b e hsafety hfair ((k + k₁) + k₂) hgrid

/-- **Both-value approval propagation**: if two correct witnesses `p₁` and
    `p₂` (possibly the same process) collectively have approved `false`
    and `true` at step `k`, then every correct process eventually has
    approved both binary values. Composes two applications of
    `approve_propagation` via `approved_persist` and `isCorrect_persist`. -/
theorem approve_both_propagation (input : Fin n → Bool) (hn : n > 3 * f)
    (p₁ p₂ : Fin n)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hcp₁ : isCorrect n (exec.drop k e 0) p₁)
    (hcp₂ : isCorrect n (exec.drop k e 0) p₂)
    (happ_f : ((exec.drop k e 0).local_ p₁).approved false = true)
    (happ_t : ((exec.drop k e 0).local_ p₂).approved true = true) :
    ∃ k', ∀ q,
      (((exec.drop (k + k') e 0).local_ q).approved false = true ∧
       ((exec.drop (k + k') e 0).local_ q).approved true = true)
      ∨ ¬isCorrect n (exec.drop (k + k') e 0) q := by
  obtain ⟨k_f, hall_f⟩ :=
    approve_propagation n f input hn p₁ false e hsafety hfair k hcp₁ happ_f
  obtain ⟨k_t, hall_t⟩ :=
    approve_propagation n f input hn p₂ true e hsafety hfair k hcp₂ happ_t
  refine ⟨k_f + k_t, fun q => ?_⟩
  by_cases hcq : isCorrect n (exec.drop (k + (k_f + k_t)) e 0) q
  · left
    have happ_f_q : ((exec.drop (k + (k_f + k_t)) e 0).local_ q).approved false = true := by
      rcases hall_f q with h | hnc
      · have := approved_persist n f input e hsafety q false (k + k_f) k_t h
        rw [show (k + k_f) + k_t = k + (k_f + k_t) from by omega] at this
        exact this
      · exfalso
        have := isCorrect_persist n f input e hsafety q (k + k_f) k_t hnc
        rw [show (k + k_f) + k_t = k + (k_f + k_t) from by omega] at this
        exact this hcq
    have happ_t_q : ((exec.drop (k + (k_f + k_t)) e 0).local_ q).approved true = true := by
      rcases hall_t q with h | hnc
      · have := approved_persist n f input e hsafety q true (k + k_t) k_f h
        rw [show (k + k_t) + k_f = k + (k_f + k_t) from by omega] at this
        exact this
      · exfalso
        have := isCorrect_persist n f input e hsafety q (k + k_t) k_f hnc
        rw [show (k + k_t) + k_f = k + (k_f + k_t) from by omega] at this
        exact this hcq
    exact ⟨happ_f_q, happ_t_q⟩
  · right ; exact hcq

/-- **Case A** of milestone 3b: if all correct senders have echoed the same
    value `b` and the echo grid from milestone 3 holds, then every correct
    receiver has `countEchoRecv b ≥ n − f`. Counting via
    `intersect_correct_ge`. -/
theorem echo_same_value_count (input : Fin n → Bool) (hn : n > 3 * f)
    (b : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (k : Nat)
    (hgrid : ∀ q, (∀ p, isCorrect n (exec.drop k e 0) p →
                    ∃ b', ((exec.drop k e 0).local_ q).echoRecv p b' = true)
                  ∨ ¬isCorrect n (exec.drop k e 0) q)
    (hall_same : ∀ p, isCorrect n (exec.drop k e 0) p →
                      ((exec.drop k e 0).local_ p).echoed = some b) :
    ∀ q, countEchoRecv n ((exec.drop k e 0).local_ q) b ≥ n - f
          ∨ ¬isCorrect n (exec.drop k e 0) q := by
  intro q
  rcases hgrid q with hgq | hnc
  · left
    let sk := exec.drop k e 0
    let A : Fin n → Bool := fun p => (sk.local_ q).echoRecv p b
    -- For every correct p, q.echoRecv p b = true (via grid + single-shot echo).
    have hall_A : ∀ p, p ∉ sk.corrupted → A p = true := by
      intro p hcp
      obtain ⟨b', her⟩ := hgq p hcp
      have hecho_p := echoed_from_echoRecv n f input hn e hsafety k p q b' hcp her
      have hecho_p_b := hall_same p hcp
      rw [hecho_p_b] at hecho_p
      have : b' = b := by injection hecho_p with h ; exact h.symm
      subst this
      exact her
    have hbudget : sk.corrupted.length ≤ f :=
      corruption_budget n f input hn e hsafety k
    have hA_ge : ((List.finRange n).filter A).length ≥ n - f :=
      count_correct_ge sk.corrupted hbudget A hall_A
    show countEchoRecv n (sk.local_ q) b ≥ n - f
    unfold countEchoRecv
    change ((List.finRange n).filter A).length ≥ n - f
    exact hA_ge
  · right ; exact hnc

/-- **Case B** of milestone 3b: two correct processes with distinct echoed
    values force every correct process to eventually approve both binary
    values. Built from two applications of `approve_propagation`. -/
theorem echo_split_approves_both (input : Fin n → Bool) (hn : n > 3 * f)
    (p₁ p₂ : Fin n) (b₁ b₂ : Bool)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) (k : Nat)
    (hcp₁ : isCorrect n (exec.drop k e 0) p₁)
    (hcp₂ : isCorrect n (exec.drop k e 0) p₂)
    (he₁ : ((exec.drop k e 0).local_ p₁).echoed = some b₁)
    (he₂ : ((exec.drop k e 0).local_ p₂).echoed = some b₂)
    (hne : b₁ ≠ b₂) :
    ∃ k', ∀ q,
      (((exec.drop (k + k') e 0).local_ q).approved false = true ∧
       ((exec.drop (k + k') e 0).local_ q).approved true = true)
      ∨ ¬isCorrect n (exec.drop (k + k') e 0) q := by
  -- Convert the two distinct echoes into a witness for `approved false` and
  -- a witness for `approved true`, then call `approve_both_propagation`.
  have happ₁ := echoed_implies_approved n f input e hsafety k p₁ b₁ hcp₁ he₁
  have happ₂ := echoed_implies_approved n f input e hsafety k p₂ b₂ hcp₂ he₂
  -- Cases on b₁ to normalize (b₁, b₂) → (false, true).
  cases b₁ <;> cases b₂
  · exact absurd rfl hne
  · exact approve_both_propagation n f input hn p₁ p₂ e hsafety hfair k
      hcp₁ hcp₂ happ₁ happ₂
  · exact approve_both_propagation n f input hn p₂ p₁ e hsafety hfair k
      hcp₂ hcp₁ happ₂ happ₁
  · exact absurd rfl hne

/-! ## Milestones -/

/-- **Milestone 1**: at some step, every correct receiver `q` has received
    `init(input p)` from every non-corrupted sender `p`. -/
theorem milestone_init_count (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∀ q, (∀ p, isCorrect n (exec.drop k e 0) p →
                    ((exec.drop k e 0).local_ q).initRecv p (input p) = true)
              ∨ ¬isCorrect n (exec.drop k e 0) q := by
  obtain ⟨k, hgrid⟩ := combine_senders_receivers n f input
    (fun p r s => (s.local_ r).initRecv p (input p) = true)
    e hsafety hfair
    (fun p r k => init_delivery_correct_sender n f input p r e hsafety hfair k)
    (fun p r j d hir => initRecv_persist n f input e hsafety r p (input p) j d hir)
    (List.finRange n) (List.finRange n) 0
  refine ⟨0 + k, fun q => ?_⟩
  by_cases hcq : isCorrect n (exec.drop (0 + k) e 0) q
  · left
    intro p hcp
    rcases hgrid q (List.mem_finRange q) p (List.mem_finRange p) with hir | hnc
    · exact hir
    · exact absurd hcp hnc
  · right ; exact hcq

/-- **Milestone 1b**: at some step, there exists a single value `b ∈ {0,1}`
    such that every correct `q` has ≥ `f + 1` init(b) receipts. The
    common value `b` is obtained by pigeonhole on the inputs of the
    currently-correct senders: among ≥ n − f correct senders, some
    `b ∈ {true, false}` is the input of ≥ ⌈(n−f)/2⌉ ≥ f + 1 of them. -/
theorem milestone_init_amplify (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∃ b, ∀ q, countInitRecv n ((exec.drop k e 0).local_ q) b ≥ f + 1
                    ∨ ¬isCorrect n (exec.drop k e 0) q := by
  obtain ⟨k, hall⟩ := milestone_init_count n f input hn e hsafety hfair
  refine ⟨k, ?_⟩
  let sk := exec.drop k e 0
  let C : Fin n → Bool := fun p => decide (p ∉ sk.corrupted)
  -- Pigeonhole on inputs of correct senders.
  -- |correct| ≥ n - f, partition by `input`. One side has ≥ ⌈(n-f)/2⌉ ≥ f+1.
  let Ctrue : Fin n → Bool := fun p => C p && input p
  let Cfalse : Fin n → Bool := fun p => C p && !input p
  have hbudget : sk.corrupted.length ≤ f :=
    corruption_budget n f input hn e hsafety k
  have hC_ge : ((List.finRange n).filter C).length ≥ n - f := by
    have hsplit : (List.finRange n).length =
        ((List.finRange n).filter C).length +
        ((List.finRange n).filter (fun x => !C x)).length := by
      generalize List.finRange n = l
      induction l with
      | nil => simp
      | cons a t ih =>
        simp only [List.filter_cons] ; cases C a <;> simp <;> omega
    have hfin : (List.finRange n).length = n := List.length_finRange
    have hnotC_le : ((List.finRange n).filter (fun x => !C x)).length ≤ f := by
      calc ((List.finRange n).filter (fun x => !C x)).length
          ≤ sk.corrupted.length := by
            apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
            intro x hx ; simp [C, List.mem_filter] at hx ; exact hx
        _ ≤ f := hbudget
    omega
  -- |C| = |Ctrue| + |Cfalse|
  have hC_split : ((List.finRange n).filter C).length =
      ((List.finRange n).filter Ctrue).length +
      ((List.finRange n).filter Cfalse).length := by
    have := filter_split C input (List.finRange n)
    simpa [Ctrue, Cfalse, Bool.and_comm] using this
  have hnf : n - f ≥ 2 * f + 1 := by omega
  -- Pick the side with ≥ f + 1 correct senders
  by_cases htrue : ((List.finRange n).filter Ctrue).length ≥ f + 1
  · -- b = true: every correct q has ≥ f+1 init(true) (one per such sender)
    refine ⟨true, fun q => ?_⟩
    rcases hall q with hcorr_recv | hnc
    · left
      show countInitRecv n (sk.local_ q) true ≥ f + 1
      have hsub : ((List.finRange n).filter Ctrue).length ≤
          countInitRecv n (sk.local_ q) true := by
        unfold countInitRecv
        apply filter_length_mono
        intro p hp
        simp only [Ctrue, Bool.and_eq_true, decide_eq_true_eq, C] at hp
        have hcp : isCorrect n sk p := hp.1
        have hip : input p = true := hp.2
        have hir := hcorr_recv p hcp
        rw [hip] at hir ; exact hir
      omega
    · right ; exact hnc
  · -- b = false: |Cfalse| ≥ f + 1 by complement
    have hfalse : ((List.finRange n).filter Cfalse).length ≥ f + 1 := by omega
    refine ⟨false, fun q => ?_⟩
    rcases hall q with hcorr_recv | hnc
    · left
      show countInitRecv n (sk.local_ q) false ≥ f + 1
      have hsub : ((List.finRange n).filter Cfalse).length ≤
          countInitRecv n (sk.local_ q) false := by
        unfold countInitRecv
        apply filter_length_mono
        intro p hp
        simp only [Cfalse, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, C] at hp
        have hcp : isCorrect n sk p := hp.1
        have hip : input p = false := hp.2
        have hir := hcorr_recv p hcp
        rw [hip] at hir ; exact hir
      omega
    · right ; exact hnc

/-- **Milestone 2**: at some step, there exists a single value `b ∈ {0,1}`
    such that every correct receiver `q` has received `init(b)` from
    every correct sender `p`. Achieved because milestone 1b says every
    correct process already has count(b) ≥ f + 1, hence is enabled to
    send `init(b)`; one further delivery round propagates `init(b)`
    from every correct sender to every correct receiver. -/
theorem milestone_init_approve (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∃ b, ∀ q, (∀ p, isCorrect n (exec.drop k e 0) p →
                          ((exec.drop k e 0).local_ q).initRecv p b = true)
                    ∨ ¬isCorrect n (exec.drop k e 0) q := by
  obtain ⟨k₁, b, hamp⟩ := milestone_init_amplify n f input hn e hsafety hfair
  -- Drop the `¬correct` disjunct of `hamp` to get the precondition of
  -- `amplify_cascade`: every correct process has count(b) ≥ f + 1.
  have hall : ∀ p, isCorrect n (exec.drop k₁ e 0) p →
                   countInitRecv n ((exec.drop k₁ e 0).local_ p) b ≥ f + 1 := by
    intro p hcp
    rcases hamp p with hc | hnc
    · exact hc
    · exact absurd hcp hnc
  obtain ⟨k', hres⟩ := amplify_cascade n f input hn b e hsafety hfair k₁ hall
  exact ⟨k₁ + k', b, hres⟩

/-- **Milestone 3**: at some step, every correct receiver `q` has received
    an echo message from every correct sender `p` (the value may differ
    per sender, since a correct process echoes the first value it
    approved). -/
theorem milestone_echo_count (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∀ q, (∀ p, isCorrect n (exec.drop k e 0) p →
                    ∃ b', ((exec.drop k e 0).local_ q).echoRecv p b' = true)
              ∨ ¬isCorrect n (exec.drop k e 0) q := by
  -- Step 1: milestone 2 gives a value `b` and step `k₁` at which every
  -- correct receiver has init(b) from every correct sender.
  obtain ⟨k₁, b, hgrid_init⟩ := milestone_init_approve n f input hn e hsafety hfair
  -- Step 2: all_init_to_approved: every correct q has `q.approved b = true` at k₁.
  have happroved := all_init_to_approved n f input hn b e hsafety hfair k₁ hgrid_init
  -- Step 3: per-(sender, receiver) primitive via echo_delivery_from_approved,
  -- rebased to step `j + k₁` (≥ both j and k₁). Approved and hcp persist.
  have hdel : ∀ p (r : Fin n) (j : Nat), ∃ j',
      (∃ b', ((exec.drop ((j + k₁) + j') e 0).local_ r).echoRecv p b' = true)
        ∨ ¬isCorrect n (exec.drop ((j + k₁) + j') e 0) p := by
    intro p r j
    -- At step k₁, either p is correct (with approved b) or not.
    rcases happroved p with happ | hnc
    · -- p correct at k₁ with approved b. Persist to j + k₁.
      by_cases hcp_eff : isCorrect n (exec.drop (j + k₁) e 0) p
      · have happ_eff : ((exec.drop (j + k₁) e 0).local_ p).approved b = true := by
          have := approved_persist n f input e hsafety p b k₁ j happ
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        exact echo_delivery_from_approved n f input p r b e hsafety hfair (j + k₁)
          hcp_eff happ_eff
      · exact ⟨0, Or.inr hcp_eff⟩
    · -- p already faulty at k₁: still faulty at j + k₁.
      refine ⟨0, Or.inr ?_⟩
      have := isCorrect_persist n f input e hsafety p k₁ j hnc
      have heq : k₁ + j = j + k₁ := by omega
      rw [heq] at this ; exact this
  -- Need to reshape hdel to match combine_senders_receivers's signature:
  -- combine expects `∀ p r j, ∃ j', received p r (drop (j + j') e) ∨ ¬correct p`.
  -- We have `∃ j', received p r (drop ((j + k₁) + j') e) ∨ ¬correct p`.
  -- Absorb the k₁ into j': given j', output (k₁ + j') so j + (k₁ + j') = (j + k₁) + j'.
  have hdel' : ∀ p (r : Fin n) (j : Nat), ∃ j',
      (∃ b', ((exec.drop (j + j') e 0).local_ r).echoRecv p b' = true)
        ∨ ¬isCorrect n (exec.drop (j + j') e 0) p := by
    intro p r j
    obtain ⟨j', h⟩ := hdel p r j
    refine ⟨k₁ + j', ?_⟩
    rw [show j + (k₁ + j') = (j + k₁) + j' from by omega]
    exact h
  have hpersist : ∀ p r (j d : Nat),
      (∃ b', ((exec.drop j e 0).local_ r).echoRecv p b' = true) →
      (∃ b', ((exec.drop (j + d) e 0).local_ r).echoRecv p b' = true) := by
    intro p r j d ⟨b', her⟩
    exact ⟨b', echoRecv_persist n f input e hsafety r p b' j d her⟩
  obtain ⟨k₂, hgrid⟩ := combine_senders_receivers n f input
    (fun p r s => ∃ b', (s.local_ r).echoRecv p b' = true)
    e hsafety hfair hdel' hpersist
    (List.finRange n) (List.finRange n) 0
  refine ⟨0 + k₂, fun q => ?_⟩
  by_cases hcq : isCorrect n (exec.drop (0 + k₂) e 0) q
  · left
    intro p hcp
    rcases hgrid q (List.mem_finRange q) p (List.mem_finRange p) with her | hnc
    · exact her
    · exact absurd hcp hnc
  · right ; exact hcq

/-- **Milestone 3b**: at some step, every correct `q` either has ≥ `n − f`
    echo receipts for *some* value `b_q` (possibly different per process),
    or has approved *both* values `false` and `true`. The disjunction is
    needed because correct echoes may split between values — in that case
    no single side accumulates `n − f` echoes, but the "both approved"
    branch takes over and feeds the `⊥`-vote path. -/
theorem milestone_echo_amplify (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∀ q,
      (∃ b, countEchoRecv n ((exec.drop k e 0).local_ q) b ≥ n - f) ∨
      (((exec.drop k e 0).local_ q).approved false = true ∧
       ((exec.drop k e 0).local_ q).approved true = true) ∨
      ¬isCorrect n (exec.drop k e 0) q := by
  obtain ⟨k₁, hgrid⟩ := milestone_echo_count n f input hn e hsafety hfair
  -- Classical case split: do all correct senders agree on a single echoed value?
  by_cases hsame : ∃ b, ∀ p, isCorrect n (exec.drop k₁ e 0) p →
      ((exec.drop k₁ e 0).local_ p).echoed = some b
  · -- Case A: all agree on some b. Use echo_same_value_count.
    obtain ⟨b, hall_same⟩ := hsame
    refine ⟨k₁, fun q => ?_⟩
    rcases echo_same_value_count n f input hn b e hsafety k₁ hgrid hall_same q with
        hcount | hnc
    · left ; exact ⟨b, hcount⟩
    · right ; right ; exact hnc
  · -- Case B: two correct processes with distinct echoed values.
    -- De Morgan hsame manually: ∀ b, ∃ p, correct p ∧ p.echoed ≠ some b
    have hsame : ∀ b, ∃ p, isCorrect n (exec.drop k₁ e 0) p ∧
        ((exec.drop k₁ e 0).local_ p).echoed ≠ some b := by
      intro b
      by_contra habs
      apply hsame
      refine ⟨b, fun p hcp => ?_⟩
      by_contra hne
      exact habs ⟨p, hcp, hne⟩
    -- Extract witnesses for b = false and b = true.
    obtain ⟨p_f, hcf, hef⟩ := hsame false
    obtain ⟨p_t, hct, het⟩ := hsame true
    -- Every correct p has echoed some value (from milestone 3 via echoed_from_echoRecv).
    -- Use hgrid at an arbitrary correct receiver (p_f itself).
    rcases hgrid p_f with hgrid_pf | hncf
    · obtain ⟨b_f, her_f⟩ := hgrid_pf p_f hcf
      have hecho_pf := echoed_from_echoRecv n f input hn e hsafety k₁ p_f p_f b_f hcf her_f
      -- p_f.echoed = some b_f, but p_f.echoed ≠ some false, so b_f = true.
      have hbf_true : b_f = true := by
        cases b_f
        · exfalso ; exact hef hecho_pf
        · rfl
      subst hbf_true
      -- Similarly extract b_t for p_t.
      rcases hgrid p_t with hgrid_pt | hnct
      · obtain ⟨b_t, her_t⟩ := hgrid_pt p_t hct
        have hecho_pt := echoed_from_echoRecv n f input hn e hsafety k₁ p_t p_t b_t hct her_t
        have hbt_false : b_t = false := by
          cases b_t
          · rfl
          · exfalso ; exact het hecho_pt
        subst hbt_false
        -- Now p_f echoed true, p_t echoed false — distinct.
        obtain ⟨k', hboth⟩ := echo_split_approves_both n f input hn p_f p_t true false
          e hsafety hfair k₁ hcf hct hecho_pf hecho_pt (by decide)
        refine ⟨k₁ + k', fun q => ?_⟩
        rcases hboth q with ⟨happ_f, happ_t⟩ | hnc
        · right ; left ; exact ⟨happ_f, happ_t⟩
        · right ; right ; exact hnc
      · -- p_t not correct at k₁: contradicts hct
        exact absurd hct hnct
    · -- p_f not correct at k₁: contradicts hcf
      exact absurd hcf hncf

/-- **Milestone 4**: at some step, every correct receiver `q` has received
    a vote message from every correct sender `p` (the value may differ
    per sender — binary vote for processes in the concentrated-echo case,
    `none` for processes that approved both values). -/
theorem milestone_vote_count (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∀ q, (∀ p, isCorrect n (exec.drop k e 0) p →
                    ∃ v, ((exec.drop k e 0).local_ q).voteRecv p v = true)
              ∨ ¬isCorrect n (exec.drop k e 0) q := by
  -- Step 1: milestone 3b gives a step k₁ at which every correct process
  -- is ready to vote (quorum or both-approved).
  obtain ⟨k₁, hready⟩ := milestone_echo_amplify n f input hn e hsafety hfair
  -- Step 2: per-(sender, receiver) delivery primitive via vote_delivery_from_ready,
  -- rebased to step j + k₁ (≥ both j and k₁). quorum and approved flags
  -- persist via countEchoRecv_persist / approved_persist.
  have hdel : ∀ p (r : Fin n) (j : Nat), ∃ j',
      (∃ v, ((exec.drop ((j + k₁) + j') e 0).local_ r).voteRecv p v = true)
        ∨ ¬isCorrect n (exec.drop ((j + k₁) + j') e 0) p := by
    intro p r j
    rcases hready p with hquorum | hboth | hnc
    · -- p has quorum for some b at k₁. Persist to j + k₁.
      by_cases hcp_eff : isCorrect n (exec.drop (j + k₁) e 0) p
      · obtain ⟨b, hqb⟩ := hquorum
        have hquorum_eff : countEchoRecv n ((exec.drop (j + k₁) e 0).local_ p) b ≥ n - f := by
          have := countEchoRecv_persist n f input e hsafety p b (n - f) k₁ j hqb
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        exact vote_delivery_from_ready n f input hn p r e hsafety hfair (j + k₁) hcp_eff
          (Or.inl ⟨b, hquorum_eff⟩)
      · exact ⟨0, Or.inr hcp_eff⟩
    · -- p has approved both at k₁. Persist to j + k₁.
      by_cases hcp_eff : isCorrect n (exec.drop (j + k₁) e 0) p
      · obtain ⟨happ_f, happ_t⟩ := hboth
        have happ_f_eff : ((exec.drop (j + k₁) e 0).local_ p).approved false = true := by
          have := approved_persist n f input e hsafety p false k₁ j happ_f
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        have happ_t_eff : ((exec.drop (j + k₁) e 0).local_ p).approved true = true := by
          have := approved_persist n f input e hsafety p true k₁ j happ_t
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        exact vote_delivery_from_ready n f input hn p r e hsafety hfair (j + k₁) hcp_eff
          (Or.inr ⟨happ_f_eff, happ_t_eff⟩)
      · exact ⟨0, Or.inr hcp_eff⟩
    · -- p not correct at k₁ → not correct at j + k₁
      refine ⟨0, Or.inr ?_⟩
      have := isCorrect_persist n f input e hsafety p k₁ j hnc
      have heq : k₁ + j = j + k₁ := by omega
      rw [heq] at this ; exact this
  -- Reshape hdel for combine_senders_receivers' (j + j') form.
  have hdel' : ∀ p (r : Fin n) (j : Nat), ∃ j',
      (∃ v, ((exec.drop (j + j') e 0).local_ r).voteRecv p v = true)
        ∨ ¬isCorrect n (exec.drop (j + j') e 0) p := by
    intro p r j
    obtain ⟨j', h⟩ := hdel p r j
    refine ⟨k₁ + j', ?_⟩
    rw [show j + (k₁ + j') = (j + k₁) + j' from by omega]
    exact h
  have hpersist : ∀ p r (j d : Nat),
      (∃ v, ((exec.drop j e 0).local_ r).voteRecv p v = true) →
      (∃ v, ((exec.drop (j + d) e 0).local_ r).voteRecv p v = true) := by
    intro p r j d ⟨v, hvr⟩
    exact ⟨v, voteRecv_persist n f input e hsafety r p v j d hvr⟩
  obtain ⟨k₂, hgrid⟩ := combine_senders_receivers n f input
    (fun p r s => ∃ v, (s.local_ r).voteRecv p v = true)
    e hsafety hfair hdel' hpersist
    (List.finRange n) (List.finRange n) 0
  refine ⟨0 + k₂, fun q => ?_⟩
  by_cases hcq : isCorrect n (exec.drop (0 + k₂) e 0) q
  · left
    intro p hcp
    rcases hgrid q (List.mem_finRange q) p (List.mem_finRange p) with hvr | hnc
    · exact hvr
    · exact absurd hcp hnc
  · right ; exact hcq

/-- **Milestone 4b**: at some step, every correct `q` is "ready to decide":
    either (first disjunct) it has ≥ `n − f` binary votes for some `b`
    (enabling `decide (some b)`), or (second disjunct) it has approved
    both values *and* has at least `n − f` total vote receipts
    (enabling `decide none`). Proof: classical case split on whether
    some correct process voted `⊥`. -/
theorem milestone_vote_amplify (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∀ q,
      (∃ b, countVoteRecv n ((exec.drop k e 0).local_ q) (some b) ≥ n - f) ∨
      (((exec.drop k e 0).local_ q).approved false = true ∧
       ((exec.drop k e 0).local_ q).approved true = true ∧
       countAnyVoteRecv n ((exec.drop k e 0).local_ q) ≥ n - f) ∨
      ¬isCorrect n (exec.drop k e 0) q := by
  obtain ⟨k₁, hgrid⟩ := milestone_vote_count n f input hn e hsafety hfair
  -- Classical case split: does some correct process vote ⊥ at step k₁?
  by_cases hexists_none :
      ∃ p, isCorrect n (exec.drop k₁ e 0) p ∧
           ((exec.drop k₁ e 0).local_ p).voted none = true
  · -- Case A: some correct p₀ voted ⊥ → approved both → approve_both_propagation.
    obtain ⟨p₀, hcp₀, hv₀⟩ := hexists_none
    obtain ⟨happ_f₀, happ_t₀⟩ :=
      voted_none_implies_both_approved n f input e hsafety k₁ p₀ hcp₀ hv₀
    obtain ⟨k', hall_both⟩ :=
      approve_both_propagation n f input hn p₀ p₀ e hsafety hfair k₁
        hcp₀ hcp₀ happ_f₀ happ_t₀
    refine ⟨k₁ + k', fun q => ?_⟩
    by_cases hcq_final : isCorrect n (exec.drop (k₁ + k') e 0) q
    · -- Correct at final → correct at k₁ (corruption monotone forward).
      have hcq_k₁ : isCorrect n (exec.drop k₁ e 0) q :=
        isCorrect_at_earlier n f input e hsafety q k₁ k' hcq_final
      rcases hall_both q with ⟨happ_f_q, happ_t_q⟩ | hnc
      · right ; left
        refine ⟨happ_f_q, happ_t_q, ?_⟩
        -- countAnyVoteRecv q ≥ n − f: count at k₁ from the grid + budget,
        -- then persist to k₁ + k'.
        have hcount_k₁ : countAnyVoteRecv n ((exec.drop k₁ e 0).local_ q) ≥ n - f := by
          let sk := exec.drop k₁ e 0
          let A : Fin n → Bool := fun p =>
            (sk.local_ q).voteRecv p (some false) ||
            (sk.local_ q).voteRecv p (some true) ||
            (sk.local_ q).voteRecv p none
          have hall_A : ∀ p, p ∉ sk.corrupted → A p = true := by
            intro p hcp
            rcases hgrid q with hgq | hnc
            · obtain ⟨v, hvr⟩ := hgq p hcp
              simp only [A, Bool.or_eq_true]
              cases v with
              | some b => cases b
                          · left ; left ; exact hvr
                          · left ; right ; exact hvr
              | none => right ; exact hvr
            · exact absurd hcq_k₁ hnc
          have hbudget_k₁ : sk.corrupted.length ≤ f :=
            corruption_budget n f input hn e hsafety k₁
          have hA_ge : ((List.finRange n).filter A).length ≥ n - f :=
            count_correct_ge sk.corrupted hbudget_k₁ A hall_A
          show countAnyVoteRecv n (sk.local_ q) ≥ n - f
          unfold countAnyVoteRecv
          change ((List.finRange n).filter A).length ≥ n - f
          exact hA_ge
        exact countAnyVoteRecv_persist n f input e hsafety q (n - f) k₁ k' hcount_k₁
      · exact absurd hcq_final hnc
    · right ; right ; exact hcq_final
  · -- Case B: every correct sender voted some binary value (no ⊥).
    -- By voted_binary_agree all agree on a single value b. Count at each q.
    -- De Morgan: ∀ p, correct → ¬voted none
    have hno_none : ∀ p, isCorrect n (exec.drop k₁ e 0) p →
        ((exec.drop k₁ e 0).local_ p).voted none = false := by
      intro p hcp
      by_contra habs
      apply hexists_none
      refine ⟨p, hcp, ?_⟩
      cases h : ((exec.drop k₁ e 0).local_ p).voted none
      · exact absurd h habs
      · rfl
    -- Extract some correct "witness" p₀ via any correct q (if one exists)
    -- and its voted value b₀. We need at least one correct process; use
    -- milestone 4's grid at an arbitrary q to find one. But we can also
    -- directly use `hgrid q` for any q — if no correct q exists, then all
    -- processes are faulty, which contradicts the corruption budget.
    -- Corruption budget: ≥ n - f correct, so some q correct.
    have hbudget := corruption_budget n f input hn e hsafety k₁
    -- There's at least one correct process — pick q₀.
    obtain ⟨q₀, hcq₀⟩ : ∃ q, isCorrect n (exec.drop k₁ e 0) q := by
      by_contra habs
      have hall_corrupt : ∀ q, q ∈ (exec.drop k₁ e 0).corrupted := by
        intro q
        by_contra hnq
        exact habs ⟨q, hnq⟩
      have : n ≤ (exec.drop k₁ e 0).corrupted.length := by
        have := nodup_sub_length (finRange_nodup n) (fun q _ => hall_corrupt q)
        simpa using this
      omega
    -- From hgrid at q₀ and voted_from_voteRecv, each correct p has voted some value.
    rcases hgrid q₀ with hgq₀ | hncq₀
    · -- For each correct p, extract its voted binary value.
      have hall_binary : ∀ p, isCorrect n (exec.drop k₁ e 0) p →
          ∃ b, ((exec.drop k₁ e 0).local_ p).voted (some b) = true := by
        intro p hcp
        obtain ⟨v, hvr⟩ := hgq₀ p hcp
        have hvp := voted_from_voteRecv n f input hn e hsafety k₁ p q₀ v hcp hvr
        cases v with
        | some b => exact ⟨b, hvp⟩
        | none => exact absurd hvp (by rw [hno_none p hcp] ; simp)
      -- Pick the voted value of q₀ itself (q₀ is correct).
      obtain ⟨b, hvq₀⟩ := hall_binary q₀ hcq₀
      -- All correct processes vote the same binary value b.
      have hall_same : ∀ p, isCorrect n (exec.drop k₁ e 0) p →
          ((exec.drop k₁ e 0).local_ p).voted (some b) = true := by
        intro p hcp
        obtain ⟨b_p, hvp⟩ := hall_binary p hcp
        have hb_eq : b_p = b :=
          voted_binary_agree n f input hn e hsafety k₁ p q₀ b_p b hcp hcq₀ hvp hvq₀
        rw [← hb_eq] ; exact hvp
      -- Counting at each correct q: q has voteRecv p (some b) for every correct p.
      refine ⟨k₁, fun q => ?_⟩
      rcases hgrid q with hgq | hnc
      · left ; refine ⟨b, ?_⟩
        -- countVoteRecv q (some b) ≥ |correct| ≥ n - f
        let sk := exec.drop k₁ e 0
        let A : Fin n → Bool := fun p => (sk.local_ q).voteRecv p (some b)
        have hall_A : ∀ p, p ∉ sk.corrupted → A p = true := by
          intro p hcp
          -- q has voteRecv p v for some v (via hgq). By voted_from_voteRecv,
          -- p.voted v = true. By hall_same, p.voted (some b) = true. By
          -- voted_unique, v = some b. So q.voteRecv p (some b) = true.
          obtain ⟨v, hvr⟩ := hgq p hcp
          have hvp := voted_from_voteRecv n f input hn e hsafety k₁ p q v hcp hvr
          have hvb := hall_same p hcp
          have hv_eq : v = some b :=
            voted_unique n f input e hsafety k₁ p v (some b) hcp hvp hvb
          rw [hv_eq] at hvr
          exact hvr
        have hbudget_k₁ : sk.corrupted.length ≤ f :=
          corruption_budget n f input hn e hsafety k₁
        have hA_ge : ((List.finRange n).filter A).length ≥ n - f :=
          count_correct_ge sk.corrupted hbudget_k₁ A hall_A
        show countVoteRecv n (sk.local_ q) (some b) ≥ n - f
        unfold countVoteRecv
        change ((List.finRange n).filter A).length ≥ n - f
        exact hA_ge
      · right ; right ; exact hnc
    · exact absurd hcq₀ hncq₀

/-- **Termination**: at some step, every correct process has committed
    a decision value. Direct composition of `milestone_vote_amplify`
    and `wf_decide`: either a process has ≥ `n − f` binary votes
    (decide-`some b` gate) or approved both with ≥ `n − f` total votes
    (decide-`none` gate). -/
theorem milestone_termination (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∀ q, (∃ v, ((exec.drop k e 0).local_ q).decided = some v)
              ∨ ¬isCorrect n (exec.drop k e 0) q := by
  obtain ⟨k₁, hready⟩ := milestone_vote_amplify n f input hn e hsafety hfair
  -- Per-receiver decide delivery primitive: case-split on milestone 4b's
  -- disjuncts, rebase to step `j + k₁` via persistence, dispatch to
  -- `decide_delivery_binary` / `decide_delivery_none`.
  have hdel : ∀ q (_r : Fin n) (j : Nat), ∃ j',
      (∃ v', ((exec.drop ((j + k₁) + j') e 0).local_ q).decided = some v')
        ∨ ¬isCorrect n (exec.drop ((j + k₁) + j') e 0) q := by
    intro q _r j
    rcases hready q with hbinary | hboth | hnc
    · -- Case I: ∃ b, countVoteRecv (some b) ≥ n - f.
      obtain ⟨b, hqb⟩ := hbinary
      by_cases hcq_eff : isCorrect n (exec.drop (j + k₁) e 0) q
      · have hqb_eff : countVoteRecv n ((exec.drop (j + k₁) e 0).local_ q) (some b) ≥ n - f := by
          have := countVoteRecv_persist n f input e hsafety q (some b) (n - f) k₁ j hqb
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        exact decide_delivery_binary n f input hn q b e hsafety hfair
          (j + k₁) hcq_eff hqb_eff
      · exact ⟨0, Or.inr hcq_eff⟩
    · -- Case II: approved both + countAnyVoteRecv ≥ n - f.
      obtain ⟨happ_f, happ_t, hany⟩ := hboth
      by_cases hcq_eff : isCorrect n (exec.drop (j + k₁) e 0) q
      · have happ_f_eff : ((exec.drop (j + k₁) e 0).local_ q).approved false = true := by
          have := approved_persist n f input e hsafety q false k₁ j happ_f
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        have happ_t_eff : ((exec.drop (j + k₁) e 0).local_ q).approved true = true := by
          have := approved_persist n f input e hsafety q true k₁ j happ_t
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        have hany_eff :
            countAnyVoteRecv n ((exec.drop (j + k₁) e 0).local_ q) ≥ n - f := by
          have := countAnyVoteRecv_persist n f input e hsafety q (n - f) k₁ j hany
          have heq : k₁ + j = j + k₁ := by omega
          rw [heq] at this ; exact this
        exact decide_delivery_none n f input hn q e hsafety hfair
          (j + k₁) hcq_eff happ_f_eff happ_t_eff hany_eff
      · exact ⟨0, Or.inr hcq_eff⟩
    · refine ⟨0, Or.inr ?_⟩
      have := isCorrect_persist n f input e hsafety q k₁ j hnc
      have heq : k₁ + j = j + k₁ := by omega
      rw [heq] at this ; exact this
  -- Reshape hdel (drop ignored receiver arg, absorb k₁ offset).
  have hdel' : ∀ q (k : Nat), ∃ k',
      (∃ v, ((exec.drop (k + k') e 0).local_ q).decided = some v)
        ∨ ¬isCorrect n (exec.drop (k + k') e 0) q := by
    intro q k
    obtain ⟨j', h⟩ := hdel q q k
    refine ⟨k₁ + j', ?_⟩
    rw [show k + (k₁ + j') = (k + k₁) + j' from by omega]
    exact h
  have hpersist : ∀ q (j d : Nat),
      (∃ v, ((exec.drop j e 0).local_ q).decided = some v) →
      (∃ v, ((exec.drop (j + d) e 0).local_ q).decided = some v) :=
    fun q j d ⟨v, hd⟩ => ⟨v, decided_persist n f input e hsafety q v j d hd⟩
  obtain ⟨k', hall⟩ := combine_senders n f input
    (fun q s => ∃ v, (s.local_ q).decided = some v)
    e hsafety hfair hdel' hpersist (List.finRange n) 0
  exact ⟨0 + k', fun q => hall q (List.mem_finRange q)⟩

/-! ## Main liveness theorem -/

/-- **BCA liveness (termination)**: under `n > 3 * f`, the BCA safety
    invariant, and weak fairness for every action (send-by-correct,
    recv, decide), every correct process eventually decides some
    value. This is the top-level liveness guarantee of the protocol. -/
theorem bca_all_correct_decide (input : Fin n → Bool) (hn : n > 3 * f)
    (e : exec (State n))
    (hsafety : (bca n f input).safety e)
    (hfair : bca_fairness n f input e) :
    ∃ k, ∀ q, isCorrect n (exec.drop k e 0) q →
              ∃ v, ((exec.drop k e 0).local_ q).decided = some v := by
  obtain ⟨k, h⟩ := milestone_termination n f input hn e hsafety hfair
  refine ⟨k, fun q hcq => ?_⟩
  rcases h q with hdec | hnc
  · exact hdec
  · exact absurd hcq hnc

end BindingCrusaderAgreement
