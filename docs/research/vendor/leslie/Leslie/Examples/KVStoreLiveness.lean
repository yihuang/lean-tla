import Leslie.Examples.KVStore
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## KVStore Liveness: Replica Convergence

    Under weak fairness of `consume r`, every replica eventually catches up.
    Specifically, if `cursor r = k` and `k < journal.length`, then eventually
    `cursor r ≥ k + 1`.

    **Property**: `∀ k, (cursor r = k ∧ k < journal.length) ↝ cursor r ≥ k + 1`

    Demonstrates: WF1 application for an `ActionSpec`.
-/

open TLA

namespace KVStore

/-! ### Fair specification with WF on all consume actions -/

def kvstoreFair : ActionSpec KVState KVAction :=
  { kvstore with fair := [.consume .r1, .consume .r2, .consume .r3] }

/-! ### State-level helper lemmas -/

/-- Consume is enabled when cursor < journal.length. -/
theorem consume_enabled (r : Replica) (s : KVState)
    (hlt : s.cursor r < s.journal.length) :
    enabled (kvstoreFair.actions (.consume r)).toAction s := by
  simp [enabled, GatedAction.toAction, GatedAction.fires]
  refine ⟨hlt, ?_⟩
  exact ⟨{ s with
    store := fun r' => if r' = r then some s.journal[s.cursor r] else s.store r'
    cursor := fun r' => if r' = r then s.cursor r + 1 else s.cursor r' },
    s.journal[s.cursor r],
    by simp [List.getElem?_eq_getElem hlt],
    rfl⟩

/-- Safety: if p(k) holds in pre-state and some action fires, then p(k) or q(k) holds in post-state.
    p(k) = "kv_inv ∧ cursor r = k ∧ k < journal.length"
    q(k) = "cursor r ≥ k + 1" -/
private theorem safety_step (r : Replica) (k : Nat) (s s' : KVState)
    (hinv : kv_inv s) (hck : s.cursor r = k) (hlt : k < s.journal.length)
    (hstep : kvstoreFair.next s s') :
    (kv_inv s' ∧ s'.cursor r = k ∧ k < s'.journal.length) ∨
    (s'.cursor r ≥ k + 1) := by
  obtain ⟨i, hfire⟩ := hstep
  have hinv' : kv_inv s' :=
    kv_inv_next s s' hinv ⟨i, hfire⟩
  cases i with
  | acquire r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstoreFair, kvstore] at ht; subst ht
    left; exact ⟨hinv', hck, hlt⟩
  | writeFail r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstoreFair, kvstore] at ht; subst ht
    left; exact ⟨hinv', hck, hlt⟩
  | writeOk r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstoreFair, kvstore] at ht
    obtain ⟨v, ht⟩ := ht; subst ht; dsimp only
    by_cases h : r = r'
    · subst h; simp; right; omega
    · left; exact ⟨hinv', by rw [if_neg h]; exact hck,
                           by simp [List.length_append]; omega⟩
  | consume r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstoreFair, kvstore] at ht
    obtain ⟨v, _, ht⟩ := ht; subst ht; dsimp only
    by_cases h : r = r'
    · subst h; simp; right; omega
    · simp [h]; left; exact ⟨hinv', hck, hlt⟩

/-- Progress: if p(k) holds and consume r fires, then q(k) holds in post-state. -/
private theorem progress_step (r : Replica) (k : Nat) (s s' : KVState)
    (hck : s.cursor r = k) (_hlt : k < s.journal.length)
    (hact : (kvstoreFair.actions (.consume r)).toAction s s') :
    s'.cursor r ≥ k + 1 := by
  simp [GatedAction.toAction, GatedAction.fires, kvstoreFair, kvstore] at hact
  obtain ⟨_, v, _, ht⟩ := hact; subst ht
  simp; omega

/-! ### WF1: single-step progress for consume r -/

theorem consume_progress (r : Replica) (k : Nat) :
    pred_implies kvstoreFair.toSpec.formula
      (leads_to (state_pred (fun s : KVState => kv_inv s ∧ s.cursor r = k ∧ k < s.journal.length))
                (state_pred (fun s : KVState => s.cursor r ≥ k + 1))) := by
  intro e ⟨_, hnext, hwf_all⟩
  -- Extract WF(consume r) from the fairness list
  have hwf : weak_fairness (kvstoreFair.actions (.consume r)).toAction e := by
    simp only [kvstoreFair, tla_bigwedge, Foldable.fold, tla_true] at hwf_all
    cases r with
    | r1 => exact hwf_all.1
    | r2 => exact hwf_all.2.1
    | r3 => exact hwf_all.2.2.1
  -- The next relation
  have hnext' : always (action_pred kvstoreFair.next) e := by
    intro k; exact hnext k
  -- Apply WF1 rule
  apply wf1
    (state_pred (fun s : KVState => kv_inv s ∧ s.cursor r = k ∧ k < s.journal.length))
    (state_pred (fun s : KVState => s.cursor r ≥ k + 1))
    kvstoreFair.next
    (kvstoreFair.actions (.consume r)).toAction
    e
  refine ⟨?safety, ?progress, ?enablement, hnext', hwf⟩
  case safety =>
    intro m ⟨hp, hstep⟩
    simp only [action_pred, state_pred, exec.drop, Nat.add_zero] at hp hstep ⊢
    obtain ⟨hinv, hck, hlt⟩ := hp
    exact safety_step r k _ _ hinv hck hlt hstep
  case progress =>
    intro m ⟨hp, _, hact⟩
    simp only [action_pred, state_pred, exec.drop, later, Nat.add_zero] at hp hact ⊢
    exact progress_step r k _ _ hp.2.1 hp.2.2 hact
  case enablement =>
    intro m hp
    simp only [state_pred, tla_enabled, tla_or, exec.drop] at hp ⊢
    obtain ⟨_, hck, hlt⟩ := hp
    left
    exact consume_enabled r _ (by omega)

/-! ### Corollary: cleaner formulation

    Under the fair spec, if cursor r < journal.length, eventually cursor r advances. -/

theorem consume_eventually_advances (r : Replica) (k : Nat) :
    pred_implies kvstoreFair.toSpec.formula
      (leads_to (state_pred (fun s : KVState => kv_inv s ∧ s.cursor r = k ∧ k < s.journal.length))
                (state_pred (fun s : KVState => s.cursor r ≥ k + 1))) :=
  consume_progress r k

end KVStore
