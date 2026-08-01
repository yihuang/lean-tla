import Leslie.Action

/-! # Quorum and counting lemmas

  General-purpose lemmas for quorum intersection and pigeonhole arguments
  over `Fin n` and `List.finRange`. Used by Byzantine protocol proofs
  (BRB, BCA, etc.).
-/

/-- A nodup sublist has bounded length. If every element of `l` appears
    in `m` and `l` has no duplicates, then `l.length ≤ m.length`. -/
theorem nodup_sub_length {α : Type} [DecidableEq α]
    {l m : List α} (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ m) :
    l.length ≤ m.length := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    have ⟨hat, hnd_t⟩ := List.nodup_cons.mp hnd
    have ha := hsub a (List.mem_cons.mpr (.inl rfl))
    have h1 := ih hnd_t fun x hx =>
      (List.mem_erase_of_ne (show x ≠ a from fun h => hat (h ▸ hx))).mpr
        (hsub x (List.mem_cons.mpr (.inr hx)))
    have h2 := List.length_erase_of_mem ha
    have : m.length ≥ 1 := by cases m with | nil => simp at ha | cons => simp
    simp [List.length_cons] ; omega

/-- `List.finRange n` has no duplicates.
    Basis for all counting arguments over process indices. -/
theorem finRange_nodup : ∀ n, (List.finRange n).Nodup := by
  intro n ; induction n with
  | zero => simp [List.finRange]
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨by simp [List.mem_map] ; exact fun _ => Fin.succ_ne_zero _,
      ih.map Fin.succ fun a b hab heq =>
        hab (by simp [Fin.ext_iff, Fin.val_succ] at heq ; exact Fin.ext heq)⟩

/-- Monotonicity: if P implies Q pointwise then |filter P| ≤ |filter Q|. -/
theorem filter_length_mono {α : Type} (P Q : α → Bool) (l : List α)
    (h : ∀ x, P x = true → Q x = true) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases hpa : P a <;> cases hqa : Q a <;> simp_all <;> omega

/-- |filter (P ∧ Q)| ≤ |filter Q|: a conjunctive filter is bounded
    by either conjunct alone. -/
theorem filter_and_le {α : Type} (P Q : α → Bool) (l : List α) :
    (l.filter (fun x => P x && Q x)).length ≤ (l.filter Q).length := by
  rw [← List.filter_filter] ; exact List.filter_sublist.length_le

/-- |filter P| = |filter (P ∧ Q)| + |filter (P ∧ ¬Q)|: decompose
    a filter into two disjoint parts.
    Core lemma for quorum intersection arguments. -/
theorem filter_split {α : Type} [DecidableEq α] (P Q : α → Bool) (l : List α) :
    (l.filter P).length =
    (l.filter (fun x => P x && Q x)).length +
    (l.filter (fun x => P x && !Q x)).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases P a <;> cases Q a <;> simp <;> omega

/-- If a `Bool`-valued predicate `A` holds for every non-corrupted
    element of `Fin n`, and the corruption budget is `≤ f`, then at
    least `n − f` elements satisfy `A`. Pure counting corollary of
    `intersect_correct_ge` specialized to `M := fun _ => true`. -/
theorem count_correct_ge {n f : Nat} (corrupted : List (Fin n))
    (hbudget : corrupted.length ≤ f) (A : Fin n → Bool)
    (hall : ∀ p, p ∉ corrupted → A p = true) :
    ((List.finRange n).filter A).length ≥ n - f := by
  -- Let C := "not in corrupted". For every correct p, A p holds, so
  -- |filter A| ≥ |filter C|. And |filter C| ≥ n − f by budget.
  have hmono : ((List.finRange n).filter
      (fun p => decide (p ∉ corrupted))).length ≤
      ((List.finRange n).filter A).length := by
    apply filter_length_mono
    intro p hp
    simp only [decide_eq_true_eq] at hp
    exact hall p hp
  -- |filter ¬(· ∉ corrupted)| ≤ |corrupted| ≤ f
  have hneg_le :
      ((List.finRange n).filter (fun p => !decide (p ∉ corrupted))).length ≤ f := by
    calc ((List.finRange n).filter (fun p => !decide (p ∉ corrupted))).length
        ≤ corrupted.length := by
          apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
          intro x hx
          simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not,
            Classical.not_not] at hx
          exact hx.2
      _ ≤ f := hbudget
  -- |filter (· ∉ corrupted)| + |filter ¬(· ∉ corrupted)| = n, via filter_split.
  have hsplit := filter_split (fun _ : Fin n => true)
    (fun p => decide (p ∉ corrupted)) (List.finRange n)
  -- Rewrite the three filter expressions to match.
  have htriv : (List.finRange n).filter (fun _ : Fin n => true) = List.finRange n := by
    apply List.filter_eq_self.mpr ; intros ; rfl
  have heq1 : ((List.finRange n).filter
      (fun x => (fun _ : Fin n => true) x && decide (x ∉ corrupted))).length =
      ((List.finRange n).filter (fun p => decide (p ∉ corrupted))).length := rfl
  have heq2 : ((List.finRange n).filter
      (fun x => (fun _ : Fin n => true) x && !decide (x ∉ corrupted))).length =
      ((List.finRange n).filter (fun p => !decide (p ∉ corrupted))).length := rfl
  rw [htriv, heq1, heq2] at hsplit
  have hfin : (List.finRange n).length = n := List.length_finRange
  omega

/-- Budget → intersected count: if `|filter M| ≥ k` and `|corrupted| ≤ f`,
    then `|filter (M ∧ · ∉ corrupted)| ≥ k − f`. -/
theorem intersect_correct_ge {n f k : Nat} (corrupted : List (Fin n)) (M : Fin n → Bool)
    (hbudget : corrupted.length ≤ f)
    (hM : ((List.finRange n).filter M).length ≥ k) :
    ((List.finRange n).filter (fun s => M s && decide (s ∉ corrupted))).length ≥ k - f := by
  have hsplit := filter_split M (fun s => decide (s ∉ corrupted)) (List.finRange n)
  have hMnotC_le : ((List.finRange n).filter
      (fun s => M s && !decide (s ∉ corrupted))).length ≤ f := by
    calc ((List.finRange n).filter (fun s => M s && !decide (s ∉ corrupted))).length
        ≤ ((List.finRange n).filter (fun s => !decide (s ∉ corrupted))).length :=
          filter_and_le M (fun s => !decide (s ∉ corrupted)) _
      _ ≤ corrupted.length := by
          apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
          intro x hx ; simp [List.mem_filter] at hx ; exact hx
      _ ≤ f := hbudget
  omega

/-- Subadditivity: |filter (P ∨ Q)| ≤ |filter P| + |filter Q|.
    Useful for Boolean pigeonhole: if the disjunction has many elements,
    one of the disjuncts must too. -/
theorem filter_or_le {α : Type} (P Q : α → Bool) (l : List α) :
    (l.filter (fun x => P x || Q x)).length ≤
    (l.filter P).length + (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases P a <;> cases Q a <;> simp <;> omega

/-- Strict monotonicity: if P implies Q pointwise and there exists an element
    where Q holds but P doesn't, then |filter Q| ≥ |filter P| + 1.
    Useful when a new entry is added to a Boolean predicate. -/
theorem filter_length_strict_mono {n : Nat} (P Q : Fin n → Bool)
    (hmono : ∀ x, P x = true → Q x = true)
    (x : Fin n) (hP : P x = false) (hQ : Q x = true) :
    ((List.finRange n).filter Q).length ≥ ((List.finRange n).filter P).length + 1 := by
  -- The old filter is a sublist of the new (monotonicity).
  -- x is in new but not old. So |new| ≥ |old| + 1.
  -- Strategy: filter Q = filter (P ∨ (· = x)) ∪ ... ≥ filter P + 1.
  -- Simpler: use filter_split with Q decomposed as (P ∧ Q) + (¬P ∧ Q).
  -- |filter Q| = |filter (P ∧ Q)| + |filter (¬P ∧ Q)|.
  -- |filter (P ∧ Q)| = |filter P| (since P → Q).
  -- |filter (¬P ∧ Q)| ≥ 1 (x is in it).
  have hsplit := filter_split Q P (List.finRange n)
  -- hsplit : |filter Q| = |filter (Q ∧ P)| + |filter (Q ∧ ¬P)|
  have heq : ((List.finRange n).filter (fun x => Q x && P x)).length =
      ((List.finRange n).filter P).length := by
    congr 1 ; apply List.filter_congr
    intro y _
    cases hpy : P y <;> cases hqy : Q y <;> simp_all
  have hge : ((List.finRange n).filter (fun x => Q x && !P x)).length ≥ 1 := by
    have : x ∈ (List.finRange n).filter (fun y => Q y && !P y) := by
      simp [List.mem_filter, hP, hQ]
    match h : (List.finRange n).filter (fun y => Q y && !P y) with
    | [] => exact absurd (List.mem_nil_iff x |>.mp (h ▸ this)) (by simp)
    | _ :: _ => simp
  omega

/-- Pigeonhole: if |{r | P r}| > |corrupted|, some r satisfies P
    and is not corrupted. -/
theorem pigeonhole_filter {n : Nat} (P : Fin n → Bool) (corrupted : List (Fin n))
    (hgt : corrupted.length < ((List.finRange n).filter P).length) :
    ∃ q, P q = true ∧ q ∉ corrupted := by
  let Q : Fin n → Bool := fun x => decide (x ∈ corrupted)
  have hsplit := filter_split P Q (List.finRange n)
  have hle : ((List.finRange n).filter (fun x => P x && Q x)).length ≤
      corrupted.length := by
    calc ((List.finRange n).filter (fun x => P x && Q x)).length
        ≤ ((List.finRange n).filter Q).length := filter_and_le P Q _
      _ ≤ corrupted.length := by
          apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
          intro x hx ; simp [Q, List.mem_filter] at hx ; exact hx
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos (by omega :
    0 < ((List.finRange n).filter (fun x => P x && !Q x)).length)
  have ⟨_, hq2⟩ := List.mem_filter.mp hq
  simp only [Q, Bool.and_eq_true, Bool.not_eq_true'] at hq2
  exact ⟨q, hq2.1, fun h => by simp [h] at hq2⟩

/-- **Echo quorum intersection (abstract)**: given two echo quorums of size ≥ n−f
    for values `v` and `w` at processes `p1` and `p2`, and the echo trace property
    (each correct echoRecv source has `echoed = some v` for that value), we must
    have `v = w`.

    The argument: each quorum has ≥ n−2f correct sources (at most f are corrupt).
    By the echo trace, these correspond to correct processes with `echoed = some v`
    or `echoed = some w`. Since `echoed : Option α` assigns at most one value per
    process, the two sets of correct processes are disjoint. The three-way bound
    `|correct_v| + |correct_w| + |corrupted| ≤ n` combined with the quorum counts
    forces `n ≤ 3f`, contradicting `n > 3f`. -/
theorem echo_quorum_intersection {n f : Nat} {α : Type} [DecidableEq α]
    (hn : n > 3 * f)
    (v w : α) (p1 p2 : Fin n)
    (echoRecv : Fin n → Fin n → α → Bool)
    (echoed : Fin n → Option α)
    (corrupted : List (Fin n))
    (hbudget : corrupted.length ≤ f)
    (hetrace : ∀ p q val, p ∉ corrupted →
      echoRecv q p val = true → echoed p = some val)
    (hv : ((List.finRange n).filter (echoRecv p1 · v)).length ≥ n - f)
    (hw : ((List.finRange n).filter (echoRecv p2 · w)).length ≥ n - f) :
    v = w := by
  by_contra hvw
  -- Helper: correct echoRecv sources at proc for val have echoed = some val
  have echo_mono := fun (proc : Fin n) (val : α) =>
    filter_length_mono
      (fun r => echoRecv proc r val && !decide (r ∈ corrupted))
      (fun r => decide (r ∉ corrupted) && decide (echoed r = some val))
      (List.finRange n)
      (fun r hr => by
        rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hr
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨hr.2, hetrace r proc val hr.2 hr.1⟩)
  -- cc = distinct corrupted count (≤ corrupted.length ≤ f)
  let cc := ((List.finRange n).filter (fun r => decide (r ∈ corrupted))).length
  have hcc_le : cc ≤ f :=
    Nat.le_trans
      (nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
        (fun x hx => by simp [List.mem_filter] at hx ; exact hx))
      hbudget
  -- correct-echoed-v ≥ n - f - cc
  have hcount_v : ((List.finRange n).filter (fun r =>
      decide (r ∉ corrupted) && decide (echoed r = some v))).length ≥ n - f - cc := by
    apply Nat.le_trans _ (echo_mono p1 v)
    have hsplit := filter_split (echoRecv p1 · v)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    have hle := filter_and_le (echoRecv p1 · v)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    omega
  have hcount_w : ((List.finRange n).filter (fun r =>
      decide (r ∉ corrupted) && decide (echoed r = some w))).length ≥ n - f - cc := by
    apply Nat.le_trans _ (echo_mono p2 w)
    have hsplit := filter_split (echoRecv p2 · w)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    have hle := filter_and_le (echoRecv p2 · w)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    omega
  -- Three-way bound: correct-v + correct-w + corrupted ≤ n
  -- Disjoint because echoed : Option α (at most one value per process)
  have h3 : ∀ (l : List (Fin n)),
      (l.filter (fun r => decide (r ∉ corrupted) && decide (echoed r = some v))).length +
      (l.filter (fun r => decide (r ∉ corrupted) && decide (echoed r = some w))).length +
      (l.filter (fun r => decide (r ∈ corrupted))).length
      ≤ l.length := by
    intro l ; induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.filter_cons, List.length_cons]
      split <;> split <;> split <;> simp_all
      all_goals first | omega
  have h3way := h3 (List.finRange n)
  have hlen : (List.finRange n).length = n := List.length_finRange
  have hcv_add : n ≤ ((List.finRange n).filter (fun r =>
    decide (r ∉ corrupted) && decide (echoed r = some v))).length
    + f + corrupted.length := by omega
  have hcw_add : n ≤ ((List.finRange n).filter (fun r =>
    decide (r ∉ corrupted) && decide (echoed r = some w))).length
    + f + corrupted.length := by omega
  omega
