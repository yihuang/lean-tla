import Leslie.SymShared

/-! ## `action_cases` tactic for SymSharedSpec protocols.

    When proving preservation or simulation theorems for a `SymSharedSpec`,
    the standard boilerplate is:

    ```
    simp only [SymSharedSpec.toSpec, mySpec] at hnext
    obtain ⟨i, a, hstep⟩ := hnext
    match a with
    | .action1 args => ...
    ```

    The `action_cases hnext with mySpec` tactic automates the first two steps.

    Usage:

    ```lean
    theorem myInv_preserved ... (hnext : (mySpec.toSpec n).next s s') : ... := by
      action_cases hnext with mySpec
      match a with
      | .action1 args => ...
    ```
-/

namespace Leslie.ActionCases

open SymShared in
/-- `action_cases h with spec` unfolds `SymSharedSpec.toSpec` and `spec` in
    hypothesis `h`, then destructs `∃ i a, step ...` into `i`, `a`, `hstep`. -/
macro "action_cases " h:ident " with " spec:ident : tactic =>
  `(tactic| (
    simp only [SymSharedSpec.toSpec, $spec:ident] at $h:ident
    obtain ⟨i, a, hstep⟩ := $h:ident))

end Leslie.ActionCases
