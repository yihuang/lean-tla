import Lean

open Lean Elab Command

/-! # `tla_var`: declare TLA variables with one command

`tla_var St x y` declares, in the current namespace:

```
def x : St → _ := fun s => St.x s
def y : St → _ := fun s => St.y s
def vars : St → St := fun s => s
```

plus `[simp]` lemmas (`x_apply`, `y_apply`, `vars_apply`) so that `simp` and
`omega` recognize `x s` and `s.x` as the same atom. `vars` is the default
stuttering frame for `□[Next]_vars` (all variables); define a custom
tuple-valued frame for a narrower view.

Usage note: proofs should use plain `simp`/`tla_unfold` (the `_apply` lemmas
are in the global simp set). Do not list a generated variable explicitly
(`simp [x]`) — programmatically declared constants are not unfoldable that
way.
-/

syntax "tla_var" ident ident+ : command

elab_rules : command
  | `(tla_var $st:ident $flds:ident*) => do
      let ns ← getCurrNamespace
      let stType ← liftTermElabM <| Term.elabType st
      let stName := stType.constName!
      let addVar (name : Name) (body : Syntax) (lemma : Syntax) := do
        let declName := ns ++ name
        let value ← liftTermElabM <| do
          let v ← Term.elabTerm body none
          instantiateMVars v
        let type ← liftTermElabM <| do
          let t ← Lean.Meta.inferType value
          instantiateMVars t
        liftCoreM <| Lean.addAndCompile <| Declaration.defnDecl {
          name := declName, levelParams := [], type := type, value := value,
          hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe
        }
        let thmName := declName.appendAfter "_apply"
        let thmType ← liftTermElabM <| do
          let t ← Term.elabType lemma
          instantiateMVars t
        let proof ← liftTermElabM <| do
          let p ← Term.elabTerm (← `(fun s : $st => rfl)) (some thmType)
          instantiateMVars p
        liftCoreM <| addDecl <| Declaration.thmDecl {
          name := thmName, levelParams := [], type := thmType, value := proof
        }
        liftTermElabM <| Lean.Meta.addSimpTheorem Lean.Meta.simpExtension thmName false false AttributeKind.global 0
      for fld in flds do
        let proj : TSyntax `ident := mkCIdent (stName ++ fld.getId)
        let varId : TSyntax `ident := mkCIdent (ns ++ fld.getId)
        addVar fld.getId (← `(fun s : $st => $proj s)) (← `(∀ s : $st, $varId s = $proj s))
      let varsId : TSyntax `ident := mkCIdent (ns ++ `vars)
      addVar `vars (← `(fun s : $st => s)) (← `(∀ s : $st, $varsId s = s))
