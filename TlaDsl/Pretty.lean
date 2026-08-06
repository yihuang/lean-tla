import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Prime

open Lean PrettyPrinter PrettyPrinter.Delaborator PrettyPrinter.Delaborator.SubExpr Meta

namespace Tla

/-! # Pretty printing: goals read like TLA

`app_unexpander`s invert the `[t| ...]` macro: temporal formulas built from
`tlaAnd`/`always`/`stutAlways`/... are displayed with the TLA notation
(`∧`, `□`, `□[A]_v`, `⌜ p ⌝`, ...) instead of raw lifted lambdas, so goals
and hypotheses are readable without `set_option pp.all`. A `@[delab lam]`
at the bottom of this file inverts the state/action brackets too: lifted
state predicates and actions print as `[p| ...]` / `[a| ...]` again.
-/

@[app_unexpander Tla.tlaAnd]
def unexpTlaAnd : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ∧ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaOr]
def unexpTlaOr : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ∨ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaImp]
def unexpTlaImp : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ⇒ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaIff]
def unexpTlaIff : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ↔ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaNot]
def unexpTlaNot : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(¬ $F)
  | _ => pure stx

@[app_unexpander Tla.tlaForall]
def unexpTlaForall : Unexpander := fun stx => do
  match stx with
  | `($_ fun $x:ident => $F) => `(∀ $x:ident, $F)
  | _ => pure stx

@[app_unexpander Tla.tlaExists]
def unexpTlaExists : Unexpander := fun stx => do
  match stx with
  | `($_ fun $x:ident => $F) => `(∃ $x:ident, $F)
  | _ => pure stx

@[app_unexpander Tla.always]
def unexpAlways : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(□ $F)
  | _ => pure stx

@[app_unexpander Tla.eventually]
def unexpEventually : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(◇ $F)
  | _ => pure stx

@[app_unexpander Tla.later]
def unexpLater : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(◯ $F)
  | _ => pure stx

@[app_unexpander Tla.stutAlways]
def unexpStutAlways : Unexpander := fun stx => do
  match stx with
  | `($_ $next $v) => `(□[$next]_$v)
  | _ => pure stx

@[app_unexpander Tla.leadsTo]
def unexpLeadsTo : Unexpander := fun stx => do
  match stx with
  | `($_ $P $Q) => `($P ↝ $Q)
  | _ => pure stx

@[app_unexpander Tla.strongUntil]
def unexpStrongUntil : Unexpander := fun stx => do
  match stx with
  | `($_ $P $Q) => `($P 𝑈 $Q)
  | _ => pure stx

@[app_unexpander Tla.statePred]
def unexpStatePred : Unexpander := fun stx => do
  match stx with
  | `($_ $p) => `(⌜$p⌝)
  | _ => pure stx

@[app_unexpander Tla.purePred]
def unexpPurePred : Unexpander := fun stx => do
  match stx with
  | `($_ $p) => `(⌞$p⌟)
  | _ => pure stx

/-! ### State/action bracket delaborators

`[p| ...]` and `[a| ...]` elaborate to plain lambdas, so without this file
goals show `fun s => x s = 0 ∧ y s = 0` again. The delaborators below
invert that for the recognizable shapes: a `σ → Prop` lambda whose state
variable only ever occurs as the first argument of a state function (a
`tla_var` abbreviation or a structure projection) is displayed as
`[p| x = 0 ∧ y = 0]`, and a `σ → σ → Prop` lambda as
`[a| x' = x + 1 ∧ y' = y]` with the post-state applications primed.
Everything else falls through to the default lambda delaborator, so
ordinary lambdas and value binders (`∀ C : Block, C ∈ ...`) are untouched.
-/

/-- Is `f` a state function: a `tla_var`-style abbreviation or a structure
projection? -/
def isStateFunction (env : Environment) (f : Expr) : Bool :=
  match f with
  | .const n _ =>
      match env.find? n with
      | some (ConstantInfo.defnInfo d) =>
          if d.hints.isAbbrev then true
          else
            let structName := n.getPrefix
            isStructure env structName &&
              (getFieldInfo? env structName (Name.mkSimple (n.getString!)) |>.isSome)
      | _ => false
  | _ => false

/-- Does `e` contain the free variable `s`? -/
def containsFVar (s : FVarId) : Expr → Bool
  | .fvar f => f == s
  | .app f a => containsFVar s f || containsFVar s a
  | .lam _ d b _ => containsFVar s d || containsFVar s b
  | .forallE _ d b _ => containsFVar s d || containsFVar s b
  | .letE _ t v b _ => containsFVar s t || containsFVar s v || containsFVar s b
  | .mdata _ e => containsFVar s e
  | .proj _ _ e => containsFVar s e
  | _ => false

/-- Every occurrence of the state variable `s` in `e` is the first argument
of a state-function application `f s` (so it can be elided in the
`[p|]/[a| ...]` display). -/
partial def stateVarElidable (env : Environment) (s : FVarId) (e : Expr) : Bool :=
  match e with
  | .fvar f => f != s
  | .app f a =>
      let a := a.consumeMData
      if a.isFVar && a.fvarId! == s then
        isStateFunction env f && !containsFVar s f
      else
        stateVarElidable env s f && stateVarElidable env s a
  | .lam _ d b _ => stateVarElidable env s d && stateVarElidable env s b
  | .forallE _ d b _ => stateVarElidable env s d && stateVarElidable env s b
  | .letE _ t v b _ => stateVarElidable env s t && stateVarElidable env s v && stateVarElidable env s b
  | .mdata _ e => stateVarElidable env s e
  | .proj _ _ e => stateVarElidable env s e
  | _ => true

/-- The arity of a bracketable state/action lambda: `some 1` for `σ → Prop`,
`some 2` for `σ → σ → Prop`, `none` otherwise. -/
def stateLamArity (e : Expr) : MetaM (Option Nat) := do
  let t ← whnf (← inferType e)
  match t with
  | .forallE _ _ c1 _ =>
      match (← whnf c1) with
      | Expr.sort _ => pure (some 1)
      | .forallE _ _ c2 _ =>
          match (← whnf c2) with
          | Expr.sort _ => pure (some 2)
          | _ => pure none
      | _ => pure none
  | _ => pure none

def isStructureType (e : Expr) : MetaM Bool := do
  let t ← whnf (← inferType e)
  match t.consumeMData.const? with
  | some (n, _) => pure (isStructure (← getEnv) n)
  | none => pure false

/-- Strip `null` wrappers that delaborated arguments are sometimes wrapped
in. -/
partial def stripNull : Syntax → Syntax
  | stx =>
      if stx.isOfKind nullKind then
        let args := stx.getArgs
        if args.size == 1 then stripNull args[0]! else stx
      else stx

/-- Rewrite `f s` to `f` (or `f'` when `post`) and `s.x` to `x` (or `x'`),
recursively, in a delabbed body. -/
partial def elideStateSyntaxAux (post : Bool) (sid : Name) : Syntax → Syntax
  | stx =>
      if stx.isOfKind ``Lean.Parser.Term.app then
        let args := stx.getArgs
        if args.size ≥ 2 then
          -- applications delaborate as `app(f, argNode)` where `argNode`
          -- is a `null` node wrapping the arguments; state-first means the
          -- first wrapped argument is the state
          let argNode := args[1]!
          let argList := argNode.getArgs
          if argList.size ≥ 1 then
            let a0 := stripNull argList[0]!
            if a0.isIdent && a0.getId == sid then
              let rest := argList.drop 1
              if rest.isEmpty then
                let f := stripNull args[0]!
                if f.isIdent then
                  if post then mkIdent (f.getId.appendAfter "'") else mkIdent f.getId
                else stx
              else
                let newArg : Syntax := argNode.modifyArgs (fun _ => rest)
                stx.modifyArgs (fun _ => #[args[0]!, newArg])
            else
              -- the state may be the base of a field-notation function:
              -- `app(proj(s, f), args...)`
              let f := stripNull args[0]!
              if f.isOfKind ``Lean.Parser.Term.proj then
                let pargs := f.getArgs
                if pargs.size ≥ 3 then
                  let b := stripNull pargs[0]!
                  let field := stripNull pargs[2]!
                  if b.isIdent && b.getId == sid && field.isIdent then
                    let newFn := if post then mkIdent (field.getId.appendAfter "'") else mkIdent field.getId
                    stx.modifyArgs (fun _ => #[newFn, args[1]!])
                  else
                    stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))
                else
                  stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))
              else
                stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))
          else
            stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))
        else
          stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))
      else if stx.isOfKind ``Lean.Parser.Term.proj then
        let args := stx.getArgs
        -- the node is `[base, ".", field]`
        if args.size ≥ 3 then
          let b := stripNull args[0]!
          let field := stripNull args[2]!
          if b.isIdent && b.getId == sid && field.isIdent then
            if post then mkIdent (field.getId.appendAfter "'") else mkIdent field.getId
          else
            stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))
        else
          stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))
      else
        stx.modifyArgs (fun as => as.map (elideStateSyntaxAux post sid))

def elideStateSyntax (post : Bool) (sName : Syntax) (stx : Syntax) : Syntax :=
  elideStateSyntaxAux post sName.getId stx

/-- The bracket shape of `e`: `some 1` for a state predicate, `some 2` for
an action, `none` for anything else (checked against the environment's
state structures). -/
def bracketShape (env : Environment) (e : Expr) : MetaM (Option Nat) := do
  let some arity ← stateLamArity e | pure none
  lambdaTelescope e fun xs body => do
    match arity with
    | 1 =>
        if xs.size != 1 then pure none
        else if !(← isStructureType xs[0]!) then pure none
        else if !stateVarElidable env xs[0]!.fvarId! body then pure none
        else pure (some 1)
    | _ =>
        if xs.size != 2 then pure none
        else if !(← isStructureType xs[0]!) || !(← isStructureType xs[1]!) then pure none
        else if !(← isDefEq (← inferType xs[0]!) (← inferType xs[1]!)) then pure none
        else if !stateVarElidable env xs[0]!.fvarId! body ||
                !stateVarElidable env xs[1]!.fvarId! body then pure none
        else pure (some 2)

/-- Delaborate `fun s => ...` / `fun s t => ...` as `[p| ...]` / `[a| ...]`
when the state variable(s) only occur as state-function applications. -/
@[delab lam]
def delabBracketLam : Delab := do
  if (← getPPOption getPPAll) || !(← getPPOption getPPNotation) then failure
  let e ← getExpr
  let env ← getEnv
  let shape ← liftM (bracketShape env e)
  match shape with
  | none => failure
  | some 1 => do
      let (bodyStx, sName) ← withBindingBodyUnusedName fun n => return (← delab, n)
      let body' : Syntax := elideStateSyntax false sName bodyStx
      if Lean.Syntax.hasIdent sName.getId body' then failure
      let bodyTerm : TSyntax `term := ⟨body'⟩
      `([p| $bodyTerm])
  | _ => do
      let ((bodyStx, tName), sName) ← withBindingBodyUnusedName fun sN =>
        withBindingBodyUnusedName fun tN => return ((← delab, tN), sN)
      let body' : Syntax := elideStateSyntax true tName (elideStateSyntax false sName bodyStx)
      if Lean.Syntax.hasIdent sName.getId body' || Lean.Syntax.hasIdent tName.getId body' then failure
      let bodyTerm : TSyntax `term := ⟨body'⟩
      `([a| $bodyTerm])

end Tla
