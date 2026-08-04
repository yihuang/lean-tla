import Lean
import TlaDsl.Basic
import TlaDsl.Notation

open scoped Tla

open Lean Elab Term Meta

namespace Tla

/- The bracket-lifting elaborators are large `partial def`s; their pattern
matches grow with each supported binder form (∀, ∃, fun), and the LCNF
compiler needs a larger heartbeat budget than the elaboration default. -/
set_option maxHeartbeats 800000

/-! # Pseudocode action/state syntax

`[p| x = 0 ∧ y = 0]` elaborates to a `StatePred σ`, and
`[a| x' = x + 1 ∧ y' = y]` elaborates to an `Action σ`, via a dedicated
elaborator: it introduces fresh state variables and lifts every identifier
of state-function type (`σ → α`) to an application of the state variable.
`x'` denotes the post state value of `x`, `x` the pre state value.

Because lifting is type-directed rather than syntax-pattern-based, the
brackets accept anything Lean elaborates: operators and function
applications (`Even x`, `n % 2`), `if-then-else`, typed and bounded
quantifiers (`∀ x : T, ...`, `∀ x ∈ S, ...` over set-valued state
functions), constants, and plain non-state values (kept as-is).
`[t| ...]` rewrites propositional connectives to the temporal ones and
leaves everything else alone.
-/

/-! ## Pointwise operators at the state level -/

abbrev stEq {σ : Type u} {α : Type v} (f g : σ → α) : σ → Prop := fun s => f s = g s
abbrev stNe {σ : Type u} {α : Type v} (f g : σ → α) : σ → Prop := fun s => f s ≠ g s
abbrev stAnd {σ : Type u} (f g : σ → Prop) : σ → Prop := fun s => f s ∧ g s
abbrev stOr {σ : Type u} (f g : σ → Prop) : σ → Prop := fun s => f s ∨ g s
abbrev stNot {σ : Type u} (f : σ → Prop) : σ → Prop := fun s => ¬ f s
abbrev stImp {σ : Type u} (f g : σ → Prop) : σ → Prop := fun s => f s → g s
abbrev stAdd {σ : Type u} {α : Type v} [Add α] (f g : σ → α) : σ → α := fun s => f s + g s
abbrev stSub {σ : Type u} {α : Type v} [Sub α] (f g : σ → α) : σ → α := fun s => f s - g s
abbrev stMul {σ : Type u} {α : Type v} [Mul α] (f g : σ → α) : σ → α := fun s => f s * g s
abbrev stLt {σ : Type u} {α : Type v} [LT α] (f g : σ → α) : σ → Prop := fun s => f s < g s
abbrev stLe {σ : Type u} {α : Type v} [LE α] (f g : σ → α) : σ → Prop := fun s => f s ≤ g s
abbrev stGt {σ : Type u} {α : Type v} [LT α] (f g : σ → α) : σ → Prop := fun s => f s > g s
abbrev stGe {σ : Type u} {α : Type v} [LE α] (f g : σ → α) : σ → Prop := fun s => f s ≥ g s
abbrev stMod {σ : Type u} {α : Type v} [Mod α] (f g : σ → α) : σ → α := fun s => f s % g s

/-! ## Pointwise operators at the action level -/

abbrev actEq {σ : Type u} {α : Type v} (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t = g s t
abbrev actNe {σ : Type u} {α : Type v} (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t ≠ g s t
abbrev actAnd {σ : Type u} (f g : σ → σ → Prop) : σ → σ → Prop := fun s t => f s t ∧ g s t
abbrev actOr {σ : Type u} (f g : σ → σ → Prop) : σ → σ → Prop := fun s t => f s t ∨ g s t
abbrev actNot {σ : Type u} (f : σ → σ → Prop) : σ → σ → Prop := fun s t => ¬ f s t
abbrev actImp {σ : Type u} (f g : σ → σ → Prop) : σ → σ → Prop := fun s t => f s t → g s t
abbrev actAdd {σ : Type u} {α : Type v} [Add α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t + g s t
abbrev actSub {σ : Type u} {α : Type v} [Sub α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t - g s t
abbrev actMul {σ : Type u} {α : Type v} [Mul α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t * g s t
abbrev actLt {σ : Type u} {α : Type v} [LT α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t < g s t
abbrev actLe {σ : Type u} {α : Type v} [LE α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t ≤ g s t
abbrev actGt {σ : Type u} {α : Type v} [LT α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t > g s t
abbrev actGe {σ : Type u} {α : Type v} [LE α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t ≥ g s t
abbrev actMod {σ : Type u} {α : Type v} [Mod α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t % g s t

/-! ## The lifting elaborators -/

/-- The element type of a set-valued term (`Finset α`, `Set α`, or
`α → Prop`). -/
def elabElemType (lS : Expr) : TermElabM Expr := do
  let t ← whnf (← inferType lS)
  match t with
  | .forallE _ α β _ =>
      if (← isDefEq β (mkSort Level.zero)) then pure α
      else throwError s!"[p|]/[a| ...]: unsupported set type: {t}"
  | .app f a =>
      if f.isConst && f.constName == ``Finset then pure a
      else throwError s!"[p|]/[a| ...]: unsupported set type: {t}"
  | _ => throwError s!"[p|]/[a| ...]: unsupported set type: {t}"

/-- The `Prop` type, used as the expected type of formulas. -/
def propType : Expr := mkSort Level.zero

/--
Build `constName xs` like `mkAppM`, but without `withNewMCtxDepth`.
`mkAppM` bumps the metavariable depth and refuses to assign metavariables
created outside that scope, which breaks elaboration of untyped binders
(`∃ x, x = n` must assign the domain metavariable from inside `Eq`).
Here the argument-type checks run at the caller's depth, so outer
metavariables are assignable; instance arguments are synthesized after the
argument checks, once the instance type is fully determined.
-/
partial def mkOpAppExpr (f : Expr) (xs : Array Expr) : TermElabM Expr := do
  let fType ← inferType f
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr)
      (insts : Array MVarId) : TermElabM Expr := do
    if h : i >= xs.size then
      for inst in insts do
        let instType ← instantiateMVars (← inst.getType)
        let val ← synthInstance instType
        inst.assign val
      pure (mkAppN f args)
    else match type with
      | .forallE _ d b bi =>
          let d := d.instantiateRevRange j args.size args
          match bi with
          | .implicit | .strictImplicit =>
              let mvar ← mkFreshExprMVar d
              loop b i j (args.push mvar) insts
          | .instImplicit =>
              let mvar ← mkFreshExprMVar d MetavarKind.synthetic
              loop b i j (args.push mvar) (insts.push mvar.mvarId!)
          | _ =>
              let x := xs[i]
              let xType ← inferType x
              if (← withAtLeastTransparency .default (isDefEq d xType)) then
                loop b (i + 1) j (args.push x) insts
              else
                throwError "mkOpAppExpr: argument type mismatch: {x} has type {xType} but {d} is expected"
      | type =>
          let type := type.instantiateRevRange j args.size args
          let type ← whnfD type
          if type.isForall then loop type i args.size args insts
          else throwError "mkOpAppExpr: too many explicit arguments"
  loop fType 0 0 #[] #[]

partial def mkOpApp (constName : Name) (xs : Array Expr) : TermElabM Expr := do
  mkOpAppExpr (← mkConstWithFreshMVarLevels constName) xs

/-- Elaborate a term with the state variable `s` in scope, lifting
identifiers of state-function type (`σ → α`) to applications `x s`. `bound`
guards the identifiers bound by `∀`/`∃` inside the body. The expected type
is threaded through so that untyped literals (`0`, `∅`) are pinned by their
context, mirroring Lean's bidirectional elaboration. -/
partial def elabStateLiftCore (bound : NameSet) (s : Expr) (expected? : Option Expr)
    (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(($e)) => elabStateLiftCore bound s expected? e
  | `(($e : $T)) => do
      let t ← Term.elabType T
      elabStateLiftCore bound s (some t) e
  | `(∃ $x:ident : $T, $b) => do
      let t ← Term.elabType T
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? b
        let lam ← mkLambdaFVars #[xv] lb
        mkOpApp ``Exists #[lam]
  | `(∃ $x:ident ∈ $S, $b) => do
      let lS ← elabStateLiftCore bound s none S
      let elemType ← elabElemType lS
      withLocalDecl x.getId .default elemType fun xv => do
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? b
        let mem ← mkOpApp ``Membership.mem #[lS, xv]
        let conj ← mkOpApp ``And #[mem, lb]
        let lam ← mkLambdaFVars #[xv] conj
        mkOpApp ``Exists #[lam]
  | `(∃ $x:ident, $b) => do
      let t ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? b
        let lam ← mkLambdaFVars #[xv] lb
        mkOpApp ``Exists #[lam]
  | `(∀ $x:ident : $T, $b) => do
      let t ← Term.elabType T
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? b
        mkForallFVars #[xv] lb
  | `(∀ $x:ident ∈ $S, $b) => do
      let lS ← elabStateLiftCore bound s none S
      let elemType ← elabElemType lS
      withLocalDecl x.getId .default elemType fun xv => do
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? b
        let mem ← mkOpApp ``Membership.mem #[lS, xv]
        let imp ← withLocalDecl `_h .default mem fun h => mkForallFVars #[h] lb
        mkForallFVars #[xv] imp
  | `(∀ $x:ident, $b) => do
      let t ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? b
        mkForallFVars #[xv] lb
  | `(fun $x:ident $ys:ident* : $T => $b) => do
      let t ← Term.elabType T
      withLocalDecl x.getId .default t fun xv => do
        let rest ← if ys.isEmpty then pure b else `(fun $ys:ident* : $T => $b)
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? rest
        mkLambdaFVars #[xv] lb
  | `(fun $x:ident $ys:ident* => $b) => do
      let t ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
      withLocalDecl x.getId .default t fun xv => do
        let rest ← if ys.isEmpty then pure b else `(fun $ys:ident* => $b)
        let lb ← elabStateLiftCore (bound.insert x.getId) s expected? rest
        mkLambdaFVars #[xv] lb
  | `(if $c then $a else $b) => do
      let lc ← elabStateLiftCore bound s (some propType) c
      let la ← elabStateLiftCore bound s expected? a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``ite #[lc, la, lb]
  | `($a % $b) => do
      let la ← elabStateLiftCore bound s expected? a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HMod.hMod #[la, lb]
  | `($a + $b) => do
      let la ← elabStateLiftCore bound s expected? a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HAdd.hAdd #[la, lb]
  | `($a - $b) => do
      let la ← elabStateLiftCore bound s expected? a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HSub.hSub #[la, lb]
  | `($a * $b) => do
      let la ← elabStateLiftCore bound s expected? a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HMul.hMul #[la, lb]
  | `($a = $b) => do
      let la ← elabStateLiftCore bound s none a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``Eq #[la, lb]
  | `($a < $b) => do
      let la ← elabStateLiftCore bound s none a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``LT.lt #[la, lb]
  | `($a ≤ $b) => do
      let la ← elabStateLiftCore bound s none a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``LE.le #[la, lb]
  | `($a > $b) => do
      let la ← elabStateLiftCore bound s none a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``GT.gt #[la, lb]
  | `($a ≥ $b) => do
      let la ← elabStateLiftCore bound s none a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``GE.ge #[la, lb]
  | `($a ≠ $b) => do
      let la ← elabStateLiftCore bound s none a
      let lb ← elabStateLiftCore bound s (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``Ne #[la, lb]
  | `($a ∧ $b) => do
      let la ← elabStateLiftCore bound s (some propType) a
      let lb ← elabStateLiftCore bound s (some propType) b
      mkOpApp ``And #[la, lb]
  | `($a ∨ $b) => do
      let la ← elabStateLiftCore bound s (some propType) a
      let lb ← elabStateLiftCore bound s (some propType) b
      mkOpApp ``Or #[la, lb]
  | `($a → $b) => do
      let la ← elabStateLiftCore bound s (some propType) a
      let lb ← elabStateLiftCore bound s (some propType) b
      withLocalDecl `_h .default la fun h => mkForallFVars #[h] lb
  | `($a ⇒ $b) => do
      let la ← elabStateLiftCore bound s (some propType) a
      let lb ← elabStateLiftCore bound s (some propType) b
      withLocalDecl `_h .default la fun h => mkForallFVars #[h] lb
  | `(¬ $a) => do
      let la ← elabStateLiftCore bound s (some propType) a
      mkOpApp ``Not #[la]
  | stx =>
      if stx.isOfKind ``«term__[_]» then do
        let la ← elabStateLiftCore bound s expected? stx[0]
        let li ← elabStateLiftCore bound s none stx[2]
        let ty ← whnf (← inferType la)
        if ty.isForall then do
          let liTy ← inferType li
          match ty with
          | .forallE _ d _ _ =>
              unless (← isDefEq liTy d) do
                throwError "[p|]/[a| ...]: index type mismatch: {li} : {liTy} but the collection expects {d}"
          | _ => pure ()
          pure (mkApp la li)
        else do
          let laSyn ← Term.exprToSyntax la
          let liSyn ← Term.exprToSyntax li
          let t ← match expected? with
            | some t => pure t
            | none => mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
          Term.elabTerm (← `($laSyn[$liSyn])) (some t)
      else if stx.isOfKind ``Lean.Parser.Term.proj then do
        let la ← elabStateLiftCore bound s expected? stx[0]
        let ty ← whnf (← inferType la)
        match ty with
        | .const s _ =>
            let proj ← mkConstWithFreshMVarLevels (s ++ stx[2].getId)
            pure (mkApp proj la)
        | _ =>
            let laSyn ← Term.exprToSyntax la
            let field := mkIdent (stx[2].getId)
            let t ← match expected? with
              | some t => pure t
              | none => mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
            Term.elabTerm (← `($laSyn.$field:ident)) (some t)
      else if stx.isIdent then do
        let id := stx.getId
        if id == `true then pure (mkConst ``True)
        else if id == `false then pure (mkConst ``False)
        else if bound.contains id then
          Term.elabIdent stx none
        else
          let e ← Term.elabIdent stx none
          let t ← whnf (← inferType e)
          match t with
          | .forallE _ d _ _ =>
              let dW ← whnf d
              if dW.isSort then pure e
              else if ¬ d.hasMVar then
                -- NB: guard the `isDefEq` behind a plain `if`. Writing
                -- `(¬ d.hasMVar) && (← isDefEq d (inferType s))` would run the
                -- monadic bind unconditionally, assigning polymorphic implicit
                -- metavariables (e.g. `id ?α`, `some ?α`) to the state type.
                if (← isDefEq d (← inferType s)) then pure (mkApp e s) else pure e
              else pure e
          | _ => pure e
      else if stx.isOfKind ``Lean.Parser.Term.app then do
        let args := (stx.getArg 1).getArgs
        let eas ← args.mapM fun a => elabStateLiftCore bound s none a
        let ef ← elabStateLiftCore bound s expected? stx[0]
        mkOpAppExpr ef eas
      else do
        let t ← match expected? with
          | some t => pure t
          | none => mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
        Term.elabTerm stx (some t)

/-- Entry point: elaborate with no expected type. -/
partial def elabStateLift (bound : NameSet) (s : Expr) (stx : Syntax) : TermElabM Expr :=
  elabStateLiftCore bound s none stx

/--
If `e` is an action formula (`σ → σ → Prop`), apply it to the two state
variables; otherwise return it unchanged. Used by `elabActionLiftCore` so
named actions (`[a| RmPrepare i ∨ ...]`) compose inside brackets. Functions
whose first two domains are sorts (polymorphic functions like
`Function.update`) are left alone.
-/
private def applyIfAction (st0 st1 : Expr) (e : Expr) : TermElabM Expr := do
  let t ← whnf (← inferType e)
  match t with
  | .forallE _ d (.forallE _ d2 (.sort _) _) _ =>
      let dW ← whnf d
      let d2W ← whnf d2
      if dW.isSort || d2W.isSort then pure e
      else if d.hasMVar || d2.hasMVar then pure e
      else do
        let h1 ← isDefEq d (← inferType st0)
        let h2 ← isDefEq d2 (← inferType st1)
        if h1 && h2 then pure (mkApp (mkApp e st0) st1) else pure e
  | _ => pure e

/-- Elaborate an `[a| ...]` body with pre/post state variables `st0 st1` in
scope: unprimed state functions apply to `st0`, primed ones to `st1`. -/
partial def elabActionLiftCore (bound : NameSet) (st0 st1 : Expr) (expected? : Option Expr)
    (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(($e)) => elabActionLiftCore bound st0 st1 expected? e
  | `(($e : $T)) => do
      let t ← Term.elabType T
      elabActionLiftCore bound st0 st1 (some t) e
  | `(∃ $x:ident : $T, $b) => do
      let t ← Term.elabType T
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? b
        let lam ← mkLambdaFVars #[xv] lb
        mkOpApp ``Exists #[lam]
  | `(∃ $x:ident ∈ $S, $b) => do
      let lS ← elabStateLiftCore bound st0 none S
      let elemType ← elabElemType lS
      withLocalDecl x.getId .default elemType fun xv => do
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? b
        let mem ← mkOpApp ``Membership.mem #[lS, xv]
        let conj ← mkOpApp ``And #[mem, lb]
        let lam ← mkLambdaFVars #[xv] conj
        mkOpApp ``Exists #[lam]
  | `(∃ $x:ident, $b) => do
      let t ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? b
        let lam ← mkLambdaFVars #[xv] lb
        mkOpApp ``Exists #[lam]
  | `(∀ $x:ident : $T, $b) => do
      let t ← Term.elabType T
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? b
        mkForallFVars #[xv] lb
  | `(∀ $x:ident ∈ $S, $b) => do
      let lS ← elabStateLiftCore bound st0 none S
      let elemType ← elabElemType lS
      withLocalDecl x.getId .default elemType fun xv => do
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? b
        let mem ← mkOpApp ``Membership.mem #[lS, xv]
        let imp ← withLocalDecl `_h .default mem fun h => mkForallFVars #[h] lb
        mkForallFVars #[xv] imp
  | `(∀ $x:ident, $b) => do
      let t ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
      withLocalDecl x.getId .default t fun xv => do
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? b
        mkForallFVars #[xv] lb
  | `(fun $x:ident $ys:ident* : $T => $b) => do
      let t ← Term.elabType T
      withLocalDecl x.getId .default t fun xv => do
        let rest ← if ys.isEmpty then pure b else `(fun $ys:ident* : $T => $b)
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? rest
        mkLambdaFVars #[xv] lb
  | `(fun $x:ident $ys:ident* => $b) => do
      let t ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
      withLocalDecl x.getId .default t fun xv => do
        let rest ← if ys.isEmpty then pure b else `(fun $ys:ident* => $b)
        let lb ← elabActionLiftCore (bound.insert x.getId) st0 st1 expected? rest
        mkLambdaFVars #[xv] lb
  | `(if $c then $a else $b) => do
      let lc ← elabStateLiftCore bound st0 (some propType) c
      let la ← elabActionLiftCore bound st0 st1 expected? a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``ite #[lc, la, lb]
  | `($a % $b) => do
      let la ← elabActionLiftCore bound st0 st1 expected? a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HMod.hMod #[la, lb]
  | `($a + $b) => do
      let la ← elabActionLiftCore bound st0 st1 expected? a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HAdd.hAdd #[la, lb]
  | `($a - $b) => do
      let la ← elabActionLiftCore bound st0 st1 expected? a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HSub.hSub #[la, lb]
  | `($a * $b) => do
      let la ← elabActionLiftCore bound st0 st1 expected? a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``HMul.hMul #[la, lb]
  | `($a = $b) => do
      let la ← elabActionLiftCore bound st0 st1 none a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``Eq #[la, lb]
  | `($a < $b) => do
      let la ← elabActionLiftCore bound st0 st1 none a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``LT.lt #[la, lb]
  | `($a ≤ $b) => do
      let la ← elabActionLiftCore bound st0 st1 none a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``LE.le #[la, lb]
  | `($a > $b) => do
      let la ← elabActionLiftCore bound st0 st1 none a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``GT.gt #[la, lb]
  | `($a ≥ $b) => do
      let la ← elabActionLiftCore bound st0 st1 none a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``GE.ge #[la, lb]
  | `($a ≠ $b) => do
      let la ← elabActionLiftCore bound st0 st1 none a
      let lb ← elabActionLiftCore bound st0 st1 (some (← inferType la)) b
      let _ ← isDefEq (← inferType la) (← inferType lb)
      mkOpApp ``Ne #[la, lb]
  | `($a ∧ $b) => do
      let la ← elabActionLiftCore bound st0 st1 (some propType) a
      let lb ← elabActionLiftCore bound st0 st1 (some propType) b
      mkOpApp ``And #[la, lb]
  | `($a ∨ $b) => do
      let la ← elabActionLiftCore bound st0 st1 (some propType) a
      let lb ← elabActionLiftCore bound st0 st1 (some propType) b
      mkOpApp ``Or #[la, lb]
  | `($a → $b) => do
      let la ← elabActionLiftCore bound st0 st1 (some propType) a
      let lb ← elabActionLiftCore bound st0 st1 (some propType) b
      withLocalDecl `_h .default la fun h => mkForallFVars #[h] lb
  | `($a ⇒ $b) => do
      let la ← elabActionLiftCore bound st0 st1 (some propType) a
      let lb ← elabActionLiftCore bound st0 st1 (some propType) b
      withLocalDecl `_h .default la fun h => mkForallFVars #[h] lb
  | `(¬ $a) => do
      let la ← elabActionLiftCore bound st0 st1 (some propType) a
      mkOpApp ``Not #[la]
  | stx =>
      if stx.isOfKind ``«term__[_]» then do
        let la ← elabActionLiftCore bound st0 st1 expected? stx[0]
        let li ← elabActionLiftCore bound st0 st1 none stx[2]
        let ty ← whnf (← inferType la)
        if ty.isForall then do
          let liTy ← inferType li
          match ty with
          | .forallE _ d _ _ =>
              unless (← isDefEq liTy d) do
                throwError "[p|]/[a| ...]: index type mismatch: {li} : {liTy} but the collection expects {d}"
          | _ => pure ()
          pure (mkApp la li)
        else do
          let laSyn ← Term.exprToSyntax la
          let liSyn ← Term.exprToSyntax li
          let t ← match expected? with
            | some t => pure t
            | none => mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
          Term.elabTerm (← `($laSyn[$liSyn])) (some t)
      else if stx.isOfKind ``Lean.Parser.Term.proj then do
        let la ← elabActionLiftCore bound st0 st1 expected? stx[0]
        let ty ← whnf (← inferType la)
        match ty with
        | .const s _ =>
            let proj ← mkConstWithFreshMVarLevels (s ++ stx[2].getId)
            pure (mkApp proj la)
        | _ =>
            let laSyn ← Term.exprToSyntax la
            let field := mkIdent (stx[2].getId)
            let t ← match expected? with
              | some t => pure t
              | none => mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
            Term.elabTerm (← `($laSyn.$field:ident)) (some t)
      else if stx.isIdent then do
        let n := stx.getId.toString
        if n == "true" then pure (mkConst ``True)
        else if n == "false" then pure (mkConst ``False)
        else if n.endsWith "'" then
          let base : Syntax := mkIdent (n.dropEnd 1).toName
          let e ← Term.elabIdent base none
          let t ← whnf (← inferType e)
          match t with
          | .forallE _ d _ _ =>
              if (← isDefEq d (← inferType st0)) then pure (mkApp e st1)
              else throwError s!"[a| ...]: primed identifier '{base}' is not a state function"
          | _ => throwError s!"[a| ...]: primed identifier '{base}' is not a state function"
        else if bound.contains stx.getId then
          Term.elabIdent stx none
        else
          let e ← Term.elabIdent stx none
          let e ← applyIfAction st0 st1 e
          let t ← whnf (← inferType e)
          match t with
          | .forallE _ d _ _ =>
              let dW ← whnf d
              if dW.isSort then pure e
              else if ¬ d.hasMVar then
                -- see the state elaborator: never run `isDefEq` inside a `&&`
                -- with a `←` bind — the bind executes unconditionally.
                if (← isDefEq d (← inferType st0)) then pure (mkApp e st0) else pure e
              else pure e
          | _ => pure e
      else if stx.isOfKind ``Lean.Parser.Term.app then do
        let args := (stx.getArg 1).getArgs
        let eas ← args.mapM fun a => elabActionLiftCore bound st0 st1 none a
        let ef ← elabActionLiftCore bound st0 st1 expected? stx[0]
        applyIfAction st0 st1 (← mkOpAppExpr ef eas)
      else do
        let t ← match expected? with
          | some t => pure t
          | none => mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
        Term.elabTerm stx (some t)

/-- Entry point: elaborate with no expected type. -/
partial def elabActionLift (bound : NameSet) (st0 st1 : Expr) (stx : Syntax) : TermElabM Expr :=
  elabActionLiftCore bound st0 st1 none stx

/-! ## The formula-level lift -/

/-- Rewrite propositional connectives in `[t| ...]` bodies to the lifted ones,
leaving everything else (lifts, temporal notations, named formulas) alone. -/
partial def liftFormula (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  match stx with
  | `(($e)) => liftFormula e
  | `(∃ $x:ident, $b) => do
      let lb ← liftFormula b
      `(tlaExists (fun $x:ident => $lb))
  | `(∀ $x:ident, $b) => do
      let lb ← liftFormula b
      `(tlaForall (fun $x:ident => $lb))
  | `($a ∧ $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaAnd $la $lb)
  | `($a ∨ $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaOr $la $lb)
  | `($a → $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaImp $la $lb)
  | `(¬ $a) => do
      let la ← liftFormula a
      `(tlaNot $la)
  | `($a ↔ $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaIff $la $lb)
  | `(⌜$p⌝) => `(statePred $p)
  | `(⌞$p⌟) => `(purePred $p)
  | `(□[$a]_$v) => `(stutAlways $a $v)
  | _ => pure stx

syntax "[p| " term "]" : term
elab "[p| " body:term "]" : term <= expectedType => do
  let σ ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
  let t ← whnf expectedType
  match t with
  | .forallE _ d _ _ => let _ ← isDefEq σ d
  | _ => pure ()
  withLocalDecl `_s .default σ fun s => do
    let eb ← elabStateLift NameSet.empty s body
    mkLambdaFVars #[s] eb

syntax "[a| " term "]" : term
elab "[a| " body:term "]" : term <= expectedType => do
  let σ ← mkFreshExprMVar (some (mkSort (Level.succ Level.zero)))
  let t ← whnf expectedType
  match t with
  | .forallE _ d _ _ => let _ ← isDefEq σ d
  | _ => pure ()
  withLocalDecl `_st0 .default σ fun st0 => do
    withLocalDecl `_st1 .default σ fun st1 => do
      let eb ← elabActionLift NameSet.empty st0 st1 body
      mkLambdaFVars #[st0, st1] eb

syntax "[t| " term "]" : term
macro_rules
  | `([t| $body]) => do
      let t ← liftFormula body
      pure t.raw

/-- `[c| Byz, p | body]`: the action `body` guarded by the honest-processor
condition `p ∉ Byz` — sugar for `CorrectAct Byz p [a| body]`, the standard
guard every correct-processor action in a Byzantine spec repeats. -/
syntax "[c| " term ", " term " | " term "]" : term
macro_rules
  | `([c| $Byz, $p | $body]) => `(CorrectAct $Byz $p [a| $body])

end Tla
