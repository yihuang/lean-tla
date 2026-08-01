import Lean
import Leslie.Gadgets.SetFn
import Leslie.Utils.MetaUtil

/-! ## Auto-generation of frame/simp lemmas for protocol state transformers.

    `#gen_frame_lemmas defName` generates `@[simp]` lemmas for every field
    of the return structure of `defName`.
-/

open Lean Meta Elab Command Term

namespace Leslie.FrameLemmaGen

/-- Get the field index for a named field in a structure. -/
def getFieldIdx (env : Environment) (structName fieldName : Name) : Option Nat := do
  let fields := getStructureFields env structName
  fields.findIdx? (· == fieldName)

/-- Build a projection expression as a function application: `StructName.fieldName s`
    This produces the same form as user-written `s.fieldName` after elaboration,
    which is important for `rw` compatibility. -/
def mkFieldProj (structName fieldName : Name) (struct : Expr) (_env : Environment) : MetaM Expr :=
  mkAppM (structName ++ fieldName) #[struct]

/-- Check if an expression is a `setFn` application. Returns (fn, idx, val) if so. -/
def matchSetFn? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``setFn 5 then
    some (e.getArg! 2, e.getArg! 3, e.getArg! 4)
  else
    none

/-- Determine a suffix for the setFn index expression. -/
def indexSuffix (env : Environment) (stateParam : Expr) (structName : Name)
    (indexParams : Array Expr) (idxExpr : Expr) : MetaM String := do
  for p in indexParams do
    if ← isDefEq idxExpr p then return "self"
  let fields := getStructureFields env structName
  for f in fields do
    let proj ← mkFieldProj structName f stateParam env
    if ← isDefEq idxExpr proj then return f.toString
  return "idx"

/-- Generate frame lemmas for a single state transformer. -/
def generateFrameLemmas (defName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? defName | throwError "unknown constant {defName}"
  let some defVal := ci.value? | throwError "{defName} is not a definition"

  liftTermElabM do
    lambdaTelescope defVal fun valParams body => do

    -- Determine return type from body
    let retType ← inferType body

    -- Find the return structure name
    let some structName := retType.getAppFn.constName?
      | throwError "return type of {defName} is not a named type"

    let fields := getStructureFields env structName

    -- Find the state parameter (first param matching return type)
    let mut stateParam : Expr := default
    let mut stateFound := false
    for p in valParams do
      let paramType ← inferType p
      if ← isDefEq paramType retType then
        stateParam := p; stateFound := true; break
    unless stateFound do throwError "could not find state parameter in {defName}"

    -- Collect Fin n params
    let mut indexParams : Array Expr := #[]
    for p in valParams do
      if ← isDefEq p stateParam then continue
      let paramType ← inferType p
      if paramType.isAppOf ``Fin then indexParams := indexParams.push p

    -- Reduce body to constructor form
    let body' ← whnf body
    let ctorArgs := body'.getAppArgs
    let numTypeParams := ctorArgs.size - fields.size
    let fieldArgs := ctorArgs[numTypeParams:]

    if fieldArgs.size != fields.size then
      logWarning s!"field count mismatch in {defName}: {fieldArgs.size} args vs {fields.size} fields"
      return

    -- Build the application expression: defName param1 param2 ...
    let defConst := Lean.mkConst defName (ci.levelParams.map Level.param)
    let appExpr := mkAppN defConst valParams

    -- Helper: construct theorem name like `DirectoryMSI.recvGetS_UncachedState_cache`
    -- by appending suffix to the last component of defName
    let mkThmName (suffix : String) : Name :=
      let lastComponent := defName.getString!
      defName.getPrefix ++ Name.mkSimple s!"{lastComponent}_{suffix}"

    -- Generate lemmas for each field
    for i in [:fields.size] do
      let fieldName := fields[i]!
      let arg := fieldArgs[i]!

      -- Get projection of original state
      let origProj ← mkFieldProj structName fieldName stateParam env
      -- Get projection of new state
      let newProj ← mkFieldProj structName fieldName appExpr env

      -- Classify the field
      let isUnmodified ← isDefEq arg origProj

      if isUnmodified then
        -- Unmodified field: (defName s i).field = s.field := rfl
        let thmName := mkThmName fieldName.toString
        let eq ← mkEq newProj origProj
        let type ← mkForallFVars valParams eq
        let type ← instantiateMVars type
        try
          -- Try rfl proof
          let rflProof := mkApp2 (mkConst ``Eq.refl [← getLevel (← inferType newProj)]) (← inferType newProj) newProj
          let proof ← mkLambdaFVars valParams rflProof
          let proof ← instantiateMVars proof
          LeslieLib.simpleAddTheorem thmName ci.levelParams type proof false
        catch _ =>
          -- Fallback: try simp proof
          let proofSyntax ← `(term| by unfold $(mkIdent defName); simp)
          LeslieLib.simpleProveTheorem thmName ci.levelParams type proofSyntax false
        -- Add @[simp]
        liftCommandElabM do
          let cmd ← `(command| attribute [simp] $(mkIdent thmName))
          elabCommand cmd
      else
        -- Check for setFn
        match matchSetFn? arg with
        | some (_fnArg, idxExpr, newVal) =>
          let suffix ← indexSuffix env stateParam structName indexParams idxExpr

          -- Self lemma: (defName s i).field idx = newVal
          let selfName := mkThmName s!"{fieldName}_{suffix}"
          let lhsSelf := mkApp newProj idxExpr
          let eqSelf ← mkEq lhsSelf newVal
          let typeSelf ← mkForallFVars valParams eqSelf
          let typeSelf ← instantiateMVars typeSelf
          let proofSelf ← `(term| by unfold $(mkIdent defName); simp [setFn])
          try
            LeslieLib.simpleProveTheorem selfName ci.levelParams typeSelf proofSelf false
            liftCommandElabM do
              let cmd ← `(command| attribute [simp] $(mkIdent selfName))
              elabCommand cmd
          catch e =>
            logWarning s!"failed to generate {selfName}: {← e.toMessageData.toString}"

          -- Ne lemma: (defName s i).field j = s.field j, with h : j ≠ idx
          let neName := mkThmName s!"{fieldName}_ne"
          let idxType ← inferType idxExpr
          withLocalDecl `j .default idxType fun j => do
          let neType ← mkAppM ``Ne #[j, idxExpr]
          withLocalDecl `h .default neType fun h => do
          let lhsNe := mkApp newProj j
          let rhsNe := mkApp origProj j
          let eqNe ← mkEq lhsNe rhsNe
          let allParams := valParams ++ #[j, h]
          let typeNe ← mkForallFVars allParams eqNe
          let typeNe ← instantiateMVars typeNe
          let proofNe ← `(term| by unfold $(mkIdent defName); simp_all [setFn])
          try
            LeslieLib.simpleProveTheorem neName ci.levelParams typeNe proofNe false
            liftCommandElabM do
              let cmd ← `(command| attribute [simp] $(mkIdent neName))
              elabCommand cmd
          catch e =>
            logWarning s!"failed to generate {neName}: {← e.toMessageData.toString}"

        | none =>
          -- Scalar modified: (defName s i).field = newVal := rfl
          let thmName := mkThmName fieldName.toString
          let eq ← mkEq newProj arg
          let type ← mkForallFVars valParams eq
          let type ← instantiateMVars type
          try
            let rflProof := mkApp2 (mkConst ``Eq.refl [← getLevel (← inferType newProj)]) (← inferType newProj) newProj
            let proof ← mkLambdaFVars valParams rflProof
            let proof ← instantiateMVars proof
            LeslieLib.simpleAddTheorem thmName ci.levelParams type proof false
          catch _ =>
            let proofSyntax ← `(term| by unfold $(mkIdent defName); simp)
            LeslieLib.simpleProveTheorem thmName ci.levelParams type proofSyntax false
          liftCommandElabM do
            let cmd ← `(command| attribute [simp] $(mkIdent thmName))
            elabCommand cmd

/-- The `#gen_frame_lemmas` command. -/
elab "#gen_frame_lemmas " ids:ident+ : command => do
  for id in ids do
    let ns ← getCurrNamespace
    let nm := ns ++ id.getId
    let env ← getEnv
    let resolvedName := if env.find? nm |>.isSome then nm else id.getId
    generateFrameLemmas resolvedName

end Leslie.FrameLemmaGen
