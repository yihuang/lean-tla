import Leslie.Action

/-! ## Random Simulator for ActionSpec Models

    Provides a random-walk simulator for testing protocol invariants
    before formal verification.

    ### Usage

    1. Define a `Simulable` instance mirroring your `ActionSpec`
    2. Call `TLA.Sim.simulate` with an invariant to check
    3. Examine the counterexample trace if a violation is found

    ### Example

    ```lean
    instance : TLA.Sim.Simulable MyState MyAction where
      init := pure { ... }
      actions := [.action1, .action2, ...]
      enabled := fun act s => ...   -- executable gate check
      step := fun act s => pure ... -- executable transition

    #eval TLA.Sim.simulate (ι := MyAction) myInvariant
    ```
-/

namespace TLA.Sim

/-- Executable mirror of an `ActionSpec` for simulation.
    Each field corresponds to a component of the `ActionSpec`:
    - `init` ↔ `ActionSpec.init` (but returns a concrete state)
    - `actions` ↔ enumeration of all action indices `ι`
    - `enabled` ↔ `GatedAction.gate` (but returns `Bool`)
    - `step` ↔ `GatedAction.transition` (but returns a concrete successor) -/
class Simulable (σ : Type) (ι : Type) where
  /-- Generate an initial state satisfying the spec's init predicate -/
  init : IO σ
  /-- All action indices to consider -/
  actions : List ι
  /-- Check if an action's gate is satisfied (executable version of the gate) -/
  enabled : ι → σ → Bool
  /-- Execute an enabled action, returning the successor state.
      Uses `IO` to support random choices in nondeterministic transitions. -/
  step : ι → σ → IO σ

/-- Configuration for the simulator. -/
structure Config where
  /-- Maximum steps per trace -/
  maxSteps : Nat := 10000
  /-- Number of random traces to run -/
  numTraces : Nat := 100
  deriving Repr

/-- Outcome of a single trace. -/
inductive TraceOutcome (σ ι : Type) where
  /-- Trace completed without invariant violation -/
  | completed (steps : Nat)
  /-- Invariant violation found; includes the full trace -/
  | violation (trace : Array (Option ι × σ))
  /-- No enabled actions (deadlock); includes the trace up to deadlock -/
  | deadlock (steps : Nat) (trace : Array (Option ι × σ))

private def pickRandom {α : Type} (l : List α) (h : l.length > 0) : IO α := do
  let idx ← IO.rand 0 (l.length - 1)
  have : idx % l.length < l.length := Nat.mod_lt _ h
  pure l[idx % l.length]

/-- Run one random trace, checking the invariant at each step.
    Returns the trace outcome (completed / violation / deadlock). -/
def runTrace [Simulable σ ι] (cfg : Config) (inv : σ → Bool) :
    IO (TraceOutcome σ ι) := do
  let mut state ← Simulable.init (ι := ι)
  if !inv state then
    return .violation #[(none, state)]
  let mut trace : Array (Option ι × σ) := #[(none, state)]
  for _ in [:cfg.maxSteps] do
    let en := Simulable.actions (σ := σ) |>.filter (Simulable.enabled · state)
    match h : en.length with
    | 0 => return .deadlock trace.size trace
    | _ + 1 =>
      let act ← pickRandom en (by omega)
      state ← Simulable.step act state
      trace := trace.push (some act, state)
      if !inv state then
        return .violation trace
  return .completed trace.size

/-- Run multiple random traces checking an invariant.
    Prints results and returns `true` if no violation was found. -/
def simulate [Simulable σ ι] [Repr σ] [Repr ι]
    (inv : σ → Bool) (cfg : Config := {}) : IO Bool := do
  let mut deadlocks := 0
  let mut totalSteps := 0
  for i in [:cfg.numTraces] do
    match ← runTrace (σ := σ) (ι := ι) cfg inv with
    | .completed n =>
      totalSteps := totalSteps + n
    | .deadlock n _ =>
      totalSteps := totalSteps + n
      deadlocks := deadlocks + 1
    | .violation trace =>
      IO.println s!"VIOLATION in trace {i + 1} at step {trace.size - 1}!"
      IO.println "Counterexample:"
      for entry in trace do
        let (act, st) := entry
        let actStr := match act with
          | none => "init"
          | some a => reprStr (α := ι) a
        IO.println s!"  {actStr}"
        IO.println s!"    → {reprStr (α := σ) st}"
      return false
  let avg := if cfg.numTraces > 0 then totalSteps / cfg.numTraces else 0
  IO.println s!"OK: {cfg.numTraces} traces × ≤{cfg.maxSteps} steps, {deadlocks} deadlocks, avg length {avg}"
  return true

/-- Generate and print a single random trace (for protocol exploration). -/
def randomWalk [Simulable σ ι] [Repr σ] [Repr ι]
    (steps : Nat := 20) : IO Unit := do
  let mut state ← Simulable.init (ι := ι)
  IO.println s!"[init] {reprStr (α := σ) state}"
  for i in [:steps] do
    let en := Simulable.actions (σ := σ) |>.filter (Simulable.enabled · state)
    match h : en.length with
    | 0 =>
      IO.println s!"DEADLOCK at step {i}"
      return
    | _ + 1 =>
      let act ← pickRandom en (by omega)
      state ← Simulable.step act state
      IO.println s!"[{reprStr (α := ι) act}] {reprStr (α := σ) state}"

/-- Run traces and report only a summary (no counterexample details).
    Useful for quick regression checks. -/
def quickCheck [Simulable σ ι]
    (inv : σ → Bool) (numTraces : Nat := 1000) (maxSteps : Nat := 1000) : IO Bool := do
  let cfg : Config := { numTraces, maxSteps }
  for _ in [:cfg.numTraces] do
    match ← runTrace (σ := σ) (ι := ι) cfg inv with
    | .completed _ => pure ()
    | .deadlock _ _ => pure ()
    | .violation _ => return false
  return true

end TLA.Sim
