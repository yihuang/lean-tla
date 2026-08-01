import Leslie.Simulate
import Leslie.Examples.TwoPhaseCommit

/-! ## Two-Phase Commit: Random Simulation

    Demonstrates using the simulator to test the 2PC protocol invariant
    before (or alongside) formal verification.

    We check two properties:
    1. **Consistency**: no RM is committed while another is aborted
    2. **Protocol invariant**: the relationship between messages and TM state
-/

open TLA TwoPhaseCommit

deriving instance Repr for TPCState
deriving instance Repr for TPCAction

/-- Executable mirror of the `tpc` ActionSpec. -/
instance : TLA.Sim.Simulable TPCState TPCAction where
  init := pure {
    rm1 := .working, rm2 := .working, tmState := .init,
    tm1Prepared := false, tm2Prepared := false,
    msgCommit := false, msgAbort := false
  }
  actions := [
    .rm1_prepare, .rm2_prepare,
    .tm_recv_prepared_1, .tm_recv_prepared_2,
    .tm_commit, .tm_abort,
    .rm1_recv_commit, .rm2_recv_commit,
    .rm1_recv_abort, .rm2_recv_abort
  ]
  enabled := fun act s => match act with
    | .rm1_prepare      => s.rm1 == .working
    | .rm2_prepare      => s.rm2 == .working
    | .tm_recv_prepared_1 => s.tmState == .init && s.rm1 == .prepared
    | .tm_recv_prepared_2 => s.tmState == .init && s.rm2 == .prepared
    | .tm_commit        => s.tmState == .init && s.tm1Prepared && s.tm2Prepared
    | .tm_abort         => s.tmState == .init
    | .rm1_recv_commit  => s.msgCommit
    | .rm2_recv_commit  => s.msgCommit
    | .rm1_recv_abort   => s.msgAbort
    | .rm2_recv_abort   => s.msgAbort
  step := fun act s => pure (match act with
    | .rm1_prepare      => { s with rm1 := .prepared }
    | .rm2_prepare      => { s with rm2 := .prepared }
    | .tm_recv_prepared_1 => { s with tm1Prepared := true }
    | .tm_recv_prepared_2 => { s with tm2Prepared := true }
    | .tm_commit        => { s with tmState := .committed, msgCommit := true }
    | .tm_abort         => { s with tmState := .aborted, msgAbort := true }
    | .rm1_recv_commit  => { s with rm1 := .committed }
    | .rm2_recv_commit  => { s with rm2 := .committed }
    | .rm1_recv_abort   => { s with rm1 := .aborted }
    | .rm2_recv_abort   => { s with rm2 := .aborted })

/-! ### Invariants to check -/

/-- Consistency: no RM committed while the other is aborted. -/
def tpcConsistent (s : TPCState) : Bool :=
  !(s.rm1 == .committed && s.rm2 == .aborted) &&
  !(s.rm1 == .aborted && s.rm2 == .committed)

/-- Protocol invariant (executable version of `tpc_inv`). -/
def tpcInv (s : TPCState) : Bool :=
  (if s.rm1 == .committed then s.msgCommit else true) &&
  (if s.rm2 == .committed then s.msgCommit else true) &&
  (if s.rm1 == .aborted then s.msgAbort else true) &&
  (if s.rm2 == .aborted then s.msgAbort else true) &&
  (if s.msgCommit then s.tmState == .committed else true) &&
  (if s.msgAbort then s.tmState == .aborted else true)

/-! ### Run the simulator -/

#eval do
  IO.println "=== 2PC Consistency Check ==="
  let _ ← TLA.Sim.simulate (ι := TPCAction) tpcConsistent
    { numTraces := 1000, maxSteps := 100 }
  IO.println ""
  IO.println "=== 2PC Protocol Invariant Check ==="
  let _ ← TLA.Sim.simulate (ι := TPCAction) tpcInv
    { numTraces := 1000, maxSteps := 100 }
  IO.println ""
  IO.println "=== Sample Trace ==="
  TLA.Sim.randomWalk (σ := TPCState) (ι := TPCAction) (steps := 15)
