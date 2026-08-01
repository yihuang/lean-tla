import Leslie.Examples.CacheCoherence.TileLink.Messages.InitProof

/-! ## Liveness Definitions for TileLink Message Model

    This file defines the protocol phase predicates and fairness-augmented
    specification needed for liveness proofs.

    The first liveness target: under weak fairness of all receive actions,
    an acquire request eventually completes with a grant.
-/

namespace TileLink.Messages.Liveness

open TLA TileLink SymShared

/-! ### Per-action fairness predicates

    Each receive action, parameterized by process index, defines a specific
    action on the state space. We make these into individual actions for
    the fairness list. -/

/-- Action: recvAcquireAtManager for process i fires. -/
def actRecvAcquireAtManager (n : Nat) (i : Fin n) : action (SymState HomeState NodeState n) :=
  fun s s' => ∃ a : Act, a = .recvAcquireAtManager ∧ tlMessages.step n i a s s'

/-- Action: recvProbeAtMaster for process i fires. -/
def actRecvProbeAtMaster (n : Nat) (i : Fin n) : action (SymState HomeState NodeState n) :=
  fun s s' => ∃ a : Act, a = .recvProbeAtMaster ∧ tlMessages.step n i a s s'

/-- Action: recvProbeAckAtManager for process i fires. -/
def actRecvProbeAckAtManager (n : Nat) (i : Fin n) : action (SymState HomeState NodeState n) :=
  fun s s' => ∃ a : Act, a = .recvProbeAckAtManager ∧ tlMessages.step n i a s s'

/-- Action: sendGrantToRequester for process i fires. -/
def actSendGrantToRequester (n : Nat) (i : Fin n) : action (SymState HomeState NodeState n) :=
  fun s s' => ∃ a : Act, a = .sendGrantToRequester ∧ tlMessages.step n i a s s'

/-- Action: recvGrantAtMaster for process i fires. -/
def actRecvGrantAtMaster (n : Nat) (i : Fin n) : action (SymState HomeState NodeState n) :=
  fun s s' => ∃ a : Act, a = .recvGrantAtMaster ∧ tlMessages.step n i a s s'

/-- Action: recvGrantAckAtManager for process i fires. -/
def actRecvGrantAckAtManager (n : Nat) (i : Fin n) : action (SymState HomeState NodeState n) :=
  fun s s' => ∃ a : Act, a = .recvGrantAckAtManager ∧ tlMessages.step n i a s s'

/-! ### Protocol phase predicates -/

/-- An acquire request is pending at node i: either the A-channel message
    hasn't been consumed yet, or a transaction is active for this requester. -/
def acquirePending (n : Nat) (i : Fin n) (s : SymState HomeState NodeState n) : Prop :=
  (s.locals i).chanA ≠ none ∨
  (∃ tx, s.shared.currentTxn = some tx ∧ tx.requester = i.1)

/-- The acquire has completed: the transaction is retired and node i has
    received its grant (chanD had the grant, now consumed). -/
def acquireComplete (n : Nat) (i : Fin n) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn = none ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanD = none

/-- The transaction is in probing phase with some probes remaining. -/
def probingWithRemaining (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∃ tx, s.shared.currentTxn = some tx ∧ tx.phase = .probing ∧
    ∃ j : Fin n, tx.probesRemaining j.1 = true

/-- The transaction has reached grantReady (all probes completed). -/
def grantReady (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∃ tx, s.shared.currentTxn = some tx ∧ tx.phase = .grantReady

/-- A grant has been sent and is pending acknowledgment. -/
def grantPendingAck (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∃ tx, s.shared.currentTxn = some tx ∧ tx.phase = .grantPendingAck

/-! ### Fairness-augmented specification

    The base `tlMessages.toSpec` has `fair := []`. We create a variant
    that includes weak fairness for all receive/send actions. -/

/-- Collect all fair actions for the TileLink protocol with n processes.
    Every receive and send action at every process index is weakly fair. -/
noncomputable def fairActions (n : Nat) : List (action (SymState HomeState NodeState n)) :=
  (List.finRange n).flatMap fun i =>
    [ actRecvAcquireAtManager n i
    , actRecvProbeAtMaster n i
    , actRecvProbeAckAtManager n i
    , actSendGrantToRequester n i
    , actRecvGrantAtMaster n i
    , actRecvGrantAckAtManager n i ]

/-- The TileLink message spec augmented with weak fairness on all
    protocol-relevant actions. -/
noncomputable def tlMessagesFair (n : Nat) : Spec (SymState HomeState NodeState n) where
  init := (tlMessages.toSpec n).init
  next := (tlMessages.toSpec n).next
  fair := fairActions n

end TileLink.Messages.Liveness
