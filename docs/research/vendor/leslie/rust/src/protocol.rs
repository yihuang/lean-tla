use crate::comm::{Inbox, Round};

/// Pure round-based protocol logic.
///
/// Both `send` and `update` are **pure functions** of the current state
/// and round — they take `&self` and return new values without side
/// effects. The driver (`run_step`) is responsible for threading the
/// state through successive calls.
///
/// This purity is intentional: it matches Leslie's `Phase` definition
/// where `send : P → S → M` and `update : P → S → (P → Option M) → S`
/// are plain functions, and it makes the Lean correspondence proof
/// straightforward — the Rust functions can be compared to their Leslie
/// counterparts without reasoning about mutation.
///
/// ## The `Oracle` parameter
///
/// The `Oracle` associated type models **external nondeterminism** that
/// the protocol cannot control: coin flips (Ben-Or), leader election
/// randomness, timeout decisions, etc. The caller chooses the oracle
/// value; the protocol logic is deterministic given (state, round,
/// inbox, oracle).
///
/// ### Why an explicit parameter rather than `rand::Rng`?
///
/// 1. **Verification**: Leslie models nondeterminism by quantifying
///    over all oracle values. An explicit, enumerable `Oracle` type
///    lets the Lean correspondence proof do the same: `∀ oracle, ...`.
///    A hidden `Rng` would be opaque to the proof.
///
/// 2. **Exhaustive testing**: Tools like TraceForge enumerate all
///    oracle values to explore the full nondeterministic state space.
///    `Oracle = bool` gives 2 branches per step; `Oracle = ()` means
///    the step is deterministic. An `Rng` cannot be enumerated.
///
/// 3. **Reproducibility**: Given the same (state, round, inbox, oracle)
///    tuple, `update` always returns the same result. Tests and replay
///    tools can reproduce any execution by recording oracle choices.
///
/// ### When `Oracle = ()`
///
/// Most protocols are deterministic: `send` and `update` are fully
/// determined by state and inbox. These protocols use `Oracle = ()`
/// and the oracle parameter is ignored. The `run_step` caller passes
/// `()` and the type system ensures no nondeterminism leaks in.
///
/// ### Alternatives considered
///
/// - **`rand::Rng` parameter**: More ergonomic for randomized protocols
///   but opaque to verification and testing tools. Could be offered as
///   a convenience wrapper that samples an `Oracle` value from an `Rng`.
///
/// - **Trait method `fn oracle_values() -> Vec<Self::Oracle>`**: Useful
///   for model checkers that enumerate all choices. Not included in the
///   core trait because it conflates the protocol definition with the
///   exploration strategy, and because `Oracle` may be infinite (e.g.,
///   a proposed value drawn from an unbounded domain).
pub trait Protocol<P, R>
where
    P: Clone + Ord + Eq,
    R: Round,
{
    type Msg: Clone;
    type Oracle: Clone;

    /// Compute the message to broadcast for the given round.
    ///
    /// Pure: depends only on `self` (the current state) and `round`.
    fn send(&self, round: &R) -> Self::Msg;

    /// Compute the next state given the current round, received inbox,
    /// and oracle value.
    ///
    /// Pure: takes `&self` and returns a new `Self`. The caller (driver)
    /// is responsible for replacing the old state with the returned value.
    fn update(&self, round: &R, inbox: &Inbox<P, Self::Msg>, oracle: Self::Oracle) -> Self;
}
