//! Shared test harness for running bounded protocol instances.
//!
//! Two simulators matching the two protocol styles in Leslie:
//!
//! - **Round-based** (`run_rounds`): Models N processes communicating
//!   synchronously per round, with heard-of (HO) sets controlling which
//!   messages are delivered. Used for consensus protocols like OneThirdRule.
//!
//! - **Action-based** (`run_actions`): Models a nondeterministic state
//!   machine where one action fires at a time. Used for asynchronous
//!   protocols like LeaseLock.
//!
//! Both simulators are single-threaded and pure — no network, no threads,
//! just function calls. They check invariants after every step.

#![allow(dead_code)]
use std::collections::BTreeMap;
use std::hash::{DefaultHasher, Hash, Hasher};

// ── Round-based simulator ──────────────────────────────────────────

/// Simulate `n` processes running a round-based protocol.
///
/// Each round:
///   1. Every process produces a message via `send(id, &state)`.
///   2. Messages are delivered per the HO set: `ho(round, receiver, sender)`.
///   3. Every process updates via `update(id, &state, &inbox, oracle)`.
///   4. The `check` callback asserts invariants on the current states.
///
/// Returns the final states after `num_rounds` rounds.
///
/// # Example
///
/// ```ignore
/// // Run 3 processes for 10 rounds with reliable (all-to-all) delivery
/// let final_states = run_rounds(
///     3, 10,
///     |id| MyProtocol::new(id, 3),           // init
///     |id, s| s.send_msg(id),                 // send
///     |id, s, inbox, _| s.update_msg(inbox),  // update
///     ho_reliable,                             // HO: all messages delivered
///     |_, _| (),                               // oracle: deterministic
///     |round, states| { /* check invariants */ },
/// );
/// ```
pub fn run_rounds<S: Clone, M: Clone, O: Clone>(
    n: usize,
    num_rounds: usize,
    init: impl Fn(usize) -> S,
    send: impl Fn(usize, &S) -> M,
    update: impl Fn(usize, &S, &BTreeMap<usize, M>, O) -> S,
    ho: impl Fn(usize, usize, usize) -> bool,
    oracle: impl Fn(usize, usize) -> O,
    check: impl Fn(usize, &[S]),
) -> Vec<S> {
    let mut states: Vec<S> = (0..n).map(&init).collect();
    check(0, &states);

    for round in 0..num_rounds {
        // 1. All processes send
        let messages: Vec<M> = (0..n).map(|i| send(i, &states[i])).collect();

        // 2. Build per-process inboxes according to HO set
        let inboxes: Vec<BTreeMap<usize, M>> = (0..n)
            .map(|receiver| {
                let mut inbox = BTreeMap::new();
                for sender in 0..n {
                    if ho(round, receiver, sender) {
                        inbox.insert(sender, messages[sender].clone());
                    }
                }
                inbox
            })
            .collect();

        // 3. All processes update (pure: old states -> new states)
        let new_states: Vec<S> = (0..n)
            .map(|i| update(i, &states[i], &inboxes[i], oracle(round, i)))
            .collect();

        states = new_states;
        check(round + 1, &states);
    }

    states
}

// ── Common HO (heard-of) strategies ────────────────────────────────

/// Reliable communication: every process hears every other process.
pub fn ho_reliable(_round: usize, _recv: usize, _send: usize) -> bool {
    true
}

/// Self-only delivery: each process hears only itself.
pub fn ho_self_only(_round: usize, recv: usize, send: usize) -> bool {
    recv == send
}

/// Random delivery: each process always hears itself, and hears each
/// other process independently with probability ~50%.
///
/// Deterministic given the seed: the delivery decision for
/// `(round, receiver, sender)` is a pure function of those three values
/// plus the seed. This means re-running with the same seed reproduces
/// the exact same execution — important for debugging failing tests.
///
/// The randomness is a simple hash-based PRNG, not cryptographic.
pub fn ho_random(seed: u64) -> impl Fn(usize, usize, usize) -> bool {
    move |round: usize, recv: usize, send: usize| -> bool {
        // Always hear yourself (self-delivery)
        if recv == send {
            return true;
        }
        // Hash (seed, round, recv, send) to get a deterministic pseudo-random bit
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        round.hash(&mut hasher);
        recv.hash(&mut hasher);
        send.hash(&mut hasher);
        hasher.finish() % 2 == 0 // ~50% delivery probability
    }
}

/// Random delivery with a configurable delivery probability.
///
/// `prob_percent` is 0..=100. Each non-self message is delivered
/// with approximately that probability. Self-delivery is always guaranteed.
pub fn ho_random_prob(seed: u64, prob_percent: u64) -> impl Fn(usize, usize, usize) -> bool {
    move |round: usize, recv: usize, send: usize| -> bool {
        if recv == send {
            return true;
        }
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        round.hash(&mut hasher);
        recv.hash(&mut hasher);
        send.hash(&mut hasher);
        hasher.finish() % 100 < prob_percent
    }
}

/// Random delivery with a minimum quorum guarantee.
///
/// Each process hears itself plus at least `min_heard` other processes
/// (chosen pseudo-randomly). Additional processes are delivered with ~50%
/// probability.
///
/// Useful for protocols like OneThirdRule that require >2n/3 delivery:
/// set `min_heard` to `2*n/3 + 1` to guarantee the communication predicate.
pub fn ho_random_quorum(seed: u64, n: usize, min_heard: usize) -> impl Fn(usize, usize, usize) -> bool {
    // Precompute: for each (round, receiver), which senders are guaranteed.
    // We use a Cell to cache the per-round-receiver selection without
    // requiring &mut in the closure.
    let cache: std::sync::Mutex<BTreeMap<(usize, usize), Vec<bool>>> =
        std::sync::Mutex::new(BTreeMap::new());

    move |round: usize, recv: usize, send: usize| -> bool {
        if recv == send {
            return true;
        }

        let mut guard = cache.lock().unwrap();
        let key = (round, recv);
        let delivered = guard.entry(key).or_insert_with(|| {
            // Build delivery vector for this (round, receiver)
            let mut others: Vec<usize> = (0..n).filter(|&s| s != recv).collect();

            // Deterministic shuffle using seed + round + recv
            for i in (1..others.len()).rev() {
                let mut hasher = DefaultHasher::new();
                seed.hash(&mut hasher);
                round.hash(&mut hasher);
                recv.hash(&mut hasher);
                i.hash(&mut hasher);
                let j = (hasher.finish() as usize) % (i + 1);
                others.swap(i, j);
            }

            // First min_heard are guaranteed, rest are ~50%
            let mut deliver = vec![false; n];
            deliver[recv] = true; // self
            for (idx, &sender) in others.iter().enumerate() {
                if idx < min_heard {
                    deliver[sender] = true;
                } else {
                    let mut hasher = DefaultHasher::new();
                    seed.hash(&mut hasher);
                    round.hash(&mut hasher);
                    recv.hash(&mut hasher);
                    sender.hash(&mut hasher);
                    deliver[sender] = hasher.finish() % 2 == 0;
                }
            }
            deliver
        });

        delivered[send]
    }
}

// ── Action-based simulator ─────────────────────────────────────────

/// Simulate an action-based protocol for `num_steps` steps.
///
/// Each step:
///   1. The `pick` callback selects an action from the possible actions.
///   2. If `can_fire(&state, &action)` holds, apply `step` to get the
///      new state and call `check` to assert invariants.
///   3. If `can_fire` is false, the action is skipped (stuttering step).
///
/// Returns the final state.
///
/// # Example
///
/// ```ignore
/// let final_state = run_actions(
///     LeaseState::init(3),
///     100,
///     |s| LeaseState::all_actions(s),    // enumerate possible actions
///     |s, a| s.can_fire(a),              // gate check
///     |s, a| s.fire(a),                  // pure transition
///     |step, _s, acts| acts[step % acts.len()].clone(), // round-robin pick
///     |step, s| { /* check invariants */ },
/// );
/// ```
pub fn run_actions<S: Clone, A: Clone>(
    init: S,
    num_steps: usize,
    actions: impl Fn(&S) -> Vec<A>,
    can_fire: impl Fn(&S, &A) -> bool,
    step: impl Fn(&S, &A) -> S,
    pick: impl Fn(usize, &S, &[A]) -> A,
    check: impl Fn(usize, &S),
) -> S {
    let mut state = init;
    check(0, &state);

    for i in 0..num_steps {
        let possible = actions(&state);
        if possible.is_empty() {
            continue;
        }
        let action = pick(i, &state, &possible);
        if can_fire(&state, &action) {
            state = step(&state, &action);
            check(i + 1, &state);
        }
    }

    state
}
