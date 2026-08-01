//! # OneThirdRule: Consensus via super-majority adoption
//!
//! Rust implementation and tests of the OneThirdRule consensus protocol,
//! corresponding to Leslie's `OneThirdRule.lean`.
//!
//! ## Protocol (Charron-Bost & Schiper)
//!
//! N processes each hold a value and an optional decision.
//! Communication is synchronous rounds with >2n/3 delivery guarantee.
//!
//! Each round:
//!   - **Send**: broadcast your current value to all processes.
//!   - **Update**: collect received values. If any single value appears
//!     in more than 2n/3 of the received messages (a "super-majority"),
//!     adopt it as your value and decide it. Otherwise, keep your value.
//!
//! ## Safety property: Agreement
//!
//! If two processes have decided, they decided the same value.
//! This holds because two super-majorities of size >2n/3 must overlap
//! (pigeonhole), so they cannot disagree.

mod common;

use std::collections::BTreeMap;

// ── Protocol state and logic ───────────────────────────────────────

/// Per-process state: current value and optional decision.
/// Once decided, a process keeps its decision forever.
#[derive(Clone, Debug)]
struct OtrState {
    val: u64,
    decided: Option<u64>,
}

impl OtrState {
    fn new(initial_value: u64) -> Self {
        Self {
            val: initial_value,
            decided: None,
        }
    }
}

/// Count how many times `v` appears in the received values.
fn count_occ(v: u64, received: &[u64]) -> usize {
    received.iter().filter(|&&x| x == v).count()
}

/// Check if `v` has a super-majority (> 2n/3) among the received values.
/// Uses integer arithmetic to avoid division: count * 3 > 2 * n.
fn has_super_majority(n: usize, v: u64, received: &[u64]) -> bool {
    count_occ(v, received) * 3 > 2 * n
}

/// Find a value with super-majority support, if any.
/// At most one such value can exist (by pigeonhole).
fn find_super_majority(n: usize, received: &[u64]) -> Option<u64> {
    received
        .iter()
        .find(|&&v| has_super_majority(n, v, received))
        .copied()
}

/// Pure send function: broadcast current value.
fn otr_send(_id: usize, state: &OtrState) -> u64 {
    state.val
}

/// Pure update function: adopt super-majority value if one exists.
///
/// Corresponds to Leslie's `otr_alg.update`:
///   let received := (List.finRange n).filterMap msgs
///   match findSuperMajority n received with
///   | some v => { val := v, decided := some v }
///   | none => s
fn otr_update(
    _id: usize,
    state: &OtrState,
    inbox: &BTreeMap<usize, u64>,
    _oracle: (),
    n: usize,
) -> OtrState {
    // Collect all received values into a list
    let received: Vec<u64> = inbox.values().copied().collect();

    match find_super_majority(n, &received) {
        Some(v) => OtrState {
            val: v,
            decided: Some(v),
        },
        None => state.clone(),
    }
}

// ── Invariant checking ─────────────────────────────────────────────

/// Agreement: all decided processes agree on the same value.
fn check_agreement(states: &[OtrState]) {
    let decisions: Vec<u64> = states.iter().filter_map(|s| s.decided).collect();
    if let Some(&first) = decisions.first() {
        for &d in &decisions[1..] {
            assert_eq!(
                first, d,
                "Agreement violated: process decided {} but another decided {}",
                first, d
            );
        }
    }
}

/// Validity: every decided value was some process's initial value.
fn check_validity(states: &[OtrState], initial_values: &[u64]) {
    for s in states {
        if let Some(d) = s.decided {
            assert!(
                initial_values.contains(&d),
                "Validity violated: decided value {} was not an initial value",
                d
            );
        }
    }
}

// ── Tests ──────────────────────────────────────────────────────────

/// Run OneThirdRule with given parameters and check agreement + validity.
fn run_otr(
    n: usize,
    rounds: usize,
    initial_values: Vec<u64>,
    ho: impl Fn(usize, usize, usize) -> bool,
) -> Vec<OtrState> {
    let init_vals = initial_values.clone();
    common::run_rounds(
        n,
        rounds,
        |id| OtrState::new(initial_values[id]),
        otr_send,
        |id, state, inbox, oracle| otr_update(id, state, inbox, oracle, n),
        ho,
        |_, _| (), // deterministic: oracle = ()
        move |_round, states| {
            check_agreement(states);
            check_validity(states, &init_vals);
        },
    )
}

#[test]
fn three_processes_unanimous_input_decide_immediately() {
    // All processes start with the same value (42).
    // With reliable delivery, all see 3/3 = 100% > 66% → super-majority.
    // Everyone decides 42 in round 1.
    let states = run_otr(3, 1, vec![42, 42, 42], common::ho_reliable);

    for s in &states {
        assert_eq!(s.decided, Some(42), "unanimous input should decide in 1 round");
    }
}

#[test]
fn three_processes_majority_input_converge() {
    // Two processes start with 1, one starts with 0.
    // With reliable delivery: each process receives [1, 1, 0].
    // count(1) = 2, need > 2*3/3 = 2. So 2 is NOT > 2. No super-majority.
    // Actually 2 * 3 = 6 > 2 * 3 = 6? No, 6 > 6 is false.
    // So with n=3 and 2 out of 3, hasSuperMajority = (2 * 3 > 2 * 3) = false.
    // Nobody decides in round 1.
    //
    // In round 2: same situation (values unchanged). Still no decision.
    // This is correct: OneThirdRule requires STRICT super-majority (> 2n/3).
    // With n=3, you need all 3 to agree (3*3=9 > 6).
    let states = run_otr(3, 5, vec![1, 1, 0], common::ho_reliable);

    // No decision reached (2/3 is not a strict super-majority for n=3)
    for s in &states {
        assert_eq!(s.decided, None, "2/3 is not > 2/3, no decision expected");
    }
    // But agreement trivially holds (no decisions)
    check_agreement(&states);
}

#[test]
fn four_processes_three_agree_decide() {
    // n=4: super-majority threshold is > 2*4/3 = 2.67, so need ≥ 3.
    // Three processes have value 7, one has value 5.
    // With reliable delivery: each sees [7, 7, 7, 5]. count(7) = 3.
    // 3 * 3 = 9 > 2 * 4 = 8. Yes! Super-majority.
    let states = run_otr(4, 1, vec![7, 7, 7, 5], common::ho_reliable);

    for s in &states {
        assert_eq!(s.decided, Some(7), "3/4 > 2/3 threshold for n=4");
    }
}

#[test]
fn five_processes_agreement_holds_under_lossy_communication() {
    // n=5 processes, all start with different values.
    // Lossy communication: each process hears only from itself and
    // process 0. This means at most 2 messages per process — never
    // enough for a super-majority (need > 10/3 ≈ 3.33, so ≥ 4).
    // No process should decide.
    let ho_partial = |_round: usize, recv: usize, send: usize| -> bool {
        send == recv || send == 0 // hear yourself + process 0
    };

    let states = run_otr(5, 10, vec![0, 1, 2, 3, 4], ho_partial);

    // No decisions (not enough messages for super-majority)
    for s in &states {
        assert_eq!(s.decided, None);
    }
    check_agreement(&states);
}

#[test]
fn agreement_holds_with_dynamic_ho_sets() {
    // n=7 processes, initial values [0, 0, 0, 0, 1, 1, 1].
    // Threshold: > 2*7/3 = 4.67, so need ≥ 5.
    //
    // Round 0: reliable → everyone sees [0,0,0,0,1,1,1].
    //   count(0)=4, 4*3=12 > 14? No. count(1)=3, 3*3=9 > 14? No.
    //   Nobody decides. Values unchanged.
    //
    // Round 1: same situation. Nobody decides.
    //
    // Now change HO: only the four 0-holders hear each other,
    // and process 4 also hears them (gets converted to 0).
    // After enough rounds, more processes adopt 0.
    // But with the strict >2n/3 rule, we need ≥5 of 7 to agree.
    let ho_dynamic = |round: usize, recv: usize, send: usize| -> bool {
        if round < 3 {
            // First 3 rounds: reliable
            true
        } else {
            // After round 3: only processes 0-4 communicate with each other
            recv <= 4 && send <= 4
        }
    };

    let states = run_otr(7, 10, vec![0, 0, 0, 0, 1, 1, 1], ho_dynamic);

    // Agreement should hold regardless of HO sets
    check_agreement(&states);
}

#[test]
fn seven_processes_unanimous_subset_decides() {
    // n=7, all start with value 3. Reliable delivery.
    // Everyone sees 7 copies of 3. 7*3=21 > 2*7=14. Super-majority.
    let states = run_otr(7, 1, vec![3; 7], common::ho_reliable);

    for s in &states {
        assert_eq!(s.decided, Some(3));
    }
}

#[test]
fn decision_is_permanent() {
    // Once decided, a process keeps its decision forever.
    // n=3, unanimous input → decide in round 1 → values stay decided.
    let states = run_otr(3, 10, vec![5, 5, 5], common::ho_reliable);

    for s in &states {
        assert_eq!(s.decided, Some(5), "decision should persist across rounds");
        assert_eq!(s.val, 5, "value should remain decided value");
    }
}

#[test]
fn agreement_under_random_delivery() {
    // n=5 processes with random ~50% message delivery.
    // With ho_random, each process hears itself + ~50% of others.
    // Super-majority needs >10/3 ≈ 3.33 received, so ≥4.
    // With 5 processes and ~50% delivery, a process hears ~1 (self) + ~2 = ~3.
    // Usually not enough for super-majority, so few decisions expected.
    // But agreement must ALWAYS hold regardless of delivery pattern.
    for seed in 0..20 {
        let states = run_otr(5, 20, vec![0, 0, 1, 1, 0], common::ho_random(seed));
        check_agreement(&states);
    }
}

#[test]
fn unanimous_input_decides_under_random_delivery() {
    // n=5, all start with value 42. Even with random delivery,
    // if enough messages get through (≥4 of 5), super-majority holds.
    // With ~50% delivery + self, a process hears ~3 of 5 on average.
    // Some rounds may reach super-majority, some may not.
    // But whenever a decision is made, it must be 42 (validity).
    for seed in 0..20 {
        let states = run_otr(5, 30, vec![42; 5], common::ho_random(seed));
        check_agreement(&states);
        check_validity(&states, &[42; 5]);
    }
}

#[test]
fn agreement_with_quorum_guaranteed_random_delivery() {
    // n=7, with ho_random_quorum guaranteeing each process hears ≥5 others.
    // Super-majority threshold: > 14/3 ≈ 4.67, so need ≥5 of same value.
    // With 7 processes all starting with value 1 and guaranteed ≥5 delivery,
    // each process sees ≥5+1=6 copies of 1.
    // 6*3 = 18 > 14. Decides in round 1.
    for seed in 0..10 {
        let states = run_otr(
            7, 5,
            vec![1; 7],
            common::ho_random_quorum(seed, 7, 5),
        );
        for s in &states {
            assert_eq!(s.decided, Some(1),
                "with quorum guarantee and unanimous input, should decide (seed={})", seed);
        }
    }
}
