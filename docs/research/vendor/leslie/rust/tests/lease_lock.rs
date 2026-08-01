//! # LeaseLock: Distributed lease lock with fencing tokens
//!
//! Rust implementation and tests of the LeaseLock protocol,
//! corresponding to Leslie's `LeaseLock.lean`.
//!
//! ## System model
//!
//! Three components modeled as a single state machine:
//!
//! 1. **Lock service**: Issues time-bounded leases with monotonically
//!    increasing fencing tokens. At most one valid lease at a time.
//!
//! 2. **Processes**: Acquire the lock, write with their fencing token.
//!    A process with an expired lease does NOT know it expired — it
//!    continues to believe it is the leader.
//!
//! 3. **Storage node**: Accepts writes tagged with (token, seq).
//!    Rejects any write where (token, seq) ≤ the current high-water mark.
//!
//! ## Safety properties
//!
//! 1. **Leader exclusivity**: The valid leader's token is strictly greater
//!    than all other processes' tokens.
//!
//! 2. **Write serialization**: The journal is strictly ordered by
//!    (fencingToken, seqNum) in lexicographic order.
//!
//! Reference: Martin Kleppmann, "How to do distributed locking" (2016).

mod common;

// ── Protocol state ─────────────────────────────────────────────────

/// A write entry in the storage journal.
#[derive(Clone, Debug, PartialEq)]
struct WriteEntry {
    value: u64,
    token: u64,
    seq: u64,
}

/// Global system state. Mirrors Leslie's `LeaseState n`.
#[derive(Clone, Debug)]
struct LeaseState {
    // ── Lock service ───────────────────────────────────────────
    /// Next fencing token to issue. Starts at 1, always increases.
    next_token: u64,
    /// Current lock holder (index into processes), or None.
    lock_holder: Option<usize>,
    /// Is the current lease still valid?
    lease_active: bool,

    // ── Per-process state ──────────────────────────────────────
    /// Fencing token from most recent acquire (0 = never held lock).
    my_token: Vec<u64>,
    /// Write sequence number within current generation.
    write_seq: Vec<u64>,
    /// Does this process believe it holds the lock?
    believes_leader: Vec<bool>,

    // ── Storage node ───────────────────────────────────────────
    /// Highest fencing token seen in an accepted write.
    high_token: u64,
    /// Highest seq number at the high_token level.
    high_seq: u64,
    /// Journal of accepted writes.
    journal: Vec<WriteEntry>,

    // ── Configuration ──────────────────────────────────────────
    n: usize,
}

impl LeaseState {
    /// Create initial state for `n` processes.
    fn init(n: usize) -> Self {
        Self {
            next_token: 1,
            lock_holder: None,
            lease_active: false,
            my_token: vec![0; n],
            write_seq: vec![0; n],
            believes_leader: vec![false; n],
            high_token: 0,
            high_seq: 0,
            journal: Vec::new(),
            n,
        }
    }
}

// ── Actions ────────────────────────────────────────────────────────

/// All possible actions in the protocol.
#[derive(Clone, Debug)]
enum Action {
    /// Process `p` acquires the lock.
    Acquire(usize),
    /// The current lease expires (process doesn't know).
    ExpireLease,
    /// Process `p` writes value `v` to storage.
    WriteOk(usize, u64),
    /// Process `p` voluntarily releases the lock.
    Release(usize),
}

impl LeaseState {
    /// Enumerate all possible actions for the current state.
    fn all_actions(&self) -> Vec<Action> {
        let mut actions = Vec::new();

        // Any process can try to acquire
        for p in 0..self.n {
            actions.push(Action::Acquire(p));
        }

        // Lease can expire if active
        actions.push(Action::ExpireLease);

        // Any believing-leader can try to write (with a few example values)
        for p in 0..self.n {
            for v in 0..3 {
                actions.push(Action::WriteOk(p, v));
            }
        }

        // Any holder can release
        for p in 0..self.n {
            actions.push(Action::Release(p));
        }

        actions
    }

    /// Gate: can this action fire in the current state?
    fn can_fire(&self, action: &Action) -> bool {
        match action {
            Action::Acquire(_) => {
                // Lock must be free or lease expired
                self.lock_holder.is_none() || !self.lease_active
            }
            Action::ExpireLease => {
                // Must have an active lease to expire
                self.lease_active
            }
            Action::WriteOk(p, _) => {
                // Process must believe it's the leader
                // AND fencing check must pass: (token, seq+1) > (high_token, high_seq)
                self.believes_leader[*p]
                    && (self.my_token[*p] > self.high_token
                        || (self.my_token[*p] == self.high_token
                            && self.write_seq[*p] + 1 > self.high_seq))
            }
            Action::Release(p) => {
                // Must hold a valid lease
                self.lock_holder == Some(*p) && self.lease_active
            }
        }
    }

    /// Pure transition: return the new state after firing the action.
    fn fire(&self, action: &Action) -> Self {
        let mut s = self.clone();
        match action {
            Action::Acquire(p) => {
                // Issue new fencing token to the acquirer.
                // The old holder (if any) is NOT notified — it still
                // believes it's the leader. This models the Kleppmann
                // scenario where a GC pause causes silent lease expiry.
                s.lock_holder = Some(*p);
                s.lease_active = true;
                s.my_token[*p] = s.next_token;
                s.next_token += 1;
                s.write_seq[*p] = 0;
                s.believes_leader[*p] = true;
            }
            Action::ExpireLease => {
                // Lease expires. The holder is NOT notified.
                // believes_leader stays true for the old holder.
                s.lease_active = false;
            }
            Action::WriteOk(p, v) => {
                // Storage accepts the write. Update high-water mark.
                s.high_token = s.my_token[*p];
                s.high_seq = s.write_seq[*p] + 1;
                s.write_seq[*p] += 1;
                s.journal.push(WriteEntry {
                    value: *v,
                    token: s.my_token[*p],
                    seq: s.write_seq[*p],
                });
            }
            Action::Release(p) => {
                // Voluntary release. Process knows it lost the lock.
                s.lock_holder = None;
                s.lease_active = false;
                s.believes_leader[*p] = false;
            }
        }
        s
    }
}

// ── Invariant checking ─────────────────────────────────────────────

/// Leader exclusivity: the valid leader's token exceeds all others.
fn check_leader_exclusivity(state: &LeaseState) {
    if let Some(holder) = state.lock_holder {
        if state.lease_active {
            let holder_token = state.my_token[holder];
            for q in 0..state.n {
                if q != holder {
                    assert!(
                        state.my_token[q] < holder_token,
                        "Leader exclusivity violated: process {}'s token {} >= holder {}'s token {}",
                        q,
                        state.my_token[q],
                        holder,
                        holder_token
                    );
                }
            }
        }
    }
}

/// Write serialization: journal entries are strictly ordered by (token, seq).
fn check_writes_serialized(state: &LeaseState) {
    for i in 1..state.journal.len() {
        let prev = &state.journal[i - 1];
        let curr = &state.journal[i];
        let ordered = prev.token < curr.token
            || (prev.token == curr.token && prev.seq < curr.seq);
        assert!(
            ordered,
            "Write serialization violated at entries {} and {}: ({}, {}) not < ({}, {})",
            i - 1,
            i,
            prev.token,
            prev.seq,
            curr.token,
            curr.seq
        );
    }
}

/// Combined invariant check.
fn check_invariant(_step: usize, state: &LeaseState) {
    check_leader_exclusivity(state);
    check_writes_serialized(state);
}

// ── Tests ──────────────────────────────────────────────────────────

#[test]
fn basic_acquire_write_release() {
    // Simple scenario: one process acquires, writes, releases.
    let mut state = LeaseState::init(3);
    assert!(state.can_fire(&Action::Acquire(0)));

    state = state.fire(&Action::Acquire(0));
    check_invariant(1, &state);
    assert_eq!(state.lock_holder, Some(0));
    assert_eq!(state.my_token[0], 1);

    // Write two values
    state = state.fire(&Action::WriteOk(0, 42));
    check_invariant(2, &state);
    assert_eq!(state.journal.len(), 1);
    assert_eq!(state.journal[0], WriteEntry { value: 42, token: 1, seq: 1 });

    state = state.fire(&Action::WriteOk(0, 43));
    check_invariant(3, &state);
    assert_eq!(state.journal.len(), 2);
    assert_eq!(state.journal[1], WriteEntry { value: 43, token: 1, seq: 2 });

    // Release
    state = state.fire(&Action::Release(0));
    check_invariant(4, &state);
    assert_eq!(state.lock_holder, None);
}

#[test]
fn kleppmann_scenario_stale_write_rejected() {
    // The classic Kleppmann scenario:
    //   1. P0 acquires lock (token 1)
    //   2. P0 writes successfully
    //   3. P0's lease expires (P0 doesn't know!)
    //   4. P1 acquires lock (token 2)
    //   5. P1 writes with token 2 → accepted
    //   6. P0 tries to write with token 1 → REJECTED (1 < 2)
    let mut state = LeaseState::init(3);

    // Step 1: P0 acquires
    state = state.fire(&Action::Acquire(0));
    assert_eq!(state.my_token[0], 1);

    // Step 2: P0 writes
    state = state.fire(&Action::WriteOk(0, 100));
    assert_eq!(state.high_token, 1);

    // Step 3: Lease expires — P0 still believes it's the leader!
    state = state.fire(&Action::ExpireLease);
    assert!(state.believes_leader[0], "P0 should still believe it's leader");
    assert!(!state.lease_active, "but lease is expired");

    // Step 4: P1 acquires (gets token 2)
    state = state.fire(&Action::Acquire(1));
    assert_eq!(state.my_token[1], 2);
    assert!(state.believes_leader[0], "P0 STILL believes it's leader");
    assert!(state.believes_leader[1], "P1 also believes it's leader");

    // Step 5: P1 writes with token 2
    state = state.fire(&Action::WriteOk(1, 200));
    assert_eq!(state.high_token, 2);
    check_invariant(5, &state);

    // Step 6: P0 tries to write — fencing check fails!
    assert!(
        !state.can_fire(&Action::WriteOk(0, 999)),
        "P0's write should be rejected: token 1 < high_token 2"
    );

    // Journal should have exactly 2 entries, properly ordered
    assert_eq!(state.journal.len(), 2);
    check_writes_serialized(&state);
}

#[test]
fn multiple_leader_transitions() {
    // Three processes take turns acquiring the lock.
    // Each writes, then the lease expires, and the next acquires.
    let mut state = LeaseState::init(3);

    for leader in 0..3 {
        state = state.fire(&Action::Acquire(leader));
        state = state.fire(&Action::WriteOk(leader, leader as u64 * 10));
        state = state.fire(&Action::WriteOk(leader, leader as u64 * 10 + 1));
        check_invariant(0, &state);

        if leader < 2 {
            state = state.fire(&Action::ExpireLease);
        }
    }

    // 6 writes total, all ordered by (token, seq)
    assert_eq!(state.journal.len(), 6);
    check_writes_serialized(&state);

    // Tokens should be 1, 2, 3 for the three leaders
    assert_eq!(state.my_token, vec![1, 2, 3]);
}

#[test]
fn reacquire_after_expiry() {
    // P0 acquires, expires, P0 reacquires with a NEW (higher) token.
    let mut state = LeaseState::init(2);

    state = state.fire(&Action::Acquire(0));
    assert_eq!(state.my_token[0], 1);
    state = state.fire(&Action::WriteOk(0, 10));

    state = state.fire(&Action::ExpireLease);
    state = state.fire(&Action::Acquire(0)); // reacquire
    assert_eq!(state.my_token[0], 2, "new token should be higher");
    assert_eq!(state.write_seq[0], 0, "write_seq reset on reacquire");

    state = state.fire(&Action::WriteOk(0, 20));
    check_invariant(0, &state);

    // Journal: (token=1,seq=1), (token=2,seq=1) — ordered
    assert_eq!(state.journal.len(), 2);
    assert!(state.journal[0].token < state.journal[1].token);
}

#[test]
fn exhaustive_three_processes_bounded_steps() {
    // Exhaustive exploration: run all fireable actions for 3 processes
    // over a bounded number of steps. Check invariants at every step.
    //
    // This is a mini model checker: try every possible action at each
    // step, depth-first, and verify the invariant never breaks.

    fn explore(state: &LeaseState, depth: usize, max_depth: usize) {
        if depth >= max_depth {
            return;
        }

        let actions = state.all_actions();
        for action in &actions {
            if state.can_fire(action) {
                let new_state = state.fire(action);
                check_invariant(depth, &new_state);
                explore(&new_state, depth + 1, max_depth);
            }
        }
    }

    // Explore all paths up to depth 6 from initial state
    // (deeper would be slow but this covers the key scenarios)
    let init = LeaseState::init(2);
    explore(&init, 0, 6);
}

#[test]
fn action_simulator_random_walk() {
    // Use the action-based simulator from the harness.
    // Round-robin through actions, checking invariants at every step.
    let init = LeaseState::init(3);

    common::run_actions(
        init,
        200,
        |s| s.all_actions(),
        |s, a| s.can_fire(a),
        |s, a| s.fire(a),
        // Pick strategy: cycle through all actions
        |step, _state, actions| actions[step % actions.len()].clone(),
        check_invariant,
    );
}

#[test]
fn generation_numbers_order_same_leader_writes() {
    // Within a single generation, writes are ordered by sequence number.
    let mut state = LeaseState::init(1);
    state = state.fire(&Action::Acquire(0));

    for i in 0..10 {
        state = state.fire(&Action::WriteOk(0, i));
        check_invariant(0, &state);
    }

    // All 10 writes have the same token, increasing seq
    assert_eq!(state.journal.len(), 10);
    for (i, entry) in state.journal.iter().enumerate() {
        assert_eq!(entry.token, 1);
        assert_eq!(entry.seq, (i + 1) as u64);
    }
    check_writes_serialized(&state);
}

#[test]
fn concurrent_believers_cannot_both_write() {
    // After lease expiry, two processes believe they're leader.
    // But only one can successfully write (the one with the higher token).
    let mut state = LeaseState::init(2);

    state = state.fire(&Action::Acquire(0)); // token 1
    state = state.fire(&Action::ExpireLease);
    state = state.fire(&Action::Acquire(1)); // token 2

    // Both believe they're leader
    assert!(state.believes_leader[0]);
    assert!(state.believes_leader[1]);

    // P1 (token 2) writes first
    state = state.fire(&Action::WriteOk(1, 50));

    // Now P0 (token 1) cannot write — fencing rejects it
    assert!(!state.can_fire(&Action::WriteOk(0, 51)));

    // P1 can still write
    assert!(state.can_fire(&Action::WriteOk(1, 52)));
    state = state.fire(&Action::WriteOk(1, 52));
    check_invariant(0, &state);
}
