use crate::comm::{Communication, Inbox, InboxExt};
use crate::protocol::Protocol;

/// Drive one protocol step against a communication object.
///
/// The sequence is: send → collect inbox → update → tick.
///
/// The caller provides:
/// - `round_pred`, which determines which remote rounds are accepted
/// - `done`, which determines when enough matching messages have been gathered
/// - `oracle`, for any nondeterminism used by the update step
///
/// `alg` is taken by `&mut` so the driver can replace the state with
/// the pure result of `update`. The protocol logic itself is pure.
pub fn run_step<C, A, M, RP, DONE>(
    comm: &mut C,
    alg: &mut A,
    round_pred: RP,
    done: DONE,
    oracle: A::Oracle,
) -> Result<(), C::Error>
where
    C: InboxExt<M>,
    A: Protocol<C::Peer, C::Round, Msg = M>,
    M: Clone,
    RP: FnMut(&C::Round, &C::Round) -> bool,
    DONE: FnMut(&Inbox<C::Peer, M>) -> bool,
{
    let local_round = comm.round().clone();
    comm.send(alg.send(&local_round))?;
    let inbox = comm.inbox(round_pred, done)?;
    *alg = alg.update(&local_round, &inbox, oracle);
    comm.tick();
    Ok(())
}

/// Common case: accept only messages from the current local round.
pub fn run_current_round_step<C, A, M, DONE>(
    comm: &mut C,
    alg: &mut A,
    done: DONE,
    oracle: A::Oracle,
) -> Result<(), C::Error>
where
    C: Communication<M> + InboxExt<M>,
    A: Protocol<C::Peer, C::Round, Msg = M>,
    M: Clone,
    DONE: FnMut(&Inbox<C::Peer, M>) -> bool,
{
    run_step(comm, alg, |local, remote| local == remote, done, oracle)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::comm::{Envelope, Process, Round, Transport};
    use std::collections::VecDeque;

    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct TestRound(u64);

    impl Round for TestRound {
        fn tick_impl(&mut self) {
            self.0 += 1;
        }
    }

    struct QueueTransport<P, R, M> {
        sent: Vec<Envelope<P, R, M>>,
        recv: VecDeque<Envelope<P, R, M>>,
    }

    impl<P, R, M> QueueTransport<P, R, M> {
        fn new() -> Self {
            Self {
                sent: Vec::new(),
                recv: VecDeque::new(),
            }
        }

        fn push_recv(&mut self, env: Envelope<P, R, M>) {
            self.recv.push_back(env);
        }
    }

    impl<P, R, M> Transport<P, R, M> for QueueTransport<P, R, M> {
        type Error = ();

        fn send_envelope(&mut self, env: Envelope<P, R, M>) -> Result<(), Self::Error> {
            self.sent.push(env);
            Ok(())
        }

        fn recv_envelope(&mut self) -> Result<Option<Envelope<P, R, M>>, Self::Error> {
            Ok(self.recv.pop_front())
        }
    }

    // ── EchoProtocol: deterministic (Oracle = ()) ──────────────

    #[derive(Clone, Default)]
    struct EchoProtocol {
        observed: Vec<(u8, &'static str)>,
    }

    impl Protocol<u8, TestRound> for EchoProtocol {
        type Msg = &'static str;
        type Oracle = ();

        fn send(&self, _round: &TestRound) -> Self::Msg {
            "proposal"
        }

        fn update(
            &self,
            _round: &TestRound,
            inbox: &Inbox<u8, Self::Msg>,
            _oracle: Self::Oracle,
        ) -> Self {
            Self {
                observed: inbox.iter().map(|(p, m)| (*p, *m)).collect(),
            }
        }
    }

    #[test]
    fn run_current_round_step_sends_updates_and_ticks() {
        let mut transport = QueueTransport::<u8, TestRound, &'static str>::new();
        transport.push_recv(Envelope {
            from: 2,
            round: TestRound(4),
            payload: "v2",
        });
        transport.push_recv(Envelope {
            from: 3,
            round: TestRound(4),
            payload: "v3",
        });

        let mut process = Process::new(1, TestRound(4), transport);
        let mut proto = EchoProtocol::default();

        run_current_round_step(&mut process, &mut proto, |acc| acc.len() >= 2, ()).unwrap();

        assert_eq!(proto.observed, vec![(2, "v2"), (3, "v3")]);
        assert_eq!(process.round().0, 5);
    }

    // ── CoinFlipProtocol: nondeterministic (Oracle = bool) ─────
    //
    // A minimal protocol demonstrating nondeterministic oracle usage.
    // Each process holds a binary value. In each round:
    //   send: broadcast current value
    //   update: if a majority of received values agree, adopt that value;
    //           otherwise, flip to the oracle's choice.
    //
    // This is a simplified Ben-Or-style pattern where the oracle
    // represents a coin flip used to break ties.

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct CoinFlipProtocol {
        value: bool,
        n: usize,
    }

    impl CoinFlipProtocol {
        fn new(value: bool, n: usize) -> Self {
            Self { value, n }
        }
    }

    impl Protocol<u8, TestRound> for CoinFlipProtocol {
        type Msg = bool;
        type Oracle = bool; // coin flip: true or false

        fn send(&self, _round: &TestRound) -> Self::Msg {
            self.value
        }

        fn update(
            &self,
            _round: &TestRound,
            inbox: &Inbox<u8, Self::Msg>,
            oracle: Self::Oracle,
        ) -> Self {
            let true_count = inbox.values().filter(|&&v| v).count();
            let false_count = inbox.values().filter(|&&v| !v).count();
            let total = inbox.len();

            let new_value = if true_count * 2 > total {
                // Majority says true → adopt true (deterministic)
                true
            } else if false_count * 2 > total {
                // Majority says false → adopt false (deterministic)
                false
            } else {
                // No majority → flip coin (nondeterministic, oracle decides)
                oracle
            };

            Self {
                value: new_value,
                n: self.n,
            }
        }
    }

    #[test]
    fn coin_flip_majority_overrides_oracle() {
        // If a majority agrees, the oracle is ignored.
        let proto = CoinFlipProtocol::new(false, 3);
        let mut inbox = Inbox::new();
        inbox.insert(0_u8, true);
        inbox.insert(1_u8, true);
        inbox.insert(2_u8, false);

        // Majority is true (2 out of 3). Oracle says false.
        let result = proto.update(&TestRound(0), &inbox, false);
        assert_eq!(result.value, true, "majority should override oracle");

        // Oracle says true — same result, oracle is irrelevant.
        let result2 = proto.update(&TestRound(0), &inbox, true);
        assert_eq!(result2.value, true);
    }

    #[test]
    fn coin_flip_uses_oracle_on_tie() {
        // With no majority, the oracle decides.
        let proto = CoinFlipProtocol::new(false, 4);
        let mut inbox = Inbox::new();
        inbox.insert(0_u8, true);
        inbox.insert(1_u8, false);

        // Tie: 1 true, 1 false. Oracle = true → value becomes true.
        let result = proto.update(&TestRound(0), &inbox, true);
        assert_eq!(result.value, true, "oracle=true should win on tie");

        // Same tie. Oracle = false → value becomes false.
        let result2 = proto.update(&TestRound(0), &inbox, false);
        assert_eq!(result2.value, false, "oracle=false should win on tie");
    }

    #[test]
    fn coin_flip_oracle_explored_exhaustively() {
        // Demonstrate that we can enumerate all oracle values to explore
        // the full nondeterministic state space — the key advantage of
        // the explicit Oracle design over an opaque Rng.
        let proto = CoinFlipProtocol::new(true, 3);
        let mut inbox = Inbox::new();
        inbox.insert(0_u8, true);
        inbox.insert(1_u8, false);
        inbox.insert(2_u8, false);

        // No majority (1 true vs 2 false? Actually 2 false > 1 true... let me check)
        // 2*2 > 3? 4 > 3, yes. So false has majority → deterministic.
        // Let's use an even split instead.
        let mut inbox2 = Inbox::new();
        inbox2.insert(0_u8, true);
        inbox2.insert(1_u8, false);

        // Enumerate all oracle values
        let oracle_values = [true, false];
        let results: Vec<bool> = oracle_values
            .iter()
            .map(|&oracle| proto.update(&TestRound(0), &inbox2, oracle).value)
            .collect();

        // Both branches explored: oracle=true → true, oracle=false → false
        assert_eq!(results, vec![true, false]);
        assert!(
            results.contains(&true) && results.contains(&false),
            "exhaustive oracle exploration should cover both outcomes"
        );
    }

    #[test]
    fn coin_flip_runs_through_driver() {
        // End-to-end: run CoinFlipProtocol through the driver with an oracle.
        let mut transport = QueueTransport::<u8, TestRound, bool>::new();
        // Two peers send: one true, one false → tie → oracle decides
        transport.push_recv(Envelope {
            from: 1,
            round: TestRound(0),
            payload: true,
        });
        transport.push_recv(Envelope {
            from: 2,
            round: TestRound(0),
            payload: false,
        });

        let mut process = Process::new(0_u8, TestRound(0), transport);
        let mut proto = CoinFlipProtocol::new(true, 3);

        // Oracle = false → on tie, adopt false
        run_current_round_step(&mut process, &mut proto, |acc| acc.len() >= 2, false).unwrap();

        assert_eq!(proto.value, false, "oracle=false on tie → value=false");
        assert_eq!(process.round().0, 1, "round should advance");
    }

    #[test]
    fn update_is_pure_returns_new_state() {
        // Verify that update does not mutate the original — it returns
        // a new value, and the old one is unchanged.
        let proto = CoinFlipProtocol::new(true, 3);
        let inbox = Inbox::new();

        let new_proto = proto.update(&TestRound(0), &inbox, false);

        // Oracle = false, empty inbox → no majority → adopt oracle = false
        assert_eq!(new_proto.value, false);
        // Original is unchanged (purity)
        assert_eq!(proto.value, true);
    }
}
