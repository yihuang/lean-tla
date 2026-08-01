use crate::comm::{BallotPhase, Inbox, PeerId};
use crate::protocol::Protocol;
use std::collections::BTreeMap;

/// Default peer identifier used by the current examples.
///
/// The wrapper keeps the protocol independent of the eventual concrete
/// identity representation.
pub type DefaultPeerId = PeerId<usize>;

/// Local state for the phased ballot leader protocol.
///
/// The nondeterministic bid decision is represented by the `bidding` field,
/// matching the Lean model's choice to encode bidding in the initial state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct State<P> {
    pub id: P,
    pub n: usize,
    pub bidding: bool,
    pub picked: Option<P>,
    pub leader: Option<P>,
}

impl<P> State<P> {
    pub fn new(id: P, n: usize, bidding: bool) -> Self {
        Self {
            id,
            n,
            bidding,
            picked: None,
            leader: None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Msg<P> {
    Bid(P),
    NoBid,
    Pick(P),
    NoPick,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BallotLeaderPhased<P> {
    pub state: State<P>,
}

impl<P> BallotLeaderPhased<P> {
    pub fn new(id: P, n: usize, bidding: bool) -> Self {
        Self {
            state: State::new(id, n, bidding),
        }
    }

    pub fn state(&self) -> &State<P> {
        &self.state
    }
}

impl<P> BallotLeaderPhased<P>
where
    P: Clone + Ord + Eq,
{
    fn collect_bids(inbox: &Inbox<P, Msg<P>>) -> Vec<P> {
        inbox
            .values()
            .filter_map(|msg| match msg {
                Msg::Bid(id) => Some(id.clone()),
                _ => None,
            })
            .collect()
    }

    fn collect_picks(inbox: &Inbox<P, Msg<P>>) -> Vec<P> {
        inbox
            .values()
            .filter_map(|msg| match msg {
                Msg::Pick(id) => Some(id.clone()),
                _ => None,
            })
            .collect()
    }

    fn min_bidder(bids: &[P]) -> Option<P> {
        bids.iter().cloned().min()
    }

    fn find_majority(n: usize, picks: &[P]) -> Option<P> {
        let mut counts: BTreeMap<P, usize> = BTreeMap::new();
        for pick in picks {
            *counts.entry(pick.clone()).or_insert(0) += 1;
        }
        counts
            .into_iter()
            .find_map(|(candidate, count)| (count * 2 > n).then_some(candidate))
    }
}

impl<P> Protocol<P, BallotPhase> for BallotLeaderPhased<P>
where
    P: Clone + Ord + Eq,
{
    type Msg = Msg<P>;
    type Oracle = ();

    fn send(&self, round: &BallotPhase) -> Self::Msg {
        assert_eq!(
            round.num_phases, 2,
            "BallotLeaderPhased expects exactly 2 phases"
        );
        match round.phase {
            0 => {
                if self.state.bidding {
                    Msg::Bid(self.state.id.clone())
                } else {
                    Msg::NoBid
                }
            }
            1 => match &self.state.picked {
                Some(candidate) => Msg::Pick(candidate.clone()),
                None => Msg::NoPick,
            },
            _ => unreachable!("BallotPhase::new guarantees phase < num_phases"),
        }
    }

    fn update(&self, round: &BallotPhase, inbox: &Inbox<P, Self::Msg>, _oracle: Self::Oracle) -> Self {
        assert_eq!(
            round.num_phases, 2,
            "BallotLeaderPhased expects exactly 2 phases"
        );
        let new_state = match round.phase {
            0 => {
                let bids = Self::collect_bids(inbox);
                State { picked: Self::min_bidder(&bids), ..self.state.clone() }
            }
            1 => {
                let picks = Self::collect_picks(inbox);
                State { leader: Self::find_majority(self.state.n, &picks), ..self.state.clone() }
            }
            _ => unreachable!("BallotPhase::new guarantees phase < num_phases"),
        };
        Self { state: new_state }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::comm::{BallotPhase, Communication, Envelope, InMemoryTransport, Process};
    use crate::driver::run_current_round_step;

    fn peer(id: usize) -> DefaultPeerId {
        PeerId::new(id)
    }

    #[test]
    fn phase_zero_picks_min_bidder() {
        let proto = BallotLeaderPhased::new(peer(1), 4, true);
        let mut inbox = Inbox::new();
        inbox.insert(peer(0), Msg::Bid(peer(3)));
        inbox.insert(peer(2), Msg::Bid(peer(1)));
        inbox.insert(peer(3), Msg::NoBid);

        let proto = proto.update(&BallotPhase::new(0, 0, 2), &inbox, ());

        assert_eq!(proto.state().picked, Some(peer(1)));
        assert_eq!(proto.send(&BallotPhase::new(0, 1, 2)), Msg::Pick(peer(1)));
    }

    #[test]
    fn phase_one_elects_majority_pick() {
        let mut proto = BallotLeaderPhased::new(peer(1), 3, true);
        proto.state.picked = Some(peer(2));

        let mut inbox = Inbox::new();
        inbox.insert(peer(0), Msg::Pick(peer(2)));
        inbox.insert(peer(2), Msg::Pick(peer(2)));

        let proto = proto.update(&BallotPhase::new(0, 1, 2), &inbox, ());

        assert_eq!(proto.state().leader, Some(peer(2)));
    }

    #[test]
    fn two_phase_run_elects_single_leader() {
        let transport = InMemoryTransport::with_incoming([
            Envelope {
                from: peer(0),
                round: BallotPhase::new(0, 0, 2),
                payload: Msg::Bid(peer(0)),
            },
            Envelope {
                from: peer(2),
                round: BallotPhase::new(0, 0, 2),
                payload: Msg::Bid(peer(2)),
            },
            Envelope {
                from: peer(0),
                round: BallotPhase::new(0, 1, 2),
                payload: Msg::Pick(peer(0)),
            },
            Envelope {
                from: peer(2),
                round: BallotPhase::new(0, 1, 2),
                payload: Msg::Pick(peer(0)),
            },
        ]);

        let mut process = Process::new(peer(1), BallotPhase::new(0, 0, 2), transport);
        let mut proto = BallotLeaderPhased::new(peer(1), 3, true);

        run_current_round_step(&mut process, &mut proto, |acc| acc.len() >= 2, ()).unwrap();
        assert_eq!(proto.state().picked, Some(peer(0)));
        assert_eq!(*process.round(), BallotPhase::new(0, 1, 2));

        run_current_round_step(&mut process, &mut proto, |acc| acc.len() >= 2, ()).unwrap();
        assert_eq!(proto.state().leader, Some(peer(0)));
        assert_eq!(*process.round(), BallotPhase::new(1, 0, 2));

        let (_, _, transport) = process.into_parts();
        assert_eq!(transport.sent().len(), 2);
        assert_eq!(transport.sent()[0].payload, Msg::Bid(peer(1)));
        assert_eq!(transport.sent()[1].payload, Msg::Pick(peer(0)));
    }
}
