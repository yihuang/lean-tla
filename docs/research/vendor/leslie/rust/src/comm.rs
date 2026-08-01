use std::collections::BTreeMap;
use std::collections::VecDeque;
use std::convert::Infallible;
use std::fmt::Debug;

pub type Inbox<P, M> = BTreeMap<P, M>;

/// Abstract peer identifier wrapper.
///
/// Protocols should prefer this wrapper over using primitive IDs directly,
/// so the concrete identity representation can evolve independently
/// (for example, from integers to IP addresses or endpoint names).
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct PeerId<I>(pub I);

impl<I> PeerId<I> {
    pub fn new(inner: I) -> Self {
        Self(inner)
    }

    pub fn as_inner(&self) -> &I {
        &self.0
    }

    pub fn into_inner(self) -> I {
        self.0
    }
}

pub trait LogicalTime: Ord + Eq + Clone {}

impl<T> LogicalTime for T where T: Ord + Eq + Clone {}

pub trait Round: LogicalTime + Debug {
    fn tick_impl(&mut self);

    fn tick(&mut self) {
        let old = self.clone();
        self.tick_impl();
        debug_assert!(
            *self > old,
            "Round::tick() did not advance time: old={old:?}, new={self:?}"
        );
    }

    fn next(mut self) -> Self
    where
        Self: Sized,
    {
        self.tick();
        self
    }
}

/// A concrete logical time for multi-phase protocols.
///
/// Ordering is lexicographic on `(ballot, phase, num_phases)` via the
/// derived `Ord` instance. Intended use keeps `num_phases` constant.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BallotPhase {
    pub ballot: u64,
    pub phase: u8,
    pub num_phases: u8,
}

impl BallotPhase {
    pub fn new(ballot: u64, phase: u8, num_phases: u8) -> Self {
        assert!(num_phases > 0, "BallotPhase requires num_phases > 0");
        assert!(
            phase < num_phases,
            "BallotPhase phase must be < num_phases: phase={phase}, num_phases={num_phases}"
        );
        Self {
            ballot,
            phase,
            num_phases,
        }
    }
}

impl Round for BallotPhase {
    fn tick_impl(&mut self) {
        debug_assert!(self.num_phases > 0);
        if self.phase + 1 < self.num_phases {
            self.phase += 1;
        } else {
            self.ballot += 1;
            self.phase = 0;
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Envelope<P, R, M> {
    pub from: P,
    pub round: R,
    pub payload: M,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Received<P, R, M> {
    pub from: P,
    pub round: R,
    pub payload: M,
}

pub trait Transport<P, R, M> {
    type Error;

    fn send_envelope(&mut self, env: Envelope<P, R, M>) -> Result<(), Self::Error>;
    fn recv_envelope(&mut self) -> Result<Option<Envelope<P, R, M>>, Self::Error>;
}

/// A reusable in-memory transport for testing, simulation, and reference
/// executions.
///
/// `incoming` is the queue observed by `recv_envelope`, while `sent` records
/// every envelope passed to `send_envelope`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InMemoryTransport<P, R, M> {
    sent: Vec<Envelope<P, R, M>>,
    incoming: VecDeque<Envelope<P, R, M>>,
}

impl<P, R, M> Default for InMemoryTransport<P, R, M> {
    fn default() -> Self {
        Self {
            sent: Vec::new(),
            incoming: VecDeque::new(),
        }
    }
}

impl<P, R, M> InMemoryTransport<P, R, M> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_incoming(incoming: impl IntoIterator<Item = Envelope<P, R, M>>) -> Self {
        Self {
            sent: Vec::new(),
            incoming: incoming.into_iter().collect(),
        }
    }

    pub fn push_incoming(&mut self, env: Envelope<P, R, M>) {
        self.incoming.push_back(env);
    }

    pub fn extend_incoming(&mut self, envs: impl IntoIterator<Item = Envelope<P, R, M>>) {
        self.incoming.extend(envs);
    }

    pub fn sent(&self) -> &[Envelope<P, R, M>] {
        &self.sent
    }

    pub fn incoming(&self) -> &VecDeque<Envelope<P, R, M>> {
        &self.incoming
    }

    pub fn take_sent(&mut self) -> Vec<Envelope<P, R, M>> {
        std::mem::take(&mut self.sent)
    }
}

impl<P, R, M> Transport<P, R, M> for InMemoryTransport<P, R, M> {
    type Error = Infallible;

    fn send_envelope(&mut self, env: Envelope<P, R, M>) -> Result<(), Self::Error> {
        self.sent.push(env);
        Ok(())
    }

    fn recv_envelope(&mut self) -> Result<Option<Envelope<P, R, M>>, Self::Error> {
        Ok(self.incoming.pop_front())
    }
}

pub trait Communication<M> {
    type Peer: Clone + Ord + Eq;
    type Round: Round;
    type Error;

    fn peer_id(&self) -> &Self::Peer;
    fn round(&self) -> &Self::Round;
    fn tick(&mut self);

    /// Stamp an outgoing payload with the current local round.
    fn send(&mut self, msg: M) -> Result<(), Self::Error>;

    /// Receive the first envelope whose round is accepted.
    /// Rejected envelopes are dropped.
    fn recv_filtered<P>(
        &mut self,
        predicate: P,
    ) -> Result<Option<Received<Self::Peer, Self::Round, M>>, Self::Error>
    where
        P: FnMut(&Self::Round, &Self::Round) -> bool;
}

pub struct Process<P, R, T> {
    peer_id: P,
    round: R,
    transport: T,
}

impl<P, R, T> Process<P, R, T> {
    pub fn new(peer_id: P, round: R, transport: T) -> Self {
        Self {
            peer_id,
            round,
            transport,
        }
    }

    pub fn into_parts(self) -> (P, R, T) {
        (self.peer_id, self.round, self.transport)
    }

    pub fn transport(&self) -> &T {
        &self.transport
    }

    pub fn transport_mut(&mut self) -> &mut T {
        &mut self.transport
    }
}

impl<P, R, M, T> Communication<M> for Process<P, R, T>
where
    P: Clone + Ord + Eq,
    R: Round,
    T: Transport<P, R, M>,
{
    type Peer = P;
    type Round = R;
    type Error = T::Error;

    fn peer_id(&self) -> &Self::Peer {
        &self.peer_id
    }

    fn round(&self) -> &Self::Round {
        &self.round
    }

    fn tick(&mut self) {
        self.round.tick();
    }

    fn send(&mut self, msg: M) -> Result<(), Self::Error> {
        let env = Envelope {
            from: self.peer_id.clone(),
            round: self.round.clone(),
            payload: msg,
        };
        self.transport.send_envelope(env)
    }

    fn recv_filtered<PRED>(
        &mut self,
        mut predicate: PRED,
    ) -> Result<Option<Received<Self::Peer, Self::Round, M>>, Self::Error>
    where
        PRED: FnMut(&Self::Round, &Self::Round) -> bool,
    {
        loop {
            match self.transport.recv_envelope()? {
                None => return Ok(None),
                Some(env) => {
                    if predicate(&self.round, &env.round) {
                        return Ok(Some(Received {
                            from: env.from,
                            round: env.round,
                            payload: env.payload,
                        }));
                    }
                    // NOTE: Non-matching envelopes are silently dropped.
                    // This includes future-round messages that arrive early.
                    //
                    // In Leslie's HO model, messages from the wrong round
                    // simply don't appear — they are never delivered. Here,
                    // they are consumed from the transport and discarded.
                    // This is more lossy than necessary: a future-round
                    // message could be buffered and delivered when the
                    // receiver advances to that round.
                    //
                    // For safety proofs this is fine — Leslie's model
                    // already accounts for arbitrary message loss. For
                    // liveness, a real implementation would want to buffer
                    // future-round messages rather than drop them. This is
                    // a transport-layer concern, not a protocol concern.
                    //
                    // TODO: Consider a buffering transport that holds
                    // future-round messages and re-delivers them when the
                    // receiver's round advances.
                }
            }
        }
    }
}

pub trait InboxExt<M>: Communication<M> {
    /// Gather accepted messages into a peer-indexed inbox.
    ///
    /// - `round_pred(local, remote)` decides whether a message's round is accepted.
    /// - `done(&acc)` decides when enough messages have been gathered.
    ///
    /// At most one message per peer is retained; newer messages overwrite older ones.
    /// Once `done` holds, the function returns immediately and may miss additional
    /// matching messages still waiting in the transport.
    fn inbox<RP, DONE>(
        &mut self,
        round_pred: RP,
        done: DONE,
    ) -> Result<Inbox<Self::Peer, M>, Self::Error>
    where
        Self: Sized,
        RP: FnMut(&Self::Round, &Self::Round) -> bool,
        DONE: FnMut(&Inbox<Self::Peer, M>) -> bool;
}

impl<C, M> InboxExt<M> for C
where
    C: Communication<M>,
{
    fn inbox<RP, DONE>(
        &mut self,
        mut round_pred: RP,
        mut done: DONE,
    ) -> Result<Inbox<Self::Peer, M>, Self::Error>
    where
        Self: Sized,
        RP: FnMut(&Self::Round, &Self::Round) -> bool,
        DONE: FnMut(&Inbox<Self::Peer, M>) -> bool,
    {
        let mut acc = Inbox::new();

        while !done(&acc) {
            match self.recv_filtered(|local, remote| round_pred(local, remote))? {
                None => break,
                Some(received) => {
                    acc.insert(received.from, received.payload);
                }
            }
        }

        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Round for u64 {
        fn tick_impl(&mut self) {
            *self += 1;
        }
    }

    #[test]
    fn send_stamps_with_current_round() {
        let transport = InMemoryTransport::<u8, u64, &'static str>::default();
        let mut process = Process::new(7, 3_u64, transport);
        process.send("hello").unwrap();
        let (_, _, transport) = process.into_parts();
        assert_eq!(transport.sent().len(), 1);
        assert_eq!(transport.sent()[0].from, 7);
        assert_eq!(transport.sent()[0].round, 3);
        assert_eq!(transport.sent()[0].payload, "hello");
    }

    #[test]
    fn inbox_filters_by_round_and_overwrites_by_peer() {
        let mut transport = InMemoryTransport::<u8, u64, &'static str>::default();
        transport.push_incoming(Envelope {
            from: 1,
            round: 1,
            payload: "old-round",
        });
        transport.push_incoming(Envelope {
            from: 2,
            round: 2,
            payload: "first",
        });
        transport.push_incoming(Envelope {
            from: 2,
            round: 2,
            payload: "second",
        });
        transport.push_incoming(Envelope {
            from: 3,
            round: 2,
            payload: "third",
        });

        let mut process = Process::new(0, 2_u64, transport);
        let inbox = process
            .inbox(|local, remote| local == remote, |acc| acc.len() >= 2)
            .unwrap();

        assert_eq!(inbox.len(), 2);
        assert_eq!(inbox.get(&2), Some(&"second"));
        assert_eq!(inbox.get(&3), Some(&"third"));
    }

    #[test]
    fn in_memory_transport_supports_preloaded_incoming_and_take_sent() {
        let incoming = vec![
            Envelope {
                from: 10,
                round: 4_u64,
                payload: "a",
            },
            Envelope {
                from: 11,
                round: 4_u64,
                payload: "b",
            },
        ];
        let mut transport = InMemoryTransport::with_incoming(incoming);

        let first = transport.recv_envelope().unwrap().unwrap();
        assert_eq!(first.from, 10);
        assert_eq!(transport.incoming().len(), 1);

        transport
            .send_envelope(Envelope {
                from: 1,
                round: 9_u64,
                payload: "sent",
            })
            .unwrap();
        let sent = transport.take_sent();
        assert_eq!(sent.len(), 1);
        assert_eq!(sent[0].payload, "sent");
        assert!(transport.sent().is_empty());
    }

    #[test]
    fn ballot_phase_orders_lexicographically() {
        let p10 = BallotPhase::new(1, 0, 4);
        let p11 = BallotPhase::new(1, 1, 4);
        let p20 = BallotPhase::new(2, 0, 4);

        assert!(p10 < p11);
        assert!(p11 < p20);
        assert!(p10 < p20);
    }

    #[test]
    fn ballot_phase_tick_advances_phase_then_ballot() {
        let mut r = BallotPhase::new(7, 0, 3);
        r.tick();
        assert_eq!(r, BallotPhase::new(7, 1, 3));

        r.tick();
        assert_eq!(r, BallotPhase::new(7, 2, 3));

        r.tick();
        assert_eq!(r, BallotPhase::new(8, 0, 3));
    }

    #[test]
    fn peer_id_wraps_an_abstract_identifier() {
        let peer = PeerId::new("10.0.0.1:7000".to_owned());
        assert_eq!(peer.as_inner(), "10.0.0.1:7000");
        assert_eq!(peer.into_inner(), "10.0.0.1:7000".to_owned());
    }
}
