use std::{
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use differential_dataflow::{
    input::InputSession,
    operators::{arrange::ArrangeBySelf, Threshold},
    trace::{Cursor, TraceReader},
    Collection, Data, ExchangeData, Hashable, IntoOwned,
};
use flume::{Receiver, RecvError, Sender, TryRecvError};
use serde::{Deserialize, Serialize};
use timely::{
    communication::Allocator,
    dataflow::{operators::Probe, ProbeHandle, Scope},
    progress::frontier::AntichainRef,
    worker::Worker,
};

pub type Time = i64;
pub type Diff = isize;

pub fn run_pumps(
    worker: &mut Worker<Allocator>,
    handle: tokio::runtime::Handle,
    mut input: impl PumpInput,
    mut output: impl PumpOutput,
) {
    if worker.index() != 0 {
        todo!("unable to multithread dataflows right now");
    }

    // begin the event loop
    let mut time = 0;
    let mut behind = false;
    input.advance_to(time);

    loop {
        // if there's a flush pending, advance dataflow
        if input.take_flush() {
            time += 1;
            input.advance_to(time);
            behind = true;
        }

        // drain any pending updates
        match input.try_recv() {
            Some(true) => continue, // event processed, check for flush
            Some(false) => break,   // sink disconnected, abort
            None => {}              // no pending events, continue
        }

        // if output is behind input, poll dataflow step
        if behind {
            if output.is_pending(&time) {
                // step worker and poll for new inputs immediately
                worker.step();
                continue;
            } else {
                behind = false;
                output.flush();
                output.advance_to(time);
            }
        }

        // otherwise wait for new input
        match handle.block_on(input.recv()) {
            true => continue, // update received, handle events
            false => break,   // source disconnected, abort
        }
    }
}

#[derive(Clone)]
pub struct InputRouter<T: Data> {
    tx: Sender<Update<T>>,
    rx: Receiver<Update<T>>,
}

impl<T: Data> Default for InputRouter<T> {
    fn default() -> Self {
        let (tx, rx) = flume::unbounded();
        Self { tx, rx }
    }
}

impl<T: Data> InputRouter<T> {
    pub fn add_sink(&self) -> InputSink<T> {
        InputSink {
            rx: self.rx.clone(),
            input: InputSession::new(),
            flush: false,
        }
    }

    pub fn into_source(self) -> InputSource<T> {
        InputSource {
            tx: self.tx,
            items: HashSet::new(),
        }
    }
}

#[allow(async_fn_in_trait)]
pub trait PumpInput: Sized {
    async fn recv(&mut self) -> bool;

    fn try_recv(&mut self) -> Option<bool>;

    fn take_flush(&mut self) -> bool;

    fn advance_to(&mut self, time: Time);

    fn and<O>(self, other: O) -> (Self, O) {
        (self, other)
    }
}

impl<L: PumpInput, R: PumpInput> PumpInput for (L, R) {
    async fn recv(&mut self) -> bool {
        use futures_util::future::{select, Either};
        let left = Box::pin(self.0.recv());
        let right = Box::pin(self.1.recv());
        match select(left, right).await {
            Either::Left((result, _fut)) => result,
            Either::Right((result, _fut)) => result,
        }
    }

    fn try_recv(&mut self) -> Option<bool> {
        self.0.try_recv().or_else(|| self.1.try_recv())
    }

    fn take_flush(&mut self) -> bool {
        self.0.take_flush() || self.1.take_flush()
    }

    fn advance_to(&mut self, time: Time) {
        self.0.advance_to(time);
        self.1.advance_to(time);
    }
}

pub struct InputSink<T: Data> {
    rx: Receiver<Update<T>>,
    input: InputSession<Time, T, Diff>,
    flush: bool,
}

impl<T: Data> InputSink<T> {
    pub fn to_collection<G>(&mut self, scope: &mut G) -> Collection<G, T, Diff>
    where
        G: Scope<Timestamp = Time>,
    {
        self.input.to_collection(scope)
    }
}

impl<T: Data> PumpInput for InputSink<T> {
    async fn recv(&mut self) -> bool {
        match self.rx.recv_async().await {
            Err(RecvError::Disconnected) => false,
            Ok(Update::Flush) => {
                self.flush = true;
                true
            }
            Ok(Update::Push(item, add)) => {
                let delta = if add { 1 } else { -1 };
                self.input.update(item, delta);
                true
            }
        }
    }

    fn try_recv(&mut self) -> Option<bool> {
        match self.rx.try_recv() {
            Err(TryRecvError::Empty) => None,
            Err(TryRecvError::Disconnected) => Some(false),
            Ok(Update::Flush) => {
                self.flush = true;
                Some(true)
            }
            Ok(Update::Push(item, add)) => {
                let delta = if add { 1 } else { -1 };
                self.input.update(item, delta);
                Some(true)
            }
        }
    }

    fn take_flush(&mut self) -> bool {
        std::mem::take(&mut self.flush)
    }

    fn advance_to(&mut self, time: Time) {
        self.input.advance_to(time);
        self.input.flush();
    }
}

pub struct InputSource<T> {
    tx: Sender<Update<T>>,
    items: HashSet<T>,
}

impl<T> Drop for InputSource<T> {
    fn drop(&mut self) {
        let mut any = false;
        for item in self.items.drain() {
            let _ = self.tx.send(Update::Push(item, false));
            any = true;
        }

        if any {
            let _ = self.tx.send(Update::Flush);
        }
    }
}

impl<T: Clone + Eq + Hash> InputSource<T> {
    pub fn add_source(&self) -> Self {
        Self {
            tx: self.tx.clone(),
            items: HashSet::new(),
        }
    }

    pub fn insert(&mut self, item: T) -> bool {
        if self.items.insert(item.clone()) {
            let _ = self.tx.send(Update::Push(item, true));
            true
        } else {
            false
        }
    }

    pub fn remove(&mut self, item: T) -> bool {
        if self.items.remove(&item) {
            let _ = self.tx.send(Update::Push(item, false));
            true
        } else {
            false
        }
    }

    pub fn flush(&self) {
        let _ = self.tx.send(Update::Flush);
    }
}

/// A trait for objects that facilitate pumping outputs of dataflows to external
/// systems.
pub trait PumpOutput: Sized {
    fn advance_to(&mut self, time: Time);

    fn is_pending(&self, time: &Time) -> bool;

    fn flush(&mut self);

    /// Shorthand helper to combine this pump output with another.
    fn and<O>(self, other: O) -> (Self, O) {
        (self, other)
    }
}

impl<L: PumpOutput, R: PumpOutput> PumpOutput for (L, R) {
    fn advance_to(&mut self, time: Time) {
        self.0.advance_to(time);
        self.1.advance_to(time);
    }

    fn is_pending(&self, time: &Time) -> bool {
        self.0.is_pending(time) || self.1.is_pending(time)
    }

    fn flush(&mut self) {
        self.0.flush();
        self.1.flush();
    }
}

#[derive(Clone)]
pub struct OutputRouter<T> {
    tx: Sender<Update<T>>,
    rx: Receiver<Update<T>>,
}

impl<T> Default for OutputRouter<T> {
    fn default() -> Self {
        let (tx, rx) = flume::unbounded();
        Self { tx, rx }
    }
}

impl<T: ExchangeData + Hashable> OutputRouter<T> {
    /// Adds an [OutputSource] to pump the outputs of some collection to an
    /// external system.
    pub fn add_source<G>(&self, collection: &Collection<G, T>) -> OutputSource<T>
    where
        G: Scope<Timestamp = Time>,
    {
        let arranged = collection.distinct().arrange_by_self();

        OutputSource {
            tx: self.tx.clone(),
            probe: arranged.stream.probe(),
            trace: Box::new(TraceWrapper(arranged.trace, PhantomData)),
        }
    }
}

impl<T> OutputRouter<T> {
    /// Finish processing this output router and create a sink to receive its outputs.
    pub fn into_sink(self) -> OutputSink<T> {
        OutputSink {
            rx: self.rx,
            checked_in: 0,
            backlog: vec![],
        }
    }
}

/// Shorthand type to define the type of DD trace updates.
type TraceUpdates<T> = Vec<((T, ()), Vec<(Time, Diff)>)>;

/// Object-safe encapsulation for a trace reader (which typically have really
/// long and complicated type names).
trait DynTrace<T> {
    fn advance_to(&mut self, time: Time);
    fn updates(&mut self) -> TraceUpdates<T>;
}

struct TraceWrapper<T, Tr>(Tr, PhantomData<T>);

impl<T, Tr> DynTrace<T> for TraceWrapper<T, Tr>
where
    Tr: TraceReader<Time = Time, Diff = Diff>,
    for<'a> Tr::Key<'a>: IntoOwned<'a, Owned = T>,
    for<'a> Tr::Val<'a>: IntoOwned<'a, Owned = ()>,
{
    fn advance_to(&mut self, time: Time) {
        let frontier = [time];
        let frontier = AntichainRef::new(&frontier);
        self.0.set_physical_compaction(frontier);
        self.0.set_logical_compaction(frontier);
    }

    fn updates(&mut self) -> TraceUpdates<T> {
        let (mut cursor, storage) = self.0.cursor();
        cursor.to_vec(&storage)
    }
}

pub struct OutputSource<T> {
    tx: Sender<Update<T>>,
    probe: ProbeHandle<Time>,
    trace: Box<dyn DynTrace<T>>,
}

impl<T> PumpOutput for OutputSource<T> {
    fn advance_to(&mut self, time: Time) {
        self.trace.advance_to(time);
    }

    fn is_pending(&self, time: &Time) -> bool {
        self.probe.less_than(time)
    }

    fn flush(&mut self) {
        for ((item, ()), sums) in self.trace.updates() {
            let delta: isize = sums.iter().map(|(_time, sum)| *sum).sum();
            let add = delta > 0;
            let update = Update::Push(item, add);
            let _ = self.tx.send(update);
        }

        let _ = self.tx.send(Update::Flush);
    }
}

/// A receiver for items outputted by a dataflow.
pub struct OutputSink<T> {
    rx: Receiver<Update<T>>,
    checked_in: usize,
    backlog: Vec<(T, bool)>,
}

impl<T: Debug> OutputSink<T> {
    /// Receives a single batch of dataflow output updates.
    ///
    /// Cancel-safe.
    pub async fn next_batch(&mut self) -> Option<Vec<(T, bool)>> {
        // adjust by one because each output router (and its update sender) is
        // held by the worker constructor until worker terminates
        while self.checked_in < self.rx.sender_count() - 1 {
            let msg = self.rx.recv_async().await.ok()?;
            match msg {
                Update::Push(item, add) => self.backlog.push((item, add)),
                Update::Flush => self.checked_in += 1,
            }
        }

        self.checked_in = 0;
        Some(std::mem::take(&mut self.backlog))
    }
}

/// Represents to an update (add/remove) to a collection of items.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Update<T> {
    /// The item has been added (true) or removed (false).
    Push(T, bool),

    /// All pending items for a timestep have been updated.
    Flush,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
pub struct Key<T>(u64, PhantomData<T>);

impl<T> Copy for Key<T> {}

impl<T> Clone for Key<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Hash for Key<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0);
    }
}

impl<T: Hashable<Output = u64>> Key<T> {
    pub fn new(data: &T) -> Self {
        Key(data.hashed(), PhantomData)
    }

    pub fn pair(data: T) -> (Self, T) {
        (Self::new(&data), data)
    }
}

pub fn key<K, V>((k, _v): (K, V)) -> K {
    k
}

pub fn value<K, V>((_k, v): (K, V)) -> V {
    v
}

pub fn swap<K, V>((k, v): (K, V)) -> (V, K) {
    (v, k)
}

pub fn map_value<K, I, O>(
    mut cb: impl FnMut(I) -> Option<O>,
) -> impl FnMut((K, I)) -> Option<(K, O)> {
    move |(k, v)| cb(v).map(|v| (k, v))
}
