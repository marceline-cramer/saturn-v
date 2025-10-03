// Copyright (C) 2025 Marceline Cramer
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// Saturn V is free software: you can redistribute it and/or modify it under
// the terms of the GNU Affero General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// Saturn V is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for
// more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with Saturn V. If not, see <https://www.gnu.org/licenses/>.

use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, VecDeque},
    hash::{DefaultHasher, Hash, Hasher},
    path::Path,
};

use anyhow::Context;
use fjall::*;
use saturn_v_client::*;
use saturn_v_eval::{
    InputEvent, InputEventKind,
    load::Loader,
    types::{Fact, Relation},
    utils::Key as DataflowKey,
};
use saturn_v_ir::{self as ir, RelationIO};
use serde::{Deserialize, Serialize, de::DeserializeOwned};

/// A transaction object for updating and querying the Saturn V server.
pub trait Transaction {
    /// Retrieves the currently running program.
    fn get_program(&mut self) -> ServerResult<Program>;

    /// Updates the currently-running program.
    fn set_program(&mut self, program: Program) -> ServerResult<()>;

    /// Clears the contents of a specific input.
    fn clear(&mut self, input: &str) -> ServerResult<()>;

    /// Updates the contents of a specific input. See [TupleUpdate].
    fn update(&mut self, input: &str, updates: &[TupleUpdate]) -> ServerResult<()>;

    /// Checks if an input contains certain values.
    ///
    /// The resulting list collates with input values.
    fn get(&mut self, input: &str, values: &[Value]) -> ServerResult<Vec<bool>>;

    /// Drops this transaction and attempts to commit the changes.
    ///
    /// If this fails, all changes made during this transaction will be rolled back.
    ///
    /// Returns the sequence ID of the committed transaction.
    fn commit(self) -> ServerResult<SequenceId>;

    /// Gets the current input map.
    fn get_input_map(&self) -> ServerResult<InputMap>;
}

/// Maintains atomic transactions on Saturn V state and inputs.
///
/// Also facilitates consistent dataflow state and generates [SequenceId].
pub struct Database<D> {
    keyspace: TransactionalKeyspace,
    partition: TransactionalPartitionHandle,
    dataflow: D,
}

impl<D: CommitDataflow> Database<D> {
    /// Creates/opens a database at the given path.
    ///
    /// Returns [`anyhow`] errors because initialization should not present database errors to clients.
    pub fn new(dataflow: D, path: impl AsRef<Path>) -> anyhow::Result<Self> {
        Self::new_inner(dataflow, Config::new(path))
    }

    /// Creates a temporary database.
    pub fn temporary(dataflow: D) -> anyhow::Result<Self> {
        let path = tempfile::TempDir::with_prefix("saturn-v-db_")
            .context("failed to create temporary directory")?
            .keep();

        Self::new_inner(dataflow, Config::new(path).temporary(true))
    }

    fn new_inner(dataflow: D, config: Config) -> anyhow::Result<Self> {
        // open a keyspace using the provided config
        let keyspace = config
            .open_transactional()
            .context("failed to open keyspace")?;

        // create a partition for all transactions with default config
        let partition = keyspace
            .open_partition("main", Default::default())
            .context("failed to open partition")?;

        // successful creation
        Ok(Self {
            keyspace,
            partition,
            dataflow,
        })
    }

    /// Attempts to begin a transaction using this database.
    pub fn transaction(&self) -> ServerResult<FjallTransaction<D>> {
        // begin a serializable transaction
        let tx = self
            .keyspace
            .write_tx()
            .map_err(|_| ServerError::DatabaseError)?;

        // create transaction structure without input map
        let mut tx = FjallTransaction {
            tx,
            key_buf: Vec::with_capacity(1024),
            partition: self.partition.clone(),
            inputs: Default::default(),
            events: Vec::with_capacity(128),
            dataflow: self.dataflow.clone(),
        };

        // populate input map
        tx.inputs = tx.get(&Key::InputMap)?.unwrap_or_default();

        // done!
        Ok(tx)
    }
}

pub struct FjallTransaction<D> {
    tx: WriteTransaction,
    key_buf: Vec<u8>,
    partition: TransactionalPartitionHandle,

    /// Cache [InputMap] to avoid ser/de and DB overhead.
    inputs: InputMap,

    /// List of dataflow input events to commit.
    events: Vec<InputEvent>,

    /// A handle to the dataflow entrypoint to commit to.
    dataflow: D,
}

impl<D: CommitDataflow> Transaction for FjallTransaction<D> {
    fn get_program(&mut self) -> ServerResult<Program> {
        self.get(&Key::Program)
            .and_then(|program| program.ok_or(ServerError::NoProgramLoaded))
    }

    fn set_program(&mut self, program: Program) -> ServerResult<()> {
        // validate the program
        program.validate().map_err(ServerError::InvalidProgram)?;

        // retrieve old program as a loader (empty if none is set)
        let old_loader = self
            .get::<Program>(&Key::Program)?
            .map(|program| Loader::load_program(&program))
            .unwrap_or_default();

        // remove old program from dataflow
        self.events
            .extend(old_loader.get_events().map(InputEvent::Remove));

        // load the program
        let loader = Loader::load_program(&program);

        // add new program to dataflow
        self.events
            .extend(loader.get_events().map(InputEvent::Insert));

        // wipe old inputs
        // TODO: reuse inputs when possible
        for name in self.inputs.relations.clone().into_keys() {
            self.clear(&name)?;
        }

        // allocate new input relations
        let mut inputs = InputMap::default();
        for (name, rel) in loader.get_relations().iter() {
            // skip non-inputs
            if rel.io != RelationIO::Input {
                continue;
            }

            // allocate index
            let index = self
                .inputs
                .relations
                .len()
                .try_into()
                .expect("input index overflow");

            // construct input info
            let info = InputRelation {
                index,
                name: name.clone(),
                id: name.clone(),
                ty: rel.ty.clone(),
                key: DataflowKey::new(rel),
            };

            // insert into our inputs
            inputs.relations.insert(name.clone(), info);
        }

        // insert input map into DB
        self.insert(&Key::InputMap, &inputs)?;

        // cache input map
        self.inputs = inputs;

        // set the program itself
        self.insert(&Key::Program, &program)?;

        // success!
        Ok(())
    }

    fn clear(&mut self, input: &str) -> ServerResult<()> {
        // construct prefix from key
        let input = self.get_input(input)?;
        let key = Key::Input { input: input.index };
        let prefix = key.as_path(&mut self.key_buf);

        // fetch all items (cannot reborrow for remove)
        let items: Vec<_> = self.tx.prefix(&self.partition, prefix).collect();

        // delete the whole prefix
        for item in items {
            // handle database error and extract key-value
            let (key, val) = item.map_err(|_| ServerError::DatabaseError)?;

            // deserialize bucket
            let bucket: Bucket =
                serde_json::from_slice(&val).map_err(|_| ServerError::DatabaseError)?;

            // remove each entry in the bucket from dataflow
            for item in bucket {
                let fact = input.make_fact(item)?;
                let ev = InputEvent::Remove(InputEventKind::Fact(fact));
                self.events.push(ev);
            }

            // delete entry
            self.tx.remove(&self.partition, key.as_ref());
        }

        // success!
        Ok(())
    }

    fn update(&mut self, input: &str, updates: &[TupleUpdate]) -> ServerResult<()> {
        let input = self.get_input(input)?;

        for TupleUpdate { state, value } in updates.to_vec() {
            // construct fact for dataflow input and type-check value
            let fact = input.make_fact(value.clone())?;

            // prepare potential input event after db update
            let ev_kind = InputEventKind::Fact(fact);
            let mut ev = None;

            // update bucket within db
            let bucket = Key::bucket(input.index, &value);
            self.fetch_update(&bucket, |old: Option<&Bucket>| {
                let mut bucket = old.map(ToOwned::to_owned).unwrap_or_default();

                let idx = bucket
                    .iter()
                    .enumerate()
                    .find(|(_idx, v)| v == &&value)
                    .map(|(idx, _v)| idx);

                match (state, idx) {
                    (false, Some(idx)) => {
                        bucket.remove(idx);
                        ev = Some(InputEvent::Remove(ev_kind.clone()));
                    }
                    (true, None) => {
                        bucket.push(value.clone());
                        ev = Some(InputEvent::Insert(ev_kind.clone()));
                    }
                    _ => {}
                }

                if bucket.is_empty() {
                    None
                } else {
                    Some(bucket)
                }
            })?;

            // send dataflow input event (if there was one)
            self.events.extend(ev);
        }

        Ok(())
    }

    fn get(&mut self, input: &str, values: &[Value]) -> ServerResult<Vec<bool>> {
        // TODO: validate value types
        let input_idx = self.get_input(input)?.index;
        let mut results = Vec::with_capacity(values.len());
        for value in values.iter() {
            results.push(
                self.get(&Key::bucket(input_idx, value))?
                    .map(|bucket: Bucket| bucket.contains(value))
                    .unwrap_or(false),
            );
        }

        Ok(results)
    }

    fn commit(mut self) -> ServerResult<SequenceId> {
        // perform actual commit
        // first error is IO, second error is SSI conflict
        self.tx
            .commit()
            .map_err(|_| ServerError::DatabaseError)?
            .map_err(|_| ServerError::Conflict)?;

        // send dataflow inputs
        let sequence = self.dataflow.commit(self.events);

        // done!
        Ok(sequence)
    }

    fn get_input_map(&self) -> ServerResult<InputMap> {
        Ok(self.inputs.clone())
    }
}

impl<D: CommitDataflow> FjallTransaction<D> {
    pub fn get_raw(&mut self, key: &Key) -> ServerResult<Option<UserValue>> {
        // construct path from key and borrow inner buffer
        let path = key.as_path(&mut self.key_buf);

        // perform the actual get operation
        self.tx
            .get(&self.partition, path)
            .map_err(|_| ServerError::DatabaseError)
    }

    pub fn get<T: DeserializeOwned>(&mut self, key: &Key) -> ServerResult<Option<T>> {
        self.get_raw(key)?
            .map(|value| serde_json::from_slice(&value).map_err(|_| ServerError::DatabaseError))
            .transpose()
    }

    pub fn insert_raw(&mut self, key: &Key, value: &[u8]) {
        // construct path from key and borrow inner buffer
        let path = key.as_path(&mut self.key_buf);

        // perform the actual insertion operation
        self.tx.insert(&self.partition, path.as_ref(), value);
    }

    pub fn insert<T: Serialize>(&mut self, key: &Key, value: &T) -> ServerResult<()> {
        let data = serde_json::to_vec(value).map_err(|_| ServerError::DatabaseError)?;
        self.insert_raw(key, data.as_slice());
        Ok(())
    }

    pub fn fetch_update_raw(
        &mut self,
        key: &Key,
        f: impl FnMut(Option<&UserValue>) -> Option<UserValue>,
    ) -> ServerResult<Option<UserValue>> {
        // construct path from key and borrow inner buffer
        let path = key.as_path(&mut self.key_buf);

        // perform the actual fetch-update operation
        self.tx
            .fetch_update(&self.partition, path.as_ref(), f)
            .map_err(|_| ServerError::DatabaseError)
    }

    pub fn fetch_update<T: DeserializeOwned + Serialize>(
        &mut self,
        key: &Key,
        mut f: impl FnMut(Option<&T>) -> Option<T>,
    ) -> ServerResult<()> {
        // wrap raw fetch-update operation into fallible ser/de operations
        let mut err = false;
        self.fetch_update_raw(key, |data| {
            // deserialize data if present
            let input = match data.map(|data| serde_json::from_slice(data)) {
                None => None,
                Some(Ok(value)) => Some(value),
                Some(Err(_)) => {
                    err = true;
                    return data.map(ToOwned::to_owned);
                }
            };

            // call inner callback on typed data
            let output = f(input.as_ref());

            // serialize output if present
            match output.map(|output| serde_json::to_vec(&output)) {
                None => None,
                Some(Ok(output)) => Some(output.into()),
                Some(Err(_)) => {
                    err = true;
                    data.map(ToOwned::to_owned)
                }
            }
        })?;

        // if there were any errors during serialization, return an error
        match err {
            false => Err(ServerError::DatabaseError),
            true => Ok(()),
        }
    }

    /// Gets an input relation's info by name.
    pub fn get_input(&self, input: &str) -> ServerResult<InputRelation> {
        self.inputs
            .relations
            .get(input)
            .cloned()
            .ok_or(ServerError::NoSuchInput(input.to_string()))
    }
}

/// A bucket (as in hash set) of values in a single database entry.
pub type Bucket = Vec<Value>;

/// Mappings between program relations and input indices.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct InputMap {
    pub relations: BTreeMap<String, InputRelation>,
}

/// Persistent information about an input relation.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct InputRelation {
    /// A database-local index for this input.
    pub index: u16,

    /// The name of this input.
    pub name: String,

    /// The API ID of this input.
    pub id: String,

    /// The type of this input.
    pub ty: StructuredType,

    /// This relation's key within the dataflow.
    pub key: DataflowKey<Relation>,
}

impl InputRelation {
    pub fn to_info(&self) -> RelationInfo {
        RelationInfo {
            name: self.name.clone(),
            id: self.id.clone(),
            ty: self.ty.clone(),
        }
    }

    /// Creates a dataflow [Fact] from a structured [Value] with error checking.
    pub fn make_fact(&self, value: Value) -> ServerResult<Fact> {
        // TODO: this allocates once for Vec and once for Arc; could be made faster (definitely hot path)
        let mut out = Vec::with_capacity(self.ty.size());
        Self::make_fact_inner(&mut out, &self.ty, value)?;
        Ok(Fact {
            relation: self.key,
            values: out.into(),
        })
    }

    /// Inner helper method to recursively flatten [Value].
    fn make_fact_inner(
        out: &mut Vec<ir::Value>,
        ty: &StructuredType,
        value: Value,
    ) -> ServerResult<()> {
        use StructuredType::*;
        use ir::Type::*;
        let ir_val = match (ty, value) {
            (Primitive(String), Value::String(val)) => ir::Value::String(val),
            (Primitive(Boolean), Value::Boolean(val)) => ir::Value::Boolean(val),
            (Primitive(Integer), Value::Integer(val)) => ir::Value::Integer(val),
            (Primitive(Real), Value::Real(val)) => ir::Value::Real(val),
            (Primitive(Symbol), Value::Symbol(val)) => ir::Value::Symbol(val),
            (Tuple(tys), Value::Tuple(els)) => {
                return tys
                    .iter()
                    .zip(els)
                    .map(|(ty, el)| Self::make_fact_inner(out, ty, el))
                    .collect();
            }
            (expected, val) => {
                return Err(ServerError::TypeMismatch {
                    expected: expected.clone(),
                    got: val.ty(),
                });
            }
        };

        out.push(ir_val);
        Ok(())
    }
}

/// Helper enum for constructing paths in the database.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Key {
    Program,
    InputMap,
    Input { input: u16 },
    Bucket { input: u16, key: u16 },
}

impl Key {
    /// Creates a bucket key for the given input and value.
    pub fn bucket(input: u16, value: &Value) -> Self {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        Key::Bucket {
            input,
            // truncate hash to 16-bit for storage
            key: hasher.finish() as u16,
        }
    }

    /// Converts the key into a path for storage in the database.
    #[inline(always)]
    pub fn as_path(self, buf: &mut Vec<u8>) -> Cow<'_, [u8]> {
        match self {
            Key::Program => b"p".into(),
            Key::InputMap => b"m".into(),
            Key::Input { input } => {
                buf.clear();
                buf.push(b'i'); // input contents prefix
                buf.extend_from_slice(&input.to_le_bytes());
                Cow::Borrowed(buf.as_slice())
            }
            Key::Bucket { input, key } => {
                Key::Input { input }.as_path(buf);
                buf.extend_from_slice(&key.to_le_bytes());
                Cow::Borrowed(buf.as_slice())
            }
        }
    }
}

/// A trait for ACID dataflow inputs.
pub trait CommitDataflow: Clone {
    fn commit(&mut self, events: Vec<InputEvent>) -> SequenceId;
}

/// A mock implementation of CommitDataflow for testing purposes.
#[derive(Clone, Default)]
pub struct MockDataflow {
    sequence: u64,
    state: BTreeSet<InputEventKind>,
    events: VecDeque<Vec<InputEvent>>,
}

impl CommitDataflow for MockDataflow {
    fn commit(&mut self, events: Vec<InputEvent>) -> SequenceId {
        self.sequence += 1;
        self.events.push_front(events);
        SequenceId(self.sequence)
    }
}

impl MockDataflow {
    /// Pulls a batch of events from the mock dataflow and validates state.
    pub fn pull(&mut self) {
        // pull the batch
        let batch = self
            .events
            .pop_back()
            .expect("expected a next batch of events");

        // apply batch to state
        self.apply(batch);
    }

    /// Applies a batch of events to the mock dataflow and validates state.
    fn apply(&mut self, batch: Vec<InputEvent>) {
        for event in batch {
            use InputEvent::*;
            match event {
                Insert(kind) => {
                    let dup = self.state.insert(kind.clone());
                    assert!(!dup, "duplicate insert event: {kind:?}");
                }
                Remove(kind) => {
                    let had = self.state.remove(&kind);
                    assert!(had, "duplicate remove event: {kind:?}");
                }
            }
        }
    }

    /// Checks the current state of the mock dataflow.
    pub fn assert_state(&self, expected: impl IntoIterator<Item = InputEventKind>) {
        assert_eq!(self.state, BTreeSet::from_iter(expected));
    }

    /// Peeks the next batch.
    pub fn peek(&self) -> &Vec<InputEvent> {
        self.events.back().expect("expected a next batch of events")
    }

    /// Assert that input events have been removed in the next batch.
    pub fn assert_removed(&self, expected: impl IntoIterator<Item = InputEventKind>) {
        // pull removed events
        let got = self
            .peek()
            .iter()
            .cloned()
            .flat_map(InputEvent::remove)
            .collect::<BTreeSet<_>>();

        // assert match
        assert_eq!(got, BTreeSet::from_iter(expected));
    }

    /// Assert that input events have been inserted in the next batch.
    pub fn assert_inserted(&self, expected: impl IntoIterator<Item = InputEventKind>) {
        // pull inserted events
        let got = self
            .peek()
            .iter()
            .cloned()
            .flat_map(InputEvent::insert)
            .collect::<BTreeSet<_>>();

        // assert match
        assert_eq!(got, BTreeSet::from_iter(expected));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_tx() {
        let dataflow = MockDataflow::default();
        let db = Database::temporary(dataflow).unwrap();
        let _tx = db.transaction().unwrap();
    }
}
