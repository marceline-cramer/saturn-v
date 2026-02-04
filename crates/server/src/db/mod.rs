// Copyright (C) 2025-2026 Marceline Cramer
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
    collections::BTreeMap,
    future::Future,
    hash::{DefaultHasher, Hash, Hasher},
    path::Path,
};

use anyhow::Context;
use fjall::*;
use saturn_v_eval::{
    load::Loader,
    types::{Fact, Relation},
    utils::Key as DataflowKey,
    InputEvent, InputEventKind,
};
use saturn_v_protocol::{ir::RelationIO, *};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use tracing::error;

#[cfg(test)]
mod tests;

/// A transaction object for updating and querying the Saturn V server.
pub trait Transaction {
    /// Retrieves the currently running program.
    fn get_program(&mut self) -> ServerResult<Program>;

    /// Updates the currently-running program.
    fn set_program(&mut self, program: Program) -> ServerResult<()>;

    /// Clears the contents of a specific input.
    fn clear_input(&mut self, input: &str) -> ServerResult<()>;

    /// Updates the contents of a specific input. See [TupleUpdate].
    fn update_input(&mut self, input: &str, updates: &[TupleUpdate]) -> ServerResult<()>;

    /// Retrieves the set of values in an input relation.
    fn get_input_values(&mut self, input: &str) -> ServerResult<Vec<StructuredValue>>;

    /// Checks if an input contains certain values.
    ///
    /// The resulting list collates with input values.
    fn check_input_values(
        &mut self,
        input: &str,
        values: &[StructuredValue],
    ) -> ServerResult<Vec<bool>>;

    /// Drops this transaction and attempts to commit the changes.
    ///
    /// If this fails, all changes made during this transaction will be rolled back.
    ///
    /// Returns the sequence ID of the committed transaction.
    fn commit(self) -> impl Future<Output = ServerResult<SequenceId>> + Send;
}

/// Maintains atomic transactions on Saturn V state and inputs.
pub struct Database {
    db: OptimisticTxDatabase,
    keyspace: OptimisticTxKeyspace,
}

impl Database {
    /// Creates/opens a database at the given path.
    ///
    /// Returns [`anyhow`] errors because initialization should not present database errors to clients.
    pub fn new(path: impl AsRef<Path>) -> anyhow::Result<Self> {
        Self::new_inner(OptimisticTxDatabase::builder(path.as_ref()))
    }

    /// Creates a temporary database.
    pub fn temporary() -> anyhow::Result<Self> {
        let path = tempfile::TempDir::with_prefix("saturn-v-db_")
            .context("failed to create temporary directory")?
            .keep();

        Self::new_inner(OptimisticTxDatabase::builder(&path).temporary(true))
    }

    fn new_inner(builder: DatabaseBuilder<OptimisticTxDatabase>) -> anyhow::Result<Self> {
        // open the database using the provided builder and configuration
        let db = builder.open().context("failed to open keyspace")?;

        // create a keyspace for all transactions with default config
        let keyspace = db
            .keyspace("main", Default::default)
            .context("failed to create keyspace")?;

        // successful creation
        Ok(Self { db, keyspace })
    }

    /// Attempts to begin a transaction using this database.
    pub fn transaction<D: CommitDataflow>(&self, dataflow: D) -> ServerResult<FjallTransaction<D>> {
        // begin a serializable transaction
        let tx = self.db.write_tx().map_err(|err| {
            error!("failed to begin tx: {err:?}");
            ServerError::DatabaseError
        })?;

        // create transaction structure without input map
        let mut tx = FjallTransaction {
            tx,
            dataflow,
            key_buf: Vec::with_capacity(1024),
            keyspace: self.keyspace.clone(),
            program_map: Default::default(),
            events: Vec::with_capacity(128),
        };

        // populate program map
        tx.program_map = tx.get(&Key::ProgramMap)?.unwrap_or_default();

        // done!
        Ok(tx)
    }
}

pub struct FjallTransaction<D> {
    tx: OptimisticWriteTx,
    keyspace: OptimisticTxKeyspace,

    /// Reusable buffer for quickly serializing database keys.
    key_buf: Vec<u8>,

    /// Cache [ProgramMap] to avoid ser/de and DB overhead.
    program_map: ProgramMap,

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
            .get::<Loader<String>>(&Key::Loader)?
            .unwrap_or_default();

        // remove old program from dataflow
        self.events
            .extend(old_loader.get_events().map(InputEvent::Remove));

        // load the program
        let loader = Loader::load_program(&program);

        // add new program to dataflow
        self.events
            .extend(loader.get_events().map(InputEvent::Insert));

        // wipe old input relations
        // TODO: reuse inputs when possible
        for name in self.program_map.input_relations.clone().into_keys() {
            self.clear_input(&name)?;
        }

        // create new program map
        let mut new_program = ProgramMap::default();

        // allocate relations
        for (name, rel) in loader.get_relations().iter() {
            // handle relations on a case-by-case
            match rel.io {
                // rest of loop is dedicated to input adding
                RelationIO::Input => {}
                // skip handling internal relations
                RelationIO::None => {}
                // add output relation to map
                RelationIO::Output => {
                    // create output info
                    let info = OutputRelation {
                        name: name.clone(),
                        id: name.clone(),
                        ty: rel.ty.clone(),
                        key: DataflowKey::new(rel),
                    };

                    // insert output relation
                    new_program.output_relations.insert(name.clone(), info);

                    // skip input relation handling
                    continue;
                }
            }

            // allocate input index
            let index = new_program
                .input_relations
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
            new_program.input_relations.insert(name.clone(), info);
        }

        // insert program map into DB
        self.insert(&Key::ProgramMap, &new_program)?;

        // add loader to DB
        self.insert(&Key::Loader, &loader)?;

        // cache program map
        self.program_map = new_program;

        // set the program itself
        self.insert(&Key::Program, &program)?;

        // success!
        Ok(())
    }

    fn clear_input(&mut self, input: &str) -> ServerResult<()> {
        // construct prefix from key
        let input = self.get_input(input)?;
        let key = Key::Input { input: input.index };
        let prefix = key.as_path(&mut self.key_buf);

        // fetch all items (cannot reborrow for remove)
        let items: Vec<_> = self
            .tx
            .prefix(&self.keyspace, prefix)
            .map(|kv| kv.into_inner())
            .collect();

        // delete the whole prefix
        for item in items {
            // handle database error and extract key-value
            let (key, val) = item.map_err(db_error)?;

            // deserialize bucket
            let bucket: Bucket = serde_json::from_slice(&val).map_err(db_error)?;

            // remove each entry in the bucket from dataflow
            for item in bucket {
                let fact = input.make_fact(item)?;
                let ev = InputEvent::Remove(InputEventKind::Fact(fact));
                self.events.push(ev);
            }

            // delete entry
            self.tx.remove(&self.keyspace, key.as_ref());
        }

        // success!
        Ok(())
    }

    fn update_input(&mut self, input: &str, updates: &[TupleUpdate]) -> ServerResult<()> {
        let input = self.get_input(input)?;

        for TupleUpdate { state, value } in updates.iter().cloned() {
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

    fn get_input_values(&mut self, input: &str) -> ServerResult<Vec<StructuredValue>> {
        // construct prefix from key
        let input = self.get_input(input)?;
        let key = Key::Input { input: input.index };
        let prefix = key.as_path(&mut self.key_buf);

        // fetch all items (cannot reborrow for remove)
        let items: Vec<_> = self
            .tx
            .prefix(&self.keyspace, prefix)
            .map(|kv| kv.into_inner())
            .collect();

        // gather values from all buckets
        let mut values = Vec::new();
        for item in items {
            // handle database error and extract key-value
            let (_key, val) = item.map_err(db_error)?;

            // deserialize bucket
            let bucket: Bucket = serde_json::from_slice(&val).map_err(db_error)?;

            // add bucket contents
            values.extend(bucket);
        }

        // success!
        Ok(values)
    }

    fn check_input_values(
        &mut self,
        input: &str,
        values: &[StructuredValue],
    ) -> ServerResult<Vec<bool>> {
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

    async fn commit(mut self) -> ServerResult<SequenceId> {
        // perform actual commit
        // first error is IO, second error is SSI conflict
        self.tx
            .commit()
            .map_err(db_error)?
            .map_err(|_| ServerError::Conflict)?;

        // send dataflow inputs
        let sequence = self.dataflow.commit(self.program_map, self.events).await;

        // done!
        Ok(sequence)
    }
}

impl<D: CommitDataflow> FjallTransaction<D> {
    pub fn get_raw(&mut self, key: &Key) -> ServerResult<Option<UserValue>> {
        // construct path from key and borrow inner buffer
        let path = key.as_path(&mut self.key_buf);

        // perform the actual get operation
        self.tx.get(&self.keyspace, path).map_err(db_error)
    }

    pub fn get<T: DeserializeOwned>(&mut self, key: &Key) -> ServerResult<Option<T>> {
        self.get_raw(key)?
            .map(|value| serde_json::from_slice(&value).map_err(db_error))
            .transpose()
    }

    pub fn insert_raw(&mut self, key: &Key, value: &[u8]) {
        // construct path from key and borrow inner buffer
        let path = key.as_path(&mut self.key_buf);

        // perform the actual insertion operation
        self.tx.insert(&self.keyspace, path.as_ref(), value);
    }

    pub fn insert<T: Serialize>(&mut self, key: &Key, value: &T) -> ServerResult<()> {
        let data = serde_json::to_vec(value).map_err(db_error)?;
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
            .fetch_update(&self.keyspace, path.as_ref(), f)
            .map_err(db_error)
    }

    pub fn fetch_update<T: DeserializeOwned + Serialize>(
        &mut self,
        key: &Key,
        mut f: impl FnMut(Option<&T>) -> Option<T>,
    ) -> ServerResult<()> {
        // wrap raw fetch-update operation into fallible ser/de operations
        let mut err = None;
        self.fetch_update_raw(key, |data| {
            // deserialize data if present
            let input = match data.map(|data| serde_json::from_slice(data)) {
                None => None,
                Some(Ok(value)) => Some(value),
                Some(Err(e)) => {
                    err = Some(e);
                    return data.map(ToOwned::to_owned);
                }
            };

            // call inner callback on typed data
            let output = f(input.as_ref());

            // serialize output if present
            match output.map(|output| serde_json::to_vec(&output)) {
                None => None,
                Some(Ok(output)) => Some(output.into()),
                Some(Err(e)) => {
                    err = Some(e);
                    data.map(ToOwned::to_owned)
                }
            }
        })?;

        // if there were any errors during serialization, return an error
        match err {
            Some(err) => Err(db_error(err)),
            None => Ok(()),
        }
    }

    /// Gets an input relation's info by name.
    pub fn get_input(&self, input: &str) -> ServerResult<InputRelation> {
        self.program_map
            .input_relations
            .get(input)
            .cloned()
            .ok_or(ServerError::NoSuchInput(input.to_string()))
    }

    /// Loads the current state of the database into the dataflow.
    pub(crate) fn load_dataflow(&mut self) -> ServerResult<()> {
        // load dataflow state from the loader
        if let Some(loader) = self.get::<Loader<String>>(&Key::Loader)? {
            let events = loader.get_events().map(InputEvent::Insert);
            self.events.extend(events);
        }

        // load each input relation
        for (name, input) in self.program_map.input_relations.clone() {
            // load each value in the input relation
            for val in self.get_input_values(&name)? {
                let fact = input.make_fact(val)?;
                let ev = InputEvent::Insert(InputEventKind::Fact(fact));
                self.events.push(ev);
            }
        }

        // done
        Ok(())
    }
}

/// A bucket (as in hash set) of values in a single database entry.
pub type Bucket = Vec<StructuredValue>;

/// Mappings between program information and database state.
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct ProgramMap {
    /// Maps input relation IDs to their information within the database.
    pub input_relations: BTreeMap<String, InputRelation>,

    /// Maps output relation IDs to their information within the database.
    pub output_relations: BTreeMap<String, OutputRelation>,
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

    /// Creates a dataflow [Fact] from a structured [StructuredValue] with error checking.
    pub fn make_fact(&self, value: StructuredValue) -> ServerResult<Fact> {
        // TODO: this allocates once for Vec and once for Arc; could be made faster (definitely hot path)
        let mut out = Vec::with_capacity(self.ty.size());
        Self::make_fact_inner(&mut out, &self.ty, value)?;
        Ok(Fact {
            relation: self.key,
            values: out.into(),
        })
    }

    /// Inner helper method to recursively flatten [StructuredValue].
    fn make_fact_inner(
        out: &mut Vec<ir::Value>,
        ty: &StructuredType,
        value: StructuredValue,
    ) -> ServerResult<()> {
        use ir::{Type::*, Value};
        use StructuredType::*;
        let ir_val = match (ty, value) {
            (Primitive(String), StructuredValue::String(val)) => Value::String(val),
            (Primitive(Boolean), StructuredValue::Boolean(val)) => Value::Boolean(val),
            (Primitive(Integer), StructuredValue::Integer(val)) => Value::Integer(val),
            (Primitive(Real), StructuredValue::Real(val)) => Value::Real(val),
            (Primitive(Symbol), StructuredValue::Symbol(val)) => Value::Symbol(val),
            (Tuple(tys), StructuredValue::Tuple(els)) => {
                return tys
                    .iter()
                    .zip(els)
                    .try_for_each(|(ty, el)| Self::make_fact_inner(out, ty, el));
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

/// Persistent information about an output relation.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct OutputRelation {
    /// The name of this input.
    pub name: String,

    /// The API ID of this input.
    pub id: String,

    /// The type of this input.
    pub ty: StructuredType,

    /// This relation's key within the dataflow.
    pub key: DataflowKey<Relation>,
}

impl OutputRelation {
    pub fn to_info(&self) -> RelationInfo {
        RelationInfo {
            name: self.name.clone(),
            id: self.id.clone(),
            ty: self.ty.clone(),
        }
    }
}

/// Helper enum for constructing paths in the database.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Key {
    Program,
    Loader,
    ProgramMap,
    Input { input: u16 },
    Bucket { input: u16, key: u16 },
}

impl Key {
    /// Creates a bucket key for the given input and value.
    pub fn bucket(input: u16, value: &StructuredValue) -> Self {
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
            Key::ProgramMap => b"m".into(),
            Key::Loader => b"l".into(),
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

/// A trait for ACID dataflow inputs. If dropped, changes must be rolled back.
pub trait CommitDataflow: Send + Sync {
    /// Atomically commits this dataflow update, returning a [SequenceId] to retrieve outputs.
    fn commit(
        &mut self,
        program_map: ProgramMap,
        events: Vec<InputEvent>,
    ) -> impl Future<Output = SequenceId> + Send;
}

impl<T: CommitDataflow> CommitDataflow for &mut T {
    fn commit(
        &mut self,
        program_map: ProgramMap,
        events: Vec<InputEvent>,
    ) -> impl Future<Output = SequenceId> + Send {
        (**self).commit(program_map, events)
    }
}

/// Helper function to log database errors while returning opaque [ServerError].
pub fn db_error<E: std::error::Error>(err: E) -> ServerError {
    tracing::error!("Database error: {}", err);
    ServerError::DatabaseError
}
