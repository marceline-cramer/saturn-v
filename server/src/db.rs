use std::{
    borrow::Cow,
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    path::Path,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use anyhow::Context;
use fjall::*;
use saturn_v_client::*;
use saturn_v_ir::RelationIO;
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
}

/// Maintains atomic transactions on Saturn V state and inputs.
///
/// Also facilitates consistent dataflow state and generates [SequenceId].
pub struct Database {
    keyspace: TransactionalKeyspace,
    partition: TransactionalPartitionHandle,
    sequence: Arc<AtomicU64>,
}

impl Database {
    /// Creates/opens a database at the given path.
    ///
    /// Returns [`anyhow`] errors because initialization should not present database errors to clients.
    pub fn new(path: impl AsRef<Path>) -> anyhow::Result<Self> {
        Self::new_inner(Config::new(path))
    }

    /// Creates a temporary database.
    pub fn temporary() -> anyhow::Result<Self> {
        let path = tempfile::TempDir::with_prefix("saturn-v-db_")
            .context("failed to create temporary directory")?
            .keep();

        Self::new_inner(Config::new(path).temporary(true))
    }

    fn new_inner(config: Config) -> anyhow::Result<Self> {
        // open a keyspace using the provided config
        let keyspace = config
            .open_transactional()
            .context("failed to open keyspace")?;

        // create a partition for all transactions with default config
        let partition = keyspace
            .open_partition("main", Default::default())
            .context("failed to open partition")?;

        // sequence starts at 0 (per-runtime)
        let sequence = Arc::new(AtomicU64::new(0));

        // successful creation
        Ok(Self {
            keyspace,
            partition,
            sequence,
        })
    }

    /// Attempts to begin a transaction using this database.
    pub fn transaction(&self) -> ServerResult<FjallTransaction> {
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
            sequence: self.sequence.clone(),
        };

        // populate input map
        tx.inputs = tx.get(&Key::InputMap)?.unwrap_or_default();

        // done!
        Ok(tx)
    }
}

pub struct FjallTransaction {
    tx: WriteTransaction,
    key_buf: Vec<u8>,
    partition: TransactionalPartitionHandle,
    sequence: Arc<AtomicU64>,

    /// Cache [InputMap] to avoid ser/de and DB overhead.
    inputs: InputMap,
}

impl Transaction for FjallTransaction {
    fn get_program(&mut self) -> ServerResult<Program> {
        self.get(&Key::Program)
            .and_then(|program| program.ok_or(ServerError::NoProgramLoaded))
    }

    fn set_program(&mut self, program: Program) -> ServerResult<()> {
        // wipe old inputs if they exist
        // TODO: reuse inputs when possible
        if let Some(old_map) = self.get::<InputMap>(&Key::InputMap)? {
            for name in old_map.relations.keys() {
                self.clear(name)?;
            }
        }

        // allocate new input relation indices
        let relations = program
            .relations
            .values()
            .filter(|rel| rel.io == RelationIO::Input)
            .map(|rel| rel.store.clone())
            .enumerate()
            .map(|(idx, name)| (name, u16::try_from(idx).expect("input index overflow")))
            .collect();

        // create new input map
        let inputs = InputMap { relations };

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
        let input_idx = self.get_input_index(input)?;
        let key = Key::Input { input: input_idx };
        let prefix = key.as_path(&mut self.key_buf);

        // fetch all items (cannot reborrow for remove)
        let items: Vec<_> = self.tx.prefix(&self.partition, prefix).collect();

        // delete the whole prefix
        for item in items {
            let (key, _val) = item.map_err(|_| ServerError::DatabaseError)?;
            // TODO: handle bucket contents?
            self.tx.remove(&self.partition, key.as_ref());
        }

        // success!
        Ok(())
    }

    fn update(&mut self, input: &str, updates: &[TupleUpdate]) -> ServerResult<()> {
        let input_idx = self.get_input_index(input)?;

        for TupleUpdate { state, value } in updates.iter() {
            let bucket = Key::bucket(input_idx, value);

            self.fetch_update(&bucket, |old: Option<&Bucket>| {
                let mut new = old.map(ToOwned::to_owned).unwrap_or_default();

                if *state {
                    new.retain(|v| v != value);
                } else if !new.contains(&value) {
                    new.push(value.clone());
                }

                if new.is_empty() { None } else { Some(new) }
            })?;
        }

        Ok(())
    }

    fn get(&mut self, input: &str, values: &[Value]) -> ServerResult<Vec<bool>> {
        let input_idx = self.get_input_index(input)?;
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

    fn commit(self) -> ServerResult<SequenceId> {
        // perform actual commit
        // first error is IO, second error is SSI conflict
        self.tx
            .commit()
            .map_err(|_| ServerError::DatabaseError)?
            .map_err(|_| ServerError::Conflict)?;

        // get sequence ID
        let seq = self.sequence.fetch_add(1, Ordering::SeqCst);

        // TODO: update dataflow

        // done!
        Ok(SequenceId(seq))
    }
}

impl FjallTransaction {
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

    /// Gets an input's index by name.
    pub fn get_input_index(&self, input: &str) -> ServerResult<u16> {
        self.inputs
            .relations
            .get(input)
            .copied()
            .ok_or(ServerError::NoSuchInput(input.to_string()))
    }
}

/// A bucket (as in hash set) of values in a single database entry.
pub type Bucket = Vec<Value>;

/// Mappings between program relations and input indices.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct InputMap {
    pub relations: HashMap<String, u16>,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_tx() {
        let db = Database::temporary().unwrap();
        let _tx = db.transaction().unwrap();
    }
}
