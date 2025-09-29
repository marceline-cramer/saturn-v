use std::{
    borrow::Cow,
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use fjall::{TransactionalPartition, UserValue, WriteTransaction};
use saturn_v_client::*;
use serde::{Serialize, de::DeserializeOwned};

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

pub struct FjallTransaction<'a> {
    tx: WriteTransaction<'a>,
    key_buf: Vec<u8>,
    partition: TransactionalPartition,
    inputs: HashMap<String, u16>,
    sequence: Arc<AtomicU64>,
}

impl<'a> Transaction for FjallTransaction<'a> {
    fn get_program(&mut self) -> ServerResult<Program> {
        self.get(&Key::Program)
            .and_then(|program| program.ok_or(ServerError::NoProgramLoaded))
    }

    fn set_program(&mut self, program: Program) -> ServerResult<()> {
        // TODO: this needs to completely restructure everything in the database
        // TODO: update input indices to match the new program
        // TODO: sanitize program contents for database keys
        // TODO: sanitize 16-bit input indices
        self.insert(&Key::Program, &program)
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
        self.tx.commit().map_err(|_| ServerError::DatabaseError)?;

        // get sequence ID
        let seq = self.sequence.fetch_add(1, Ordering::SeqCst);

        // TODO: update dataflow

        // done!
        Ok(SequenceId(seq))
    }
}

impl<'a> FjallTransaction<'a> {
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
            .get(input)
            .copied()
            .ok_or(ServerError::NoSuchInput(input.to_string()))
    }
}

/// A bucket (as in hash set) of values in a single database entry.
pub type Bucket = Vec<Value>;

/// Helper enum for constructing paths in the database.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Key {
    Program,
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
