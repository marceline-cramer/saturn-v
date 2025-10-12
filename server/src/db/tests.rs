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
// along with Saturn V. If not, see <https://www.gnu.org/licenses>.

use std::collections::{BTreeSet, VecDeque};

use super::*;

/// A mock implementation of CommitDataflow for testing purposes.
#[derive(Clone, Default)]
pub struct MockDataflow {
    sequence: u64,
    state: BTreeSet<InputEventKind>,
    events: VecDeque<Vec<InputEvent>>,
}

impl CommitDataflow for MockDataflow {
    fn commit(mut self, events: Vec<InputEvent>) -> SequenceId {
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

#[test]
fn create_tx() {
    let db = Database::temporary().unwrap();
    let dataflow = MockDataflow::default();
    let _tx = db.transaction(dataflow).unwrap();
}
