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

#[test]
fn create_tx() {
    let db = Database::temporary().unwrap();
    let dataflow = MockDataflow::default();
    let _tx = db.transaction(dataflow).unwrap();
}

#[test]
fn test_get_program_no_program_loaded() {
    let db = Database::temporary().unwrap();
    let dataflow = MockDataflow::default();
    let mut tx = db.transaction(dataflow).unwrap();
    let result = tx.get_program();
    assert_eq!(result.unwrap_err(), ServerError::NoProgramLoaded);
}

#[test]
fn test_set_program_invalid_program() {
    let db = Database::temporary().unwrap();
    let dataflow = MockDataflow::default();
    let mut tx = db.transaction(dataflow).unwrap();

    let mut program = Program::default();
    program.insert_relation(ir::Relation {
        store: "Invalid".to_string(),
        ty: StructuredType::Primitive(ir::Type::String),
        kind: ir::RelationKind::Basic,
        io: ir::RelationIO::None,
        stratum: 0,
        facts: vec![vec![ir::Value::Integer(0)]],
        rules: vec![],
    });

    let result = tx.set_program(program.clone());
    let expected_error = ServerError::InvalidProgram(program.validate().err().unwrap());
    assert_eq!(result.unwrap_err(), expected_error);
}

#[test]
fn test_set_and_get_program_success() {
    let db = Database::temporary().unwrap();
    let dataflow = MockDataflow::default();
    let mut tx = db.transaction(dataflow).unwrap();

    let mut program = Program::default();
    program.insert_relation(ir::Relation {
        store: "TestInput".to_string(),
        ty: StructuredType::Primitive(ir::Type::String),
        kind: ir::RelationKind::Basic,
        io: ir::RelationIO::Input,
        stratum: 0,
        facts: vec![],
        rules: vec![],
    });

    // set the program
    tx.set_program(program.clone()).unwrap();

    // get the program and verify it matches
    assert_eq!(program, tx.get_program().unwrap());
}

#[test]
fn test_get_input_contains_values() {
    use StructuredValue::String;
    let db = Database::temporary().unwrap();
    let dataflow = MockDataflow::default();
    let mut tx = db.transaction(dataflow).unwrap();

    // Create a program with an input relation
    let mut program = Program::default();
    program.insert_relation(ir::Relation {
        store: "TestInput".to_string(),
        ty: StructuredType::Primitive(ir::Type::String),
        kind: ir::RelationKind::Basic,
        io: ir::RelationIO::Input,
        stratum: 0,
        facts: vec![],
        rules: vec![],
    });

    tx.set_program(program).unwrap();

    // Insert some values into the input
    let updates = vec![
        TupleUpdate {
            state: true,
            value: String("hello".to_string()),
        },
        TupleUpdate {
            state: true,
            value: String("world".to_string()),
        },
    ];
    tx.update_input("TestInput", &updates).unwrap();

    // Test checking for values
    let values_to_check = vec![
        String("hello".to_string()),
        String("missing".to_string()),
        String("world".to_string()),
    ];

    let results = tx
        .check_input_values("TestInput", &values_to_check)
        .unwrap();

    assert_eq!(results, vec![true, false, true]);
}

#[test]
fn test_no_such_input_error() {
    let db = Database::temporary().unwrap();
    let dataflow = MockDataflow::default();
    let mut tx = db.transaction(dataflow).unwrap();

    // create a program with no input relations
    let program = Program::default();
    tx.set_program(program).unwrap();

    // try to access a non-existent input
    let values = vec![StructuredValue::String("test".to_string())];
    let result = tx.check_input_values("NonExistentInput", &values);

    assert_eq!(
        result.unwrap_err(),
        ServerError::NoSuchInput("NonExistentInput".to_string())
    );
}
