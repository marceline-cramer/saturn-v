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
    collections::{HashMap, HashSet},
    hash::Hash,
};

use indexmap::IndexSet;
use saturn_v_ir::{self as ir, Instruction, Program, QueryTerm, Rule};

use crate::{
    types::{Fact, IndexList, Node, Query, Relation, StoreHead},
    utils::Key,
};

pub type VariableMap = IndexSet<u32>;

#[derive(Debug)]
pub struct Loader<R> {
    pub(crate) relations: HashMap<R, Relation>,
    pub(crate) facts: HashSet<Fact>,
    pub(crate) nodes: HashSet<Node>,
}

impl<R: Clone + Hash + Eq + 'static> Loader<R> {
    /// Loads a program.
    pub fn load_program(program: &Program<R>) -> Self {
        // assert that the program is valid
        if let Err(err) = program.validate() {
            panic!("program failed validation\n{err}");
        }

        // create an initial load using the program's relations
        let mut loader = Self::new(program.relations.values());

        // add all of the program's relations
        for r in program.relations.values() {
            loader.load_relation(r);
        }

        // add all of the program's constraints
        for c in program.constraints.iter() {
            loader.load_constraint(c);
        }

        // return the completely loaded program
        loader
    }

    /// Creates a new loader with the given set of indexed relations.
    ///
    /// Private because you're intended to use [Self::load_program] to work
    /// with entire programs at once. Since relations are discriminated by
    /// their index in the relations list, this makes the loader not work well
    /// with multiple programs or node sources quite yet.
    fn new<'a>(relations: impl Iterator<Item = &'a ir::Relation<R>>) -> Self {
        let relations = relations
            .enumerate()
            .map(|(idx, rel)| {
                (
                    rel.store.clone(),
                    Relation {
                        discriminant: idx as u64,
                        kind: rel.kind,
                        is_output: rel.is_output,
                    },
                )
            })
            .collect();

        Self {
            relations,
            facts: HashSet::new(),
            nodes: HashSet::new(),
        }
    }

    /// Loads a constraint.
    fn load_constraint(&mut self, constraint: &ir::Constraint<R>) {
        // load the instructions
        let (src, map) = self.load_instruction(&constraint.loaded, &constraint.instructions);

        // map the constraint head
        let mut head = IndexList::with_capacity(constraint.head.len());
        for idx in constraint.head.iter() {
            let mapped = map.get_index_of(idx).unwrap();
            head.push(mapped);
        }

        // add the constraint node
        self.nodes.insert(Node::Constraint {
            src,
            head,
            weight: constraint.weight.clone(),
            kind: constraint.kind.clone(),
        });
    }

    /// Loads a relation.
    fn load_relation(&mut self, relation: &ir::Relation<R>) {
        // add facts
        let key = Key::new(self.relations.get(&relation.store).unwrap());
        for fact in relation.facts.iter() {
            self.facts.insert(Fact {
                relation: key,
                values: fact.clone().into(),
            });
        }

        // add all rules
        for rule in relation.rules.iter() {
            self.load_rule(&relation.store, rule);
        }
    }

    /// Loads a rule.
    fn load_rule(&mut self, relation: &R, rule: &Rule<R>) {
        // load the instructions
        let (src, map) = self.load_instruction(&rule.loaded, &rule.instructions);

        // build the head of the relation
        let mut head = StoreHead::with_capacity(rule.head.len());
        for term in rule.head.iter() {
            head.push(match term {
                QueryTerm::Value(val) => QueryTerm::Value(val.clone()),
                QueryTerm::Variable(idx) => {
                    let mapped = map.get_index_of(idx).unwrap();
                    QueryTerm::Variable(mapped.try_into().unwrap())
                }
            });
        }

        // add the store node
        let dst = Key::new(self.relations.get(relation).unwrap());
        self.nodes.insert(Node::StoreRelation { src, dst, head });
    }

    /// Loads an instruction. Returns the node of the instruction and a [VariableMap].
    fn load_instruction(&mut self, loaded: &[R], instr: &Instruction) -> (Key<Node>, VariableMap) {
        use Instruction::*;
        match instr {
            Noop => unreachable!("cannot load noops"),
            Sink { .. } => unreachable!("cannot load sinks"),
            Filter { test, rest } => {
                let (src, map) = self.load_instruction(loaded, rest);
                let expr = test.clone().map_variables(&map);
                let (dst, node) = Key::pair(Node::Filter { src, expr });
                self.nodes.insert(node);
                (dst, map)
            }
            FromQuery {
                relation: idx,
                terms,
            } => {
                // load the key of the relation to load from
                let key = &loaded[*idx as usize];
                let relation = Key::new(self.relations.get(key).unwrap());

                // load query terms into node
                let mut map = IndexSet::new();
                let mut query = Query::new();
                for term in terms.iter() {
                    match term.clone() {
                        QueryTerm::Variable(idx) => {
                            map.insert(idx);
                            query.push(None);
                        }
                        QueryTerm::Value(val) => {
                            query.push(Some(val));
                        }
                    }
                }

                // create node
                let (dst, node) = Key::pair(Node::LoadRelation { relation, query });
                self.nodes.insert(node);
                (dst, map)
            }
            Let { var, expr, rest } => {
                // create nodes for the rest of the instructions
                let (src, mut map) = self.load_instruction(loaded, rest);

                // map variables from rule-scoped indices to node-scoped indices
                let expr = expr.clone().map_variables(&map);

                // add the variable to upwards-bound mappings
                map.insert(*var);

                // create the push node
                let (dst, node) = Key::pair(Node::Push { src, expr });
                self.nodes.insert(node);
                (dst, map)
            }
            Merge { lhs, rhs } => {
                // add the nodes for each branch
                let (lhs, lhs_map) = self.load_instruction(loaded, lhs);
                let (rhs, rhs_map) = self.load_instruction(loaded, rhs);

                // assert that the variable maps are equal
                assert_eq!(lhs_map, rhs_map);

                // create the merge node
                let (dst, node) = Key::pair(Node::Merge { lhs, rhs });
                self.nodes.insert(node);
                (dst, lhs_map)
            }
            Join { lhs, rhs } => {
                // add the nodes for each branch
                let (lhs, lhs_map) = self.load_instruction(loaded, lhs);
                let (rhs, rhs_map) = self.load_instruction(loaded, rhs);

                // track variables in each segment of the join
                let mut joined = IndexSet::new(); // variable map in common
                let mut lhs_proj = Vec::new(); // all projected left-hand variables
                let mut rhs_proj = Vec::new(); // all projected right-hand variables

                // add joined indices in order from the left-hand side
                for (lhs_idx, lhs) in lhs_map.iter().enumerate() {
                    if let Some(rhs_idx) = rhs_map.get_index_of(lhs) {
                        joined.insert(*lhs);
                        lhs_proj.push(lhs_idx);
                        rhs_proj.push(rhs_idx);
                    }
                }

                // save the number of common variables
                let num = joined.len();

                // add unjoined indices from the left-hand side
                for (lhs_idx, lhs) in lhs_map.iter().enumerate() {
                    if !rhs_map.contains(lhs) {
                        joined.insert(*lhs);
                        lhs_proj.push(lhs_idx);
                    }
                }

                // add unjoined indices from the right-hand side
                for (rhs_idx, rhs) in rhs_map.iter().enumerate() {
                    if !lhs_map.contains(rhs) {
                        joined.insert(*rhs);
                        rhs_proj.push(rhs_idx);
                    }
                }

                // create the projection nodes
                let (lhs, lhs_node) = Key::pair(Node::Project {
                    src: lhs,
                    map: lhs_proj.into(),
                });

                let (rhs, rhs_node) = Key::pair(Node::Project {
                    src: rhs,
                    map: rhs_proj.into(),
                });

                // create the join node
                let (dst, node) = Key::pair(Node::Join { lhs, rhs, num });
                self.nodes.extend([lhs_node, rhs_node, node]);
                (dst, joined)
            }
        }
    }
}
