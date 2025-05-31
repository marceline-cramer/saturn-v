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
    fmt::Display,
    hash::Hash,
};

use indexmap::IndexSet;
use saturn_v_ir::{self as ir, Expr, Instruction, Program, QueryTerm, Rule};
use tracing::debug;

use crate::{
    types::{Fact, Node, NodeInput, NodeOutput, NodeSource, Relation},
    utils::{InputSource, Key},
};

pub type VariableMap = IndexSet<u32>;

#[derive(Clone, Debug)]
pub struct Loader<R> {
    pub(crate) relations: HashMap<R, Relation>,
    pub(crate) facts: HashSet<Fact>,
    pub(crate) nodes: HashSet<Node>,
}

impl<R: Clone + Display + Hash + Eq + 'static> Loader<R> {
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

    /// Inserts the contents of this loader into dataflow inputs.
    pub fn add_to_dataflow(
        self,
        relations: &mut InputSource<Relation>,
        facts: &mut InputSource<Fact>,
        nodes: &mut InputSource<Node>,
    ) {
        // display statistics
        debug!(
            relations = self.relations.len(),
            facts = self.facts.len(),
            unique_nodes = self.nodes.len(),
            "loading dataflow",
        );

        for relation in self.relations.into_values() {
            relations.insert(relation);
        }

        for fact in self.facts {
            facts.insert(fact);
        }

        for node in self.nodes {
            nodes.insert(node);
        }

        nodes.flush();
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
                        formatting: rel.formatting.clone().into(),
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
        let (node, map) =
            self.load_instruction(&constraint.body.loaded, &constraint.body.instructions);

        // map the constraint head
        let mut head = Vec::with_capacity(constraint.head.len());
        for idx in constraint.head.iter() {
            let mapped = map.get_index_of(idx).unwrap();
            head.push(mapped);
        }

        // make the node output to a constraint
        let output = NodeOutput::Constraint {
            head: head.into(),
            weight: constraint.weight,
            kind: constraint.kind.clone(),
        };

        // insert the node
        self.insert(node, None, Some(output));
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
        let (node, map) = self.load_instruction(&rule.body.loaded, &rule.body.instructions);

        // build the head of the relation and its projection
        let mut head = Vec::with_capacity(rule.head.len());
        let mut proj = Vec::with_capacity(rule.head.len());
        for term in rule.head.iter() {
            head.push(match term {
                QueryTerm::Value(val) => QueryTerm::Value(val.clone()),
                QueryTerm::Variable(idx) => {
                    let mapped = map.get_index_of(idx).unwrap();
                    let idx = proj.len();
                    proj.push(mapped);
                    QueryTerm::Variable(idx.try_into().unwrap())
                }
            });
        }

        // make the node output to a relation
        let output = NodeOutput::Relation {
            dst: Key::new(self.relations.get(relation).unwrap()),
            head: head.into(),
        };

        // store the node
        self.insert(node, Some(proj), Some(output));
    }

    /// Stores a node with a given projection and returns its node source.
    fn insert(
        &mut self,
        node: WipNode,
        project: Option<Vec<usize>>,
        output: Option<NodeOutput>,
    ) -> NodeSource {
        if let NodeInput::Source { src } = &node.input {
            if node.push.is_empty()
                && node.filter.is_empty()
                && project.is_none()
                && output.is_none()
            {
                return src.clone();
            }
        }

        let node = Node {
            input: node.input,
            push: node.push.into(),
            filter: node.filter.into(),
            project: project.map(Into::into),
            output,
        };

        let key = Key::new(&node);
        let src = NodeSource::Node { node: key };
        self.nodes.insert(node);
        src
    }

    /// Loads an instruction. Returns the node of the instruction and a [VariableMap].
    fn load_instruction(&mut self, loaded: &[R], instr: &Instruction) -> (WipNode, VariableMap) {
        use Instruction::*;
        match instr {
            Noop => unreachable!("cannot load noops"),
            Sink { .. } => unreachable!("cannot load sinks"),
            Filter { test, rest } => {
                let (mut node, map) = self.load_instruction(loaded, rest);
                let expr = map_variables(test.clone(), &map);
                node.filter.push(expr);
                (node, map)
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
                let mut query = Vec::new();
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

                // create node input
                let input = NodeInput::Source {
                    src: NodeSource::Relation {
                        relation,
                        query: query.into(),
                    },
                };

                // create node
                let node = WipNode::new(input);

                // return new node and variable map
                (node, map)
            }
            Let { var, expr, rest } => {
                // create nodes for the rest of the instructions
                let (mut node, mut map) = self.load_instruction(loaded, rest);

                // map variables from rule-scoped indices to node-scoped indices
                let expr = map_variables(expr.clone(), &map);

                // add the variable to upwards-bound mappings
                map.insert(*var);

                // add push expression to node
                node.push.push(expr);

                // return modified node
                (node, map)
            }
            Merge { lhs, rhs } => {
                // add the nodes for each branch
                let (lhs, lhs_map) = self.load_instruction(loaded, lhs);
                let (rhs, rhs_map) = self.load_instruction(loaded, rhs);

                // assert that the variable maps are equal
                assert_eq!(lhs_map, rhs_map);

                // ensure that the right-hand side is projected to the left-hand map
                let mut rhs_proj = Vec::with_capacity(rhs_map.len());
                for var in lhs_map.iter() {
                    let rhs_idx = rhs_map.get_index_of(var).unwrap();
                    rhs_proj.push(rhs_idx);
                }

                // insert left-hand side and project right-hand side
                let lhs = self.insert(lhs, None, None);
                let rhs = self.insert(rhs, Some(rhs_proj), None);

                // create the merge node
                let node = WipNode::new(NodeInput::Merge { lhs, rhs });

                // return the node and its variable map
                (node, lhs_map)
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

                // store projected nodes
                let lhs = self.insert(lhs, Some(lhs_proj), None);
                let rhs = self.insert(rhs, Some(rhs_proj), None);

                // create the join node
                let node = WipNode::new(NodeInput::Join { lhs, rhs, num });

                // return the node and its map
                (node, joined)
            }
        }
    }
}

/// Maps an expression's variables using the given variable map.
pub fn map_variables(expr: ir::Expr, map: &IndexSet<u32>) -> ir::Expr {
    use ir::Expr::*;
    match expr {
        Variable(idx) => Variable(map.get_index_of(&idx).unwrap() as u32),
        UnaryOp { op, term } => UnaryOp {
            op,
            term: map_variables((*term).clone(), map).into(),
        },
        BinaryOp { op, lhs, rhs } => BinaryOp {
            op,
            lhs: map_variables((*lhs).clone(), map).into(),
            rhs: map_variables((*rhs).clone(), map).into(),
        },
        Load { relation, query } => Load {
            relation,
            query: query
                .into_iter()
                .map(|term| match term {
                    QueryTerm::Variable(idx) => {
                        QueryTerm::Variable(map.get_index_of(&idx).unwrap() as u32)
                    }
                    term => term,
                })
                .collect(),
        },
        other => other,
    }
}

pub struct WipNode {
    pub input: NodeInput,
    pub push: Vec<Expr>,
    pub filter: Vec<Expr>,
}

impl WipNode {
    pub fn new(input: NodeInput) -> Self {
        Self {
            input,
            push: vec![],
            filter: vec![],
        }
    }
}
