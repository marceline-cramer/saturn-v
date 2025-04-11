use std::collections::HashSet;

use indexmap::IndexSet;
use saturn_v_ir::{Instruction, QueryTerm};

use crate::{
    types::{Fact, Node, Query, Relation},
    utils::Key,
};

pub type VariableMap = IndexSet<usize>;

#[derive(Debug)]
pub struct Loader {
    pub(crate) relations: IndexSet<Relation>,
    pub(crate) facts: HashSet<Fact>,
    pub(crate) nodes: HashSet<Node>,
}

impl Loader {
    pub fn new(relations: Vec<Relation>) -> Self {
        Self {
            relations: IndexSet::from_iter(relations),
            facts: HashSet::new(),
            nodes: HashSet::new(),
        }
    }

    pub fn add_fact(&mut self, fact: Fact) {
        self.facts.insert(fact);
    }

    pub fn store_relation(&mut self, relation: usize, head: Vec<QueryTerm>, instr: &Instruction) {
        let dst = Key::new(self.relations.get_index(relation).unwrap());
        let (src, map) = self.add_instruction(instr);

        let head = head
            .into_iter()
            .map(|term| match term {
                QueryTerm::Value(val) => QueryTerm::Value(val),
                QueryTerm::Variable(idx) => QueryTerm::Variable(map.get_index_of(&idx).unwrap()),
            })
            .collect();

        self.nodes.insert(Node::StoreRelation { src, dst, head });
    }

    pub fn add_instruction(&mut self, instr: &Instruction) -> (Key<Node>, VariableMap) {
        use Instruction::*;
        match instr {
            Noop => unreachable!("cannot load noops"),
            Sink(_, _) => unreachable!("cannot load sinks"),
            Filter(test, rest) => {
                let (src, map) = self.add_instruction(rest);
                let expr = test.clone().map_variables(&map);
                let (dst, node) = Key::pair(Node::Filter { src, expr });
                self.nodes.insert(node);
                (dst, map)
            }
            FromQuery(idx, terms) => {
                // TODO: error handling here
                let relation = Key::new(self.relations.get_index(*idx as usize).unwrap());

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
            Let(var, expr, rest) => {
                let (src, mut map) = self.add_instruction(rest);
                let expr = expr.clone().map_variables(&map);
                let (dst, node) = Key::pair(Node::Push { src, expr });
                map.insert(*var as usize);
                self.nodes.insert(node);
                (dst, map)
            }
            Merge(lhs, rhs) => {
                let (lhs, lhs_map) = self.add_instruction(lhs);
                let (rhs, rhs_map) = self.add_instruction(rhs);
                assert_eq!(lhs_map, rhs_map);
                let (dst, node) = Key::pair(Node::Merge { lhs, rhs });
                self.nodes.insert(node);
                (dst, lhs_map)
            }
            Join(lhs, rhs) => {
                let (lhs, lhs_map) = self.add_instruction(lhs);
                let (rhs, rhs_map) = self.add_instruction(rhs);

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
