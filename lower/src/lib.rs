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

use std::collections::{BTreeMap, HashSet};

#[derive(Clone, Default)]
pub struct Scope {
    /// The set of indexed relations owned by this scope. Each relation is unique
    /// and indexed by `reverse_map`.
    relations: Vec<PrimitiveRelation>,

    /// A reverse lookup table from primitive relations to their indices in
    /// `relations`.
    reverse_lookup: BTreeMap<PrimitiveRelation, usize>,

    /// A backlog of freshly-inserted primitive relations to rewrite with their indices.
    inserted: Vec<(usize, PrimitiveRelation)>,

    /// A disjoint set data structure of all of the tautology groups of the
    /// primitive relations. This set looks up the parent of a given index.
    /// If no parent exists, it is a root.
    tautologies: BTreeMap<usize, usize>,
}

impl Scope {
    /// Find the root node of a tautology group by relation index.
    ///
    /// Mutates the tautology graph to make future lookups faster.
    pub fn lookup_taut(&mut self, mut idx: usize) -> usize {
        // create a trace of touched indices to update once the root is found
        let mut trace = vec![];

        // follow tautology pointers until root is found
        let root = loop {
            // look up the parent of this tautology node
            let Some(parent) = self.tautologies.get(&idx).copied() else {
                // if no parent exists, we've found the root
                break idx;
            };

            // trace this node
            trace.push(idx);

            // lookup the parent and restart search
            idx = parent;
        };

        // update all of the touched indices
        for idx in trace {
            self.tautologies.insert(idx, root);
        }

        // return the found root
        root
    }

    /// Inserts a fresh relation into this scope. Returns its index.
    ///
    /// Does not modify tautology groups.
    pub fn insert(&mut self, relation: PrimitiveRelation) -> usize {
        use std::collections::btree_map::Entry;
        match self.reverse_lookup.entry(relation.clone()) {
            // if the relation is old, just return its index
            Entry::Occupied(entry) => *entry.get(),
            // otherwise, create a new index for it and queue it for rewriting
            Entry::Vacant(entry) => {
                let idx = self.relations.len();
                self.relations.push(relation.clone());
                self.inserted.push((idx, relation));
                entry.insert(idx);
                idx
            }
        }
    }

    /// Unifies two tautology groups.
    pub fn unify(&mut self, lhs: usize, rhs: usize) {
        // make sure both indices point to their roots
        let lhs = self.lookup_taut(lhs);
        let rhs = self.lookup_taut(rhs);

        // make sure we don't construct recursive groups
        if lhs != rhs {
            self.tautologies.insert(lhs, rhs);
        }
    }

    /// Rewrites all pending relations until fixed-point.
    pub fn flush(&mut self) {
        // pop a pending relation until none are left
        while let Some((idx, rel)) = self.inserted.pop() {
            // rewrite this relation
            for rewrite in rel.rewrites() {
                // insert this rewrite and get its index
                let rewrite_idx = self.insert(rewrite);

                // unify the rewrite's tautology group with the original
                // relation's tautology group
                self.unify(idx, rewrite_idx);
            }
        }
    }

    /// Finds all the root indices of the tautology groups in this scope.
    pub fn tautology_groups(&self) -> Vec<usize> {
        // iterate through each relation
        let mut roots = Vec::new();
        for idx in 0..self.relations.len() {
            // if there is a relation but not a tautology lookup, this relation
            // is the root of its tautology group
            if !self.tautologies.contains_key(&idx) {
                roots.push(idx);
            }
        }

        // return the roots
        roots
    }

    /// Look up every relation and its index.
    pub fn relations(&self) -> impl Iterator<Item = (usize, PrimitiveRelation)> + 'static {
        self.relations.clone().into_iter().enumerate()
    }
}

/// Searches for a single procedural interpretation of a scope.
pub fn interpret_any(scope: &mut Scope) -> Option<Vec<PrimitiveRelation>> {
    // ensure scope is flushed
    scope.flush();

    // load all relations by index
    let relations: Vec<_> = scope
        .relations()
        .map(|(idx, rel)| {
            let relation = SearchRelation {
                data: rel,
                tautology_group: scope.lookup_taut(idx),
            };

            (idx, relation)
        })
        .collect();

    // the set of all tautology groups that need to be satisfied
    let tautology_groups: HashSet<usize> = HashSet::from_iter(scope.tautology_groups());

    // the stack of active search nodes
    let mut stack = vec![SearchNode::default()];

    // depth-first search
    while let Some(node) = stack.pop() {
        // if all tautologies have been satisfied, this node is a complete search
        if node.tautologies == tautology_groups {
            return Some(node.relations);
        }

        // find next relations to activate and search
        for (idx, rel) in relations.iter() {
            // get the tautology this relation belongs to
            let taut = scope.lookup_taut(*idx);

            // ignore this relation if its tautology is satisfied
            if node.tautologies.contains(&taut) {
                continue;
            }

            // ignore this relation if its variables are unsatisfied
            if !rel.can_activate(&node.variables) {
                continue;
            }

            // create a child search node
            let mut child = node.clone();

            // this relation activates its tautology
            child.tautologies.insert(rel.tautology_group);

            // push the activated relation to the search node
            child.relations.push(rel.data.clone());

            // assign any variables
            // TODO: abstract this into SearchRelation (like can_activate())
            child.variables.extend(rel.data.assigns());

            // pursue this child as a search tree branch
            stack.push(child);
        }
    }

    // no interpretation could be found
    None
}

#[derive(Clone, Debug, Default)]
struct SearchNode {
    /// The list of active relations.
    relations: Vec<PrimitiveRelation>,

    /// The set of variables that are assigned.
    variables: HashSet<usize>,

    /// The set of tautology groups that have been satisfied.
    tautologies: HashSet<usize>,
}

struct SearchRelation {
    /// This relation's primitive data.
    data: PrimitiveRelation,

    /// The tautology group that this relation satisfies.
    tautology_group: usize,
}

impl SearchRelation {
    /// Tests whether a given assignment of variables allows this relation to
    /// activate.
    pub fn can_activate(&self, variables: &HashSet<usize>) -> bool {
        self.data.deps().all(|idx| variables.contains(&idx))
    }
}

pub struct EvalArena {
    /// The set of nodes in this arena. Each relation is unique and indexed by
    /// `reverse_map`.
    nodes: Vec<EvalNode>,

    /// A reverse lookup table from nodes to their indices in `nodes`.
    reverse_lookup: BTreeMap<EvalNode, usize>,

    /// A backlog of freshly-inserted nodes to fork the search of.
    inserted: Vec<(usize, EvalNode)>,
}

pub struct EvalNode {
    src: EvalSource,
    ops: Vec<PrimitiveRelation>,
}

pub enum EvalSource {
    Load { idx: usize, terms: Vec<Term> },
    Join { lhs: usize, rhs: usize },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveRelation {
    Binary {
        op: BinaryOpKind,
        out: Term,
        lhs: Term,
        rhs: Term,
    },

    Unary {
        op: UnaryOpKind,
        out: Term,
        term: Term,
    },

    Magic {
        var: usize,
    },

    Load {
        idx: usize,
        terms: Vec<Term>,
    },
}

impl PrimitiveRelation {
    pub fn rewrites(self) -> Vec<Self> {
        use BinaryOpKind::*;
        use PrimitiveRelation::*;

        fn binary(op: BinaryOpKind, out: Term, lhs: Term, rhs: Term) -> PrimitiveRelation {
            Binary { op, out, lhs, rhs }
        }

        fn unary(op: UnaryOpKind, out: Term, term: Term) -> PrimitiveRelation {
            Unary { op, out, term }
        }

        let mut rewrites = vec![];

        // TODO: commutative identities?
        match self {
            Binary { op, out, lhs, rhs } => {
                // commutative identities
                if let Add | Mul | Eq = op {
                    rewrites.push(binary(op, out, rhs, lhs));
                }

                // TODO: fancy string prefix/suffix concat rewrites

                // related operators
                let related = match op {
                    Add => Some([binary(Sub, lhs, out, rhs), binary(Sub, rhs, out, lhs)]),
                    Sub => Some([binary(Add, lhs, out, rhs), binary(Sub, rhs, lhs, out)]),
                    Mul => Some([binary(Div, lhs, out, rhs), binary(Div, rhs, out, lhs)]),
                    Div => Some([binary(Mul, lhs, out, rhs), binary(Div, rhs, lhs, out)]),
                    _ => None,
                };

                rewrites.extend(related.into_iter().flatten());
            }
            Unary {
                op,
                out: lhs,
                term: rhs,
            } => rewrites.push(unary(op, rhs, lhs)),
            _ => {}
        }

        // return the full set of rewrites
        rewrites
    }

    /// Returns the set of all variables that are a dependency of this relation.
    pub fn deps(&self) -> impl Iterator<Item = usize> {
        use PrimitiveRelation::*;
        match self {
            Binary { lhs, rhs, .. } => Some([lhs.variable(), rhs.variable()]),
            Unary { out, term, .. } => Some([out.variable(), term.variable()]),
            Magic { .. } | Load { .. } => None,
        }
        .into_iter()
        .flatten()
        .flatten()
    }

    /// Returns the set of all variables that are assigned by this relation.
    pub fn assigns(&self) -> Vec<usize> {
        use PrimitiveRelation::*;
        match self {
            Binary { out, .. } => out.variable().into_iter().collect(),
            Unary { out, .. } => out.variable().into_iter().collect(),
            Magic { var } => vec![*var],
            Load { terms, .. } => terms.iter().flat_map(Term::variable).collect(),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Value(Value),
    Variable(usize),
}

impl Term {
    pub fn variable(&self) -> Option<usize> {
        if let Term::Variable(idx) = self {
            Some(*idx)
        } else {
            None
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Concat,
    And,
    Or,
    Eq,
    Lt,
    Le,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryOpKind {
    Not,
    Negate,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Value {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        use PrimitiveRelation::*;

        let mut scope = Scope::default();

        let a = Magic { var: 0 };
        let b = Magic { var: 1 };
        let c = Binary {
            op: BinaryOpKind::Add,
            out: Term::Variable(2),
            lhs: Term::Variable(1),
            rhs: Term::Variable(0),
        };

        scope.insert(a.clone());
        scope.insert(b.clone());
        scope.insert(c.clone());

        let result = interpret_any(&mut scope);
        assert_eq!(result, Some(vec![b, a, c]))
    }

    #[test]
    fn join() {
        use PrimitiveRelation::*;

        let mut scope = Scope::default();

        scope.insert(Load {
            idx: 0,
            terms: vec![Term::Variable(0), Term::Variable(1)],
        });

        scope.insert(Load {
            idx: 0,
            terms: vec![Term::Variable(1), Term::Variable(2)],
        });

        let result = interpret_any(&mut scope);
        eprintln!("{result:#?}");
    }
}
