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

use std::collections::{HashMap, HashSet};

use salsa::{Database, Update};

use crate::{
    parse::{file_relations, AbstractType, RelationDefinition, TypeAlias},
    toplevel::File,
    types::{PrimitiveType, WithAst},
};

/// Resolves the type of a relation definition.
#[salsa::tracked]
pub fn resolve_relation_type<'a>(
    db: &'a dyn Database,
    def: RelationDefinition<'a>,
) -> ResolvedRelationType<'a> {
    // recursively resolve the abstract type
    let mut in_progress = HashSet::new();
    in_progress.insert(Unresolved::Relation(def));
    let kind = resolve_abstract_type(db, &in_progress, def.ty(db));

    // build the resolved relation type
    ResolvedRelationType::new(db, def, kind)
}

/// Helper function to recursively resolve an abstract relation type.
fn resolve_abstract_type<'db>(
    db: &'db dyn Database,
    in_progress: &HashSet<Unresolved>,
    ty: &WithAst<AbstractType>,
) -> WithAst<ResolvedType<'db>> {
    // first, handle non-named types
    let name = match ty.as_ref() {
        AbstractType::Named(name) => name,
        AbstractType::Primitive(prim) => return ty.with(ResolvedType::Primitive(*prim)),
        AbstractType::Tuple(els) => {
            return ty.with(ResolvedType::Tuple(
                els.iter()
                    .map(|el| resolve_abstract_type(db, in_progress, el))
                    .collect(),
            ))
        }
    };

    // attempt to look up the resolved type
    let file = ty.ast.file(db);
    match file_unresolved_types(db, file).get(name) {
        None => ty.with(ResolvedType::Unknown),
        Some(unresolved) => {
            // we're tracking a new unresolved type in the cycle
            // create a new set to track it
            let mut new_in_progress = in_progress.clone();

            // if the cycle tracker already has this item, bail
            // TODO: throw an error
            if !new_in_progress.insert(*unresolved) {
                return ty.with(ResolvedType::Unknown);
            }

            // resolve the specific kind of item
            match unresolved {
                Unresolved::Relation(def) => {
                    resolve_abstract_type(db, &new_in_progress, def.ty(db))
                }
                _ => unimplemented!(),
            }
        }
    }
}

/// Looks up all unresolved type definitions in a file by name.
#[salsa::tracked]
pub fn file_unresolved_types<'a>(
    db: &'a dyn Database,
    file: File,
) -> HashMap<String, Unresolved<'a>> {
    // track running types
    let mut unresolved = HashMap::new();

    // add relations
    for (name, def) in file_relations(db, file) {
        let ty = Unresolved::Relation(def);
        unresolved.insert(name, ty);
    }

    // return the complete list
    unresolved
}

/// A resolved relation type definition.
#[salsa::tracked]
pub struct ResolvedRelationType<'db> {
    /// The relation definition this relation type corresponds to.
    pub def: RelationDefinition<'db>,

    /// The inner resolved type.
    pub kind: WithAst<ResolvedType<'db>>,
}

/// A resolved type alias definition.
#[salsa::tracked]
pub struct ResolvedTypeAlias<'db> {
    /// The type alias definition this resolved alias corresponds to.
    pub def: TypeAlias<'db>,

    /// The inner resolved type.
    pub kind: WithAst<ResolvedType<'db>>,
}

/// May contain tuples, primitives, and resolved alias or relation types.
#[derive(Clone, PartialEq, Eq, Hash, Update)]
pub enum ResolvedType<'db> {
    Primitive(PrimitiveType),
    Tuple(Vec<WithAst<ResolvedType<'db>>>),
    Relation(ResolvedRelationType<'db>),
    Alias(ResolvedTypeAlias<'db>),

    /// This type leaf could not be resolved.
    Unknown,
}

/// An enum to encapsulate different kinds of unresolved items for cycle tracking.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Update)]
pub enum Unresolved<'db> {
    Relation(RelationDefinition<'db>),
    Alias(TypeAlias<'db>),
}
