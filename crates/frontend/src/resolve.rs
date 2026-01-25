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

use std::collections::{BTreeMap, HashMap, HashSet};

use salsa::{Database, Update};

use crate::{
    diagnostic::{AccumulateDiagnostic, BasicDiagnostic, DiagnosticKind},
    parse::{self, AbstractImport, AbstractType, AbstractTypeAlias, ItemKind, RelationDefinition},
    toplevel::{AstNode, File, Namespace, NamespaceItem, Workspace},
    types::{PrimitiveType, WithAst},
};

/// Resolves the type of a relation definition.
#[salsa::tracked]
pub fn resolve_relation_type<'db>(
    db: &'db dyn Database,
    def: RelationDefinition<'db>,
) -> ResolvedRelationType<'db> {
    // recursively resolve the abstract type
    let mut in_progress = HashSet::new();
    in_progress.insert(Unresolved::Relation(def));
    let kind = resolve_abstract_type(db, &in_progress, def.ty(db));

    // build the resolved relation type
    ResolvedRelationType::new(db, def, kind)
}

/// Resolves the type of a type alias.
#[salsa::tracked]
pub fn resolve_type_alias<'db>(
    db: &'db dyn Database,
    def: AbstractTypeAlias<'db>,
) -> ResolvedTypeAlias<'db> {
    // recursively resolve the abstract type
    let mut in_progress = HashSet::new();
    in_progress.insert(Unresolved::TypeAlias(def));
    let kind = resolve_abstract_type(db, &in_progress, def.ty(db));

    // build the resolved type alias
    ResolvedTypeAlias::new(db, def, kind)
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
        None => {
            // throw an error diagnostic
            UnknownType {
                name: ty.with(name.clone()),
            }
            .accumulate(db);

            // could not resolve the type name
            ty.with(ResolvedType::Unknown)
        }
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
                    let kind = resolve_abstract_type(db, &new_in_progress, def.ty(db));
                    let resolved = ResolvedRelationType::new(db, *def, kind);
                    ty.with(ResolvedType::Relation(resolved))
                }
                Unresolved::TypeAlias(alias) => {
                    let kind = resolve_abstract_type(db, &new_in_progress, &(*alias).ty(db));
                    let resolved = ResolvedTypeAlias::new(db, *alias, kind);
                    ty.with(ResolvedType::Alias(resolved))
                }
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
    file_interns(db, file)
        .into_iter()
        .flat_map(|(name, item)| match item.inner {
            NamespaceItem::Relation(rel) => Some((name, Unresolved::Relation(rel))),
            NamespaceItem::TypeAlias(alias) => Some((name, Unresolved::TypeAlias(alias))),
            _ => None,
        })
        .collect()
}

/// A resolved relation type definition.
#[salsa::tracked]
#[derive(Debug)]
pub struct ResolvedRelationType<'db> {
    /// The relation definition this relation type corresponds to.
    pub def: RelationDefinition<'db>,

    /// The inner resolved type.
    pub kind: WithAst<ResolvedType<'db>>,
}

/// A resolved type alias definition.
#[salsa::tracked]
#[derive(Debug)]
pub struct ResolvedTypeAlias<'db> {
    /// The type alias definition this resolved alias corresponds to.
    pub def: AbstractTypeAlias<'db>,

    /// The inner resolved type.
    pub kind: WithAst<ResolvedType<'db>>,
}

/// May contain tuples, primitives, and resolved alias or relation types.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Update)]
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
    TypeAlias(AbstractTypeAlias<'db>),
}

/// Resolves a file's exported namespace.
#[salsa::tracked]
pub fn resolve_file_exports<'db>(db: &'db dyn Database, _file: File) -> Namespace<'db> {
    // no exports for now
    Namespace::new(db, Default::default())
}

/// Resolves a relation definition in a file by name.
#[salsa::tracked]
pub fn file_relation(
    db: &dyn Database,
    file: File,
    name: WithAst<String>,
) -> Option<RelationDefinition<'_>> {
    match file_interns(db, file).get(name.as_ref()) {
        None => {
            RelationNotFound { name }.accumulate(db);
            None
        }
        Some(item) => match &item.inner {
            NamespaceItem::Unknown => {
                RelationNotFound { name }.accumulate(db);
                None
            }
            NamespaceItem::Relation(rel) => Some(*rel),
            item => {
                ExpectedRelation {
                    ast: name.ast,
                    got: item.kind(),
                }
                .accumulate(db);

                None
            }
        },
    }
}

/// Resolves a file's internal name table.
#[salsa::tracked]
pub fn file_interns<'db>(
    db: &'db dyn Database,
    file: File,
) -> BTreeMap<String, WithAst<NamespaceItem<'db>>> {
    // create empty name list
    let mut names = Vec::new();

    // initialize name table using file's imports
    names.extend(
        parse::file_item_kind_ast(db, file, ItemKind::Import)
            .into_iter()
            .map(|ast| parse::abstract_import(db, ast))
            .flat_map(|import| import_items(db, import)),
    );

    // add all relation definitions
    names.extend(
        parse::file_item_kind_ast(db, file, ItemKind::Definition)
            .into_iter()
            .map(|ast| parse::abstract_relation(db, ast))
            .map(|rel| (rel.name(db).clone(), NamespaceItem::Relation(rel))),
    );

    // merge all names together in a single table
    let mut table = BTreeMap::new();
    for (name, item) in names {
        use std::collections::btree_map::Entry;
        match table.entry(name.inner.clone()) {
            Entry::Vacant(entry) => {
                entry.insert(name.with(item));
            }
            Entry::Occupied(entry) => {
                ItemDefinedAgain {
                    name: name.inner.clone(),
                    original: entry.get().ast,
                    redefinition: name.ast,
                }
                .accumulate(db);
            }
        }
    }

    // return the completed name table
    table
}

/// Resolves an abstract import to a table of namespace items.
#[salsa::tracked]
pub fn import_items<'db>(
    db: &'db dyn Database,
    import: AbstractImport<'db>,
) -> Vec<(WithAst<String>, NamespaceItem<'db>)> {
    // begin with the file externs
    let mut ns = file_externs(db, import.ast(db).file(db));

    // walk through each segment of the path
    for segment in import.path(db).iter() {
        // resolve the path segment in the current namespace
        let child = namespace_item(db, ns, segment.clone());

        // read the namespace from the child item
        match child {
            // look up child file export namespaces
            NamespaceItem::File(file) => {
                ns = resolve_file_exports(db, file);
                continue;
            }
            // simply recursively search child namespaces
            NamespaceItem::Namespace(child_ns) => {
                ns = child_ns;
                continue;
            }
            // ignore; error for unknown items has already been thrown
            NamespaceItem::Unknown => {}
            // other items may not be indexed
            _ => NoChildren {
                item: segment.clone(),
                kind: child.kind(),
            }
            .accumulate(db),
        }

        // if child could not be found, return a fresh namespace with unknown items
        return import
            .items(db)
            .iter()
            .map(|item| (item.clone(), NamespaceItem::Unknown))
            .collect();
    }

    // resolve each item
    import
        .items(db)
        .iter()
        .map(|item| (item.clone(), namespace_item(db, ns, item.clone())))
        .collect()
}

/// Resolve a path within a namespace to an item.
///
/// Throws an error diagnostic if the item could not be found.
#[salsa::tracked]
pub fn namespace_item<'db>(
    db: &'db dyn Database,
    ns: Namespace<'db>,
    name: WithAst<String>,
) -> NamespaceItem<'db> {
    match ns.items(db).get(name.as_ref()) {
        Some(NamespaceItem::Unknown) | None => {
            UnknownNamespaceItem { name }.accumulate(db);
            NamespaceItem::Unknown
        }
        Some(item) => item.clone(),
    }
}

/// Resolves the namespace available for a file to import from.
#[salsa::tracked]
pub fn file_externs<'db>(db: &'db dyn Database, file: File) -> Namespace<'db> {
    // create a namespace
    let mut items = BTreeMap::new();

    // add the stdlib namespace
    let stdlib = workspace_stdlib(db, file.workspace(db));
    items.insert("Stdlib".to_string(), NamespaceItem::Namespace(stdlib));

    // return the complete externs namespace
    Namespace::new(db, items)
}

/// Creates the stdlib namespace from the workspace input.
#[salsa::tracked]
pub fn workspace_stdlib<'db>(db: &'db dyn Database, ws: Workspace) -> Namespace<'db> {
    let items = ws
        .stdlib(db)
        .iter()
        .map(|(name, file)| (name.clone(), NamespaceItem::File(*file)))
        .collect();

    Namespace::new(db, items)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnknownType {
    pub name: WithAst<String>,
}

impl BasicDiagnostic for UnknownType {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.name.ast..self.name.ast
    }

    fn message(&self) -> String {
        format!("could not find type {}", self.name)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnknownNamespaceItem {
    pub name: WithAst<String>,
}

impl BasicDiagnostic for UnknownNamespaceItem {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.name.ast..self.name.ast
    }

    fn message(&self) -> String {
        format!("could not find {} in namespace", self.name)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ItemDefinedAgain {
    pub name: String,
    pub original: AstNode,
    pub redefinition: AstNode,
}

impl BasicDiagnostic for ItemDefinedAgain {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.redefinition..self.redefinition
    }

    fn message(&self) -> String {
        format!("conflicting definitions of {}", self.name)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }

    fn notes(&self) -> Vec<WithAst<String>> {
        vec![self.original.with("originally defined here".to_string())]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RelationNotFound {
    pub name: WithAst<String>,
}

impl BasicDiagnostic for RelationNotFound {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.name.ast..self.name.ast
    }

    fn message(&self) -> String {
        format!("undefined relation {}", self.name)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NoChildren {
    pub item: WithAst<String>,
    pub kind: &'static str,
}

impl BasicDiagnostic for NoChildren {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.item.ast..self.item.ast
    }

    fn message(&self) -> String {
        format!("{} {} does not have child items", self.kind, self.item)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExpectedRelation {
    pub ast: AstNode,
    pub got: &'static str,
}

impl BasicDiagnostic for ExpectedRelation {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.ast..self.ast
    }

    fn message(&self) -> String {
        format!("expected relation, got {}", self.got)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}
