// Copyright (C) 2025-2026 Marceline Cramer
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
    collections::{BTreeMap, HashMap},
    fmt::Debug,
};

use ropey::{Rope, RopeSlice};
use salsa::{Database, Update};
use smallvec::SmallVec;

use url::Url;

pub use salsa::DatabaseImpl as Db;

use crate::{
    diagnostic::{AccumulateDiagnostic, SimpleError},
    parse::{AbstractTypeAlias, RelationDefinition},
    types::WithAst,
};

#[salsa::input]
pub struct Workspace {
    #[return_ref]
    pub files: HashMap<Url, File>,
    #[return_ref]
    pub stdlib: HashMap<String, File>,
}

#[salsa::tracked]
pub struct Namespace<'db> {
    #[return_ref]
    pub items: BTreeMap<String, NamespaceItem<'db>>,
}

#[derive(Clone, PartialEq, Eq, Hash, Update)]
pub enum NamespaceItem<'db> {
    File(File),
    Namespace(Namespace<'db>),
    Relation(RelationDefinition<'db>),
    TypeAlias(AbstractTypeAlias<'db>),
    Unknown,
}

impl<'db> NamespaceItem<'db> {
    /// Returns a user-readable string identifier for what kind of item this is.
    pub fn kind(&self) -> &'static str {
        match self {
            NamespaceItem::File(_) => "file",
            NamespaceItem::Namespace(_) => "namespace",
            NamespaceItem::Relation(_) => "relation",
            NamespaceItem::TypeAlias(_) => "type alias",
            NamespaceItem::Unknown => "unknown",
        }
    }
}

#[salsa::input]
#[derive(Debug)]
pub struct File {
    pub workspace: Workspace,
    #[return_ref]
    pub contents: Rope,
    #[return_ref]
    pub url: Url,
    pub root: Option<AstNode>,
}

impl File {
    /// Shadow root behind this method to retrieve the file's AST. This is so
    /// we can initialize files with uninitialized ASTs.
    pub fn ast(&self, db: &dyn Database) -> AstNode {
        self.root(db).unwrap()
    }
}

#[salsa::input]
pub struct AstNode {
    pub file: File,
    pub id: usize,
    pub symbol: &'static str,
    pub span: Span,
    #[return_ref]
    pub children: Children,
    #[return_ref]
    pub fields: Vec<(&'static str, AstNode)>,
}

impl Debug for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AstNode")
    }
}

impl AstNode {
    pub fn contents<'db>(&self, db: &'db dyn Database) -> RopeSlice<'db> {
        let span = self.span(db);
        let contents = self.file(db).contents(db);
        let start = contents.line_to_char(span.start.line) + span.start.column;
        let end = contents.line_to_char(span.end.line) + span.end.column;
        contents.slice(start..end)
    }

    pub fn with<T>(self, inner: T) -> WithAst<T> {
        WithAst { ast: self, inner }
    }

    pub fn get_field(&self, db: &dyn Database, name: &str) -> Option<AstNode> {
        for (field, ast) in self.fields(db).iter() {
            if *field == name {
                return Some(*ast);
            }
        }

        None
    }

    pub fn expect_field(&self, db: &dyn Database, name: &str) -> AstNode {
        self.get_field(db, name)
            .unwrap_or_else(|| panic!("expected {:?} node to have {name:?} field", self.symbol(db)))
    }

    pub fn get_fields(
        &self,
        db: &dyn Database,
        name: &str,
    ) -> impl Iterator<Item = Self> + 'static {
        self.fields(db)
            .iter()
            .filter(|(field, _ast)| *field == name)
            .map(|(_name, ast)| *ast)
            .collect::<Vec<_>>()
            .into_iter()
    }

    pub fn get_children(&self, db: &dyn Database) -> impl Iterator<Item = Self> + 'static {
        self.children(db).clone().into_iter()
    }

    pub fn with_contents(&self, db: &dyn Database) -> WithAst<String> {
        self.with(self.contents(db).to_string())
    }

    pub fn location(&self, db: &dyn Database) -> lsp_types::Location {
        lsp_types::Location {
            uri: self.file(db).url(db).clone(),
            range: self.span(db).into(),
        }
    }
}

pub type Children = SmallVec<[AstNode; 4]>;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: Point,
    pub end: Point,
}

impl From<lsp_types::Range> for Span {
    fn from(range: lsp_types::Range) -> Self {
        Self {
            start: range.start.into(),
            end: range.end.into(),
        }
    }
}

impl From<Span> for lsp_types::Range {
    fn from(span: Span) -> Self {
        Self {
            start: span.start.into(),
            end: span.end.into(),
        }
    }
}

impl Span {
    pub fn contains(&self, at: Point) -> bool {
        at >= self.start && at < self.end
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Point {
    pub line: usize,
    pub column: usize,
}

impl From<lsp_types::Position> for Point {
    fn from(pos: lsp_types::Position) -> Self {
        Self {
            line: pos.line as usize,
            column: pos.character as usize,
        }
    }
}

impl From<Point> for lsp_types::Position {
    fn from(pt: Point) -> Self {
        Self {
            line: pt.line as u32,
            character: pt.column as u32,
        }
    }
}

#[salsa::tracked]
pub fn file_syntax_errors(db: &dyn Database, file: File) {
    syntax_errors(db, file.ast(db));
}

#[salsa::tracked]
pub fn syntax_errors(db: &dyn Database, ast: AstNode) {
    if ast.symbol(db) == "ERROR" {
        // include the tree-sitter symbol and nearby text in the diagnostic message
        let sym = ast.symbol(db);
        let contents = ast.with_contents(db).inner;
        let msg = if contents.trim().is_empty() {
            format!("syntax error: {}", sym)
        } else {
            format!("syntax error: {} near `{}`", sym, contents.trim())
        };

        SimpleError::new(ast, msg).accumulate(db);
    } else {
        ast.children(db)
            .iter()
            .for_each(|child| syntax_errors(db, *child));
    }
}

#[salsa::tracked]
pub fn node_hierarchy_at(db: &dyn Database, file: File, at: Point) -> Vec<AstNode> {
    // depth-first search from the root node
    let mut cursor = Some(file.ast(db));

    // loop until nodes have no more children
    let mut stack = Vec::new();
    while let Some(node) = cursor {
        // add this node to the stack
        stack.push(node);

        // reset current node cursor
        cursor = None;

        // find children inside
        for child in node.children(db).iter() {
            // if this child's span contains the cursor, descend into it
            if child.span(db).contains(at) {
                cursor = Some(*child);
                break;
            }
        }
    }

    // return the complete stack
    stack
}
