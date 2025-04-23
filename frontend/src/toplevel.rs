use std::collections::HashMap;

use salsa::Database;
use smallvec::SmallVec;

use url::Url;

pub use salsa::DatabaseImpl as Db;

#[salsa::input]
pub struct Workspace {
    #[return_ref]
    pub files: HashMap<Url, File>,
}

#[salsa::input]
pub struct File {
    #[return_ref]
    pub ast: HashMap<usize, AstNode>,
}

#[salsa::input]
pub struct AstNode {
    pub symbol: &'static str,
    pub field: Option<&'static str>,
    pub span: Span,
    #[return_ref]
    pub contents: Option<String>,
    #[return_ref]
    pub children: Children,
}

pub type Children = SmallVec<[usize; 4]>;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: Point,
    pub end: Point,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Point {
    pub line: usize,
    pub column: usize,
}

#[salsa::tracked]
pub fn node_parents(db: &dyn Database, file: File) -> HashMap<usize, usize> {
    file.ast(db)
        .iter()
        .flat_map(|(parent, node)| node.children(db).iter().map(|child| (*child, *parent)))
        .collect()
}
