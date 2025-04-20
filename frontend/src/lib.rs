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

use std::collections::HashMap;

use smallvec::SmallVec;

pub use salsa::DatabaseImpl as Db;

#[salsa::input]
pub struct Workspace {
    #[return_ref]
    pub files: HashMap<String, File>,
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
    pub contents: Option<String>,
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
