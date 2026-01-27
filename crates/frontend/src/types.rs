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
    fmt::{Debug, Display},
    ops::Deref,
};

use salsa::Update;
use strum::{Display, EnumString};

use crate::toplevel::AstNode;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WithAst<T> {
    /// The AST node corresponding to this object.
    pub ast: AstNode,

    /// The inner type whose AST is being tracked.
    pub inner: T,
}

impl<T> WithAst<T> {
    pub fn new(ast: AstNode, inner: T) -> Self {
        Self { ast, inner }
    }

    pub fn map<O>(self, cb: impl FnOnce(T) -> O) -> WithAst<O> {
        WithAst {
            ast: self.ast,
            inner: cb(self.inner),
        }
    }

    pub fn with<O>(&self, inner: O) -> WithAst<O> {
        WithAst {
            ast: self.ast,
            inner,
        }
    }
}

impl<T> Deref for WithAst<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> AsRef<T> for WithAst<T> {
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T: Debug> Debug for WithAst<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: Display> Display for WithAst<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

unsafe impl<T: Eq + Update> Update for WithAst<T> {
    unsafe fn maybe_update(old_pointer: *mut Self, new_value: Self) -> bool {
        let old: &mut Self = unsafe { &mut *old_pointer };
        let update = T::maybe_update(&mut old.inner, new_value.inner);
        let ast = old.ast != new_value.ast;
        old.ast = new_value.ast;
        update || ast
    }
}

#[derive(Copy, Clone, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, EnumString)]
pub enum PrimitiveType {
    Integer,
    Real,
    String,
    Boolean,
    Symbol,
}

impl From<saturn_v_ir::Type> for PrimitiveType {
    fn from(ir: saturn_v_ir::Type) -> Self {
        use saturn_v_ir::Type::*;
        match ir {
            Boolean => PrimitiveType::Boolean,
            Integer => PrimitiveType::Integer,
            Real => PrimitiveType::Real,
            Symbol => PrimitiveType::Symbol,
            String => PrimitiveType::String,
        }
    }
}

impl From<PrimitiveType> for saturn_v_ir::Type {
    fn from(ty: PrimitiveType) -> Self {
        use saturn_v_ir::Type::*;
        match ty {
            PrimitiveType::Boolean => Boolean,
            PrimitiveType::Integer => Integer,
            PrimitiveType::Real => Real,
            PrimitiveType::Symbol => Symbol,
            PrimitiveType::String => String,
        }
    }
}
