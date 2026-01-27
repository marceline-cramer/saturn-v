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
    any::TypeId,
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    ops::{Deref, Range},
    panic::UnwindSafe,
};

use ariadne::{Color, Label, Report, ReportKind};
use lsp_types::Diagnostic as LspDiagnostic;
use salsa::{Accumulator, Database};

use crate::{
    toplevel::{AstNode, File, Span},
    types::WithAst,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SimpleError {
    pub ast: AstNode,
    pub message: String,
}

impl SimpleError {
    pub fn new(ast: AstNode, message: impl ToString) -> Self {
        Self {
            ast,
            message: message.to_string(),
        }
    }
}

impl BasicDiagnostic for SimpleError {
    fn range(&self) -> Range<AstNode> {
        self.ast..self.ast
    }

    fn message(&self) -> String {
        self.message.clone()
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn source(&self) -> Option<String> {
        None
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

pub trait BasicDiagnostic: DynEq + UnwindSafe + Send + Sync + 'static {
    fn range(&self) -> Range<AstNode>;

    fn message(&self) -> String;

    fn kind(&self) -> DiagnosticKind;

    fn source(&self) -> Option<String> {
        None
    }

    fn notes(&self) -> Vec<WithAst<String>> {
        vec![]
    }

    fn is_fatal(&self) -> bool;
}

impl<T: BasicDiagnostic> Diagnostic for T {
    fn to_lsp(&self, db: &dyn Database) -> Vec<(File, LspDiagnostic)> {
        let message = LspDiagnostic {
            range: ast_span(db, self.range()).into(),
            severity: Some(self.kind().into()),
            source: self.source(),
            message: self.message(),
            ..Default::default()
        };

        let notes = self.notes().into_iter().map(|note| LspDiagnostic {
            range: ast_span(db, note.ast..note.ast).into(),
            severity: Some(lsp_types::DiagnosticSeverity::HINT),
            source: self.source(),
            message: note.inner,
            ..Default::default()
        });

        let file = self.range().start.file(db);
        notes.chain([message]).map(|d| (file, d)).collect()
    }

    fn to_ariadne(&self, db: &dyn Database) -> Vec<Report<'_, ReportSpan>> {
        // create span
        let span = ReportSpan {
            file: self.range().start.file(db),
            range: ast_to_range(db, self.range()),
        };

        // configure the report
        let config = ariadne::Config::new()
            .with_cross_gap(true)
            .with_compact(true);

        // pick color based on kind
        use DiagnosticKind::*;
        let (kind, color) = match self.kind() {
            Error => (ReportKind::Error, Color::Red),
            Warning => (ReportKind::Warning, Color::Yellow),
            Info => (ReportKind::Advice, Color::Green),
            Note => (ReportKind::Custom("note", Color::Blue), Color::Blue),
        };

        // create labels
        let labels = self.notes().clone().into_iter().map(|msg| {
            let span = ReportSpan {
                file: self.range().start.file(db),
                range: ast_to_range(db, msg.ast..msg.ast),
            };

            Label::new(span)
                .with_message(&msg.inner)
                .with_color(Color::Blue)
                .with_order(1)
        });

        // build report
        let report = Report::build(kind, span.clone())
            .with_config(config)
            .with_message(self.message())
            .with_label(Label::new(span).with_color(color))
            .with_labels(labels)
            .finish();

        // return only one report
        vec![report]
    }

    fn is_fatal(&self) -> bool {
        self.is_fatal()
    }
}

pub fn ast_to_range(db: &dyn Database, ast: Range<AstNode>) -> Range<usize> {
    // retrieve the file corresponding to the range
    let file = ast.start.file(db);
    assert!(file == ast.end.file(db), "AST node files do not match");

    // lookup the file source
    let src = file.contents(db);

    // calculate character offsets within file source
    let span = ast_span(db, ast);
    let start = src.line_to_char(span.start.line) + span.start.column;
    let end = src.line_to_char(span.end.line) + span.end.column;

    // return the total span
    start..end
}

pub fn ast_span(db: &dyn Database, ast: Range<AstNode>) -> Span {
    // look up the points corresponding to the span ends
    let start = ast.start.span(db).start;
    let end = ast.end.span(db).end;

    // combine them
    Span { start, end }
}

#[salsa::accumulator]
pub struct DynDiagnostic(pub Box<dyn Diagnostic>);

impl Deref for DynDiagnostic {
    type Target = dyn Diagnostic;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

pub trait AccumulateDiagnostic: Diagnostic + Sized {
    fn accumulate(self, db: &dyn Database);
}

impl<T: Diagnostic + Sized> AccumulateDiagnostic for T {
    fn accumulate(self, db: &dyn Database) {
        DynDiagnostic(Box::new(self)).accumulate(db);
    }
}

pub trait Diagnostic: DynEq + UnwindSafe + Send + Sync + 'static {
    fn to_lsp(&self, db: &dyn Database) -> Vec<(File, LspDiagnostic)>;
    fn to_ariadne(&self, db: &dyn Database) -> Vec<Report<'_, ReportSpan>>;
    fn is_fatal(&self) -> bool;
}

/// A trait to allow a value to be compared against value-erased others.
pub trait DynEq {
    fn dyn_eq(&self) -> (TypeId, u64);
}

impl<T: Hash + 'static> DynEq for T {
    fn dyn_eq(&self) -> (TypeId, u64) {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        (TypeId::of::<T>(), hasher.finish())
    }
}

/// The kind (severity, level, etc.) of a diagnostic.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DiagnosticKind {
    Error,
    Warning,
    Info,
    Note,
}

impl From<DiagnosticKind> for lsp_types::DiagnosticSeverity {
    fn from(kind: DiagnosticKind) -> Self {
        use lsp_types::DiagnosticSeverity;
        use DiagnosticKind::*;
        match kind {
            Error => DiagnosticSeverity::ERROR,
            Warning => DiagnosticSeverity::WARNING,
            Info => DiagnosticSeverity::INFORMATION,
            Note => DiagnosticSeverity::HINT,
        }
    }
}

/// Custom Ariadne type for reporting spans.
///
/// Ariadne would blanket-impl for (File, Range<usize>) except that File does
/// not implement Debug, therefore this is necessary.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ReportSpan {
    pub file: File,
    pub range: Range<usize>,
}

impl ariadne::Span for ReportSpan {
    type SourceId = File;

    fn source(&self) -> &Self::SourceId {
        &self.file
    }

    fn start(&self) -> usize {
        self.range.start
    }

    fn end(&self) -> usize {
        self.range.end
    }
}

/// Custom Ariadne type to implement `Cache` with [File].
///
/// [File] doesn't implement [Display], so a manual implementation is needed.
pub struct ReportCache<'db> {
    /// The database to look up file properties with.
    db: &'db dyn Database,

    /// The cache of file strings.
    files: HashMap<File, ariadne::Source<String>>,
}

impl ariadne::Cache<File> for ReportCache<'_> {
    type Storage = String;

    fn fetch(&mut self, id: &File) -> Result<&ariadne::Source<String>, impl std::fmt::Debug> {
        Ok::<_, ()>(self.files.entry(*id).or_insert_with(|| {
            let contents = id.contents(self.db).to_string();
            ariadne::Source::from(contents)
        }))
    }

    fn display<'a>(&self, id: &'a File) -> Option<impl std::fmt::Display + 'a> {
        Some(id.url(self.db).clone())
    }
}

impl<'db> ReportCache<'db> {
    /// Creates an empty report cache.
    pub fn new(db: &'db dyn Database) -> Self {
        Self {
            db,
            files: HashMap::new(),
        }
    }
}
