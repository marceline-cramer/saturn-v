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
    sync::Arc,
};

use ropey::Rope;
use salsa::Setter;
use saturn_v_frontend::{AstNode, Children, Db, File, Point, Span, Workspace};
use tokio::sync::Mutex;
use tower_lsp::{jsonrpc::Result, lsp_types::*, LanguageServer};
use tree_sitter::{InputEdit, Language, Parser, Tree};

pub type EditorMap = HashMap<Url, Arc<Mutex<Editor>>>;

pub struct LspBackend {
    editors: Arc<Mutex<EditorMap>>,
    db: Mutex<Db>,
    workspace: Workspace,
    language: Language,
}

impl Default for LspBackend {
    fn default() -> Self {
        let db = Db::new();
        let workspace = Workspace::new(&db, HashMap::new());
        let language = Language::new(tree_sitter_kerolox::LANGUAGE);
        let editors = Default::default();

        LspBackend {
            editors,
            db: Mutex::new(db),
            workspace,
            language,
        }
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for LspBackend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::INCREMENTAL),
                        ..Default::default()
                    },
                )),
                ..Default::default()
            },
            server_info: Default::default(),
        })
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        // lock the database
        let mut db = self.db.lock().await;

        // create the editor struct
        let url = params.text_document.uri.clone();
        let ed = Editor::new(&mut db, &self.language, params.clone());

        // insert editor file into workspace
        let mut files = self.workspace.files(&*db).to_owned();
        files.insert(params.text_document.uri, ed.file);
        self.workspace.set_files(&mut *db).to(files);

        // add the editor into the map
        self.editors
            .lock()
            .await
            .insert(url, Arc::new(Mutex::new(ed)));
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.editors.lock().await.remove(&params.text_document.uri);

        let mut db = self.db.lock().await;
        let mut files = self.workspace.files(&*db).to_owned();
        files.remove(&params.text_document.uri);
        self.workspace.set_files(&mut *db).to(files);
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(ed) = self
            .editors
            .lock()
            .await
            .get_mut(&params.text_document.uri)
            .cloned()
        {
            let mut db = self.db.lock().await;
            ed.lock().await.on_change(&mut db, params);
        }
    }
}

pub struct Editor {
    contents: Rope,
    parser: Parser,
    tree: Tree,
    file: File,
}

impl Editor {
    /// Creates a new editor.
    pub fn new(db: &mut Db, language: &Language, params: DidOpenTextDocumentParams) -> Self {
        // initialize the tree-sitter parser and tree
        let mut parser = Parser::new();

        parser
            .set_language(language)
            .expect("failed to set parser language");

        let tree = parser
            .parse(&params.text_document.text, None)
            .expect("failed to create initial tree");

        // create the initial file
        let file = File::new(db, Default::default());

        // create the editor
        let mut ed = Self {
            contents: Rope::from_str(&params.text_document.text),
            parser,
            tree,
            file,
        };

        // update the AST for the initial text contents
        ed.update_ast(db);

        // done!
        ed
    }

    /// Handle text document change parameters.
    pub fn on_change(&mut self, db: &mut Db, params: DidChangeTextDocumentParams) {
        // push the changes into the content and current tree
        for change in params.content_changes.iter() {
            // TODO: send this as an error message to LSP client
            let _ = self.on_content_change(change);
        }

        // create a lookup function to access contiguous chunks of the contents
        let mut lookup = |byte, _position| {
            let (chunk, chunk_byte, _, _) = self.contents.chunk_at_byte(byte);
            let offset = byte - chunk_byte;
            &chunk.as_bytes()[offset..]
        };

        // update the parse tree
        self.tree = self
            .parser
            .parse_with_options(&mut lookup, Some(&self.tree), None)
            .expect("failed to parse");

        // update AST
        self.update_ast(db);
    }

    /// Handle a text document content change event.
    fn on_content_change(&mut self, ev: &TextDocumentContentChangeEvent) -> ropey::Result<()> {
        // fetch the range from the ev event
        let range = ev.range.as_ref().unwrap();

        // typecast all of the range variables to usize
        let start_row = range.start.line as usize;
        let start_col = range.start.character as usize;
        let end_row = range.end.line as usize;
        let end_col = range.end.character as usize;

        // get the character indices of the beginning of each line
        let start_line = self.contents.try_line_to_char(start_row)?;
        let end_line = self.contents.try_line_to_char(end_row)?;

        // calculate the character indices of the range
        let start_char = start_line + start_col;
        let end_char = end_line + end_col;

        // convert the character indices to byte indices
        // done before update to content
        let start_byte = self.contents.char_to_byte(start_char);
        let old_end_byte = self.contents.char_to_byte(end_char);

        // mutate the contents
        self.contents.try_remove(start_char..end_char)?;
        self.contents.insert(start_char, &ev.text);

        // locate the new ending position
        let new_end_byte = start_byte + ev.text.len();
        let new_end_row = self.contents.try_byte_to_line(new_end_byte)?;
        let new_end_char = self.contents.line_to_char(new_end_row);
        let new_end_col = self.contents.try_byte_to_char(new_end_byte)? - new_end_char;

        // edit the parse tree
        use tree_sitter::Point;
        self.tree.edit(&InputEdit {
            start_byte,
            old_end_byte,
            new_end_byte,
            start_position: Point {
                row: start_row,
                column: start_col,
            },
            old_end_position: Point {
                row: end_row,
                column: end_col,
            },
            new_end_position: Point {
                row: new_end_row,
                column: new_end_col,
            },
        });

        // success!
        Ok(())
    }

    /// Efficiently update inputs to the frontend with changes to the AST.
    pub fn update_ast(&mut self, db: &mut Db) {
        let mut cursor = self.tree.walk();
        let mut stack = vec![(None, cursor.node())];
        let mut keep = HashSet::new();
        let mut ast = self.file.ast(db).to_owned();

        while let Some((field, node)) = stack.pop() {
            // any node we encounter in the new tree should be preserved
            keep.insert(node.id());

            // convert the range type to a frontend span
            let span = Span {
                start: Point {
                    line: node.range().start_point.row,
                    column: node.range().start_point.column,
                },
                end: Point {
                    line: node.range().end_point.row,
                    column: node.range().end_point.column,
                },
            };

            // add it and its children
            let mut children = Children::new();
            for (idx, child) in node.children(&mut cursor).enumerate() {
                // look up the optional field name of the node
                let field = node.field_name_for_child(idx as u32);

                // add the children and be sure we process it
                children.push(child.id());
                stack.push((field, child));
            }

            // if the AST already contains this node, skip adding it. node
            // IDs change when their contents change, so this ensures that we
            // don't modify inputs unnecessarily. we do this after children are
            // iterated so that all of the descendants of old trees are kept
            // before we remove all unencountered nodes after this loop.
            if let Some(node) = ast.get(&node.id()) {
                // update the span of an existing node
                node.set_span(db).to(span);
                continue;
            }

            // if we don't have any children, get text contents of the AST node
            let contents = if children.is_empty() {
                Some(self.contents.byte_slice(node.byte_range()).to_string())
            } else {
                None
            };

            // create the AST node
            let symbol = node.grammar_name();
            let ast_node = AstNode::new(db, symbol, field, span, contents, children);

            // insert the AST node
            ast.insert(node.id(), ast_node);
        }

        // discard nodes that aren't in the latest tree
        ast.retain(|id, _node| keep.contains(id));

        // update the file ast
        self.file.set_ast(db).to(ast);
    }
}
