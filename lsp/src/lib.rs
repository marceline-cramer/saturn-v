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

use std::{collections::HashMap, sync::Arc};

use ropey::Rope;
use salsa::Setter;
use saturn_v_frontend::toplevel::{AstNode, Children, Db, File, Point, Span, Workspace};
use tokio::sync::Mutex;
use tower_lsp::{jsonrpc::Result, lsp_types::*, Client, LanguageServer};
use tree_sitter::{InputEdit, Language, Node, Parser, Tree};

pub type EditorMap = HashMap<Url, Arc<Mutex<Editor>>>;

pub struct LspBackend {
    client: Client,
    editors: Arc<Mutex<EditorMap>>,
    db: Mutex<Db>,
    workspace: Workspace,
    language: Language,
}

impl LspBackend {
    pub fn new(client: Client) -> Self {
        let db = Db::new();
        let workspace = Workspace::new(&db, HashMap::new());
        let language = Language::new(tree_sitter_kerolox::LANGUAGE);
        let editors = Default::default();

        LspBackend {
            client,
            editors,
            db: Mutex::new(db),
            workspace,
            language,
        }
    }
}

impl LspBackend {
    pub async fn update_diagnostics(&self) {
        // lock the database
        let db = self.db.lock().await;

        // load all workspace diagnostics
        let diagnostics = saturn_v_frontend::check_all_diagnostics(&*db, self.workspace);

        // convert the diagnostics into a set of LSP diagnostics
        let diagnostics = diagnostics.into_iter().flat_map(|d| d.to_lsp(&*db));

        // batch diagnostics by file
        let mut by_file: HashMap<_, Vec<_>> = HashMap::new();
        for (file, d) in diagnostics {
            by_file.entry(file).or_default().push(d);
        }

        // even if a file doesn't receive diagnostics, publish them
        for ed in self.editors.lock().await.values() {
            let ed = ed.lock().await;
            by_file.entry(ed.file).or_default();
        }

        // update all diagnostics
        for (file, diagnostics) in by_file {
            let url = file.url(&*db).clone();

            self.client
                .publish_diagnostics(url, diagnostics, None)
                .await;
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
                hover_provider: Some(HoverProviderCapability::Simple(true)),
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
        let ed = Editor::new(
            &mut db,
            self.workspace,
            url.clone(),
            &self.language,
            &params.text_document.text,
        );

        // insert editor file into workspace
        let mut files = self.workspace.files(&*db).to_owned();
        files.insert(params.text_document.uri, ed.file);
        self.workspace.set_files(&mut *db).to(files);

        // add the editor into the map
        self.editors
            .lock()
            .await
            .insert(url, Arc::new(Mutex::new(ed)));

        // unlock database and update diagnostics
        drop(db);
        self.update_diagnostics().await;
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

        // update diagnostics
        self.update_diagnostics().await;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let ed = self
            .editors
            .lock()
            .await
            .get(&params.text_document_position_params.text_document.uri)
            .cloned();

        let Some(ed) = ed else { return Ok(None) };

        let db = self.db.lock().await;
        let hover = ed.lock().await.hover(&db, params);
        hover
    }
}

pub struct Editor {
    contents: Rope,
    parser: Parser,
    tree: Tree,
    file: File,
    ast: HashMap<usize, AstNode>,
}

impl Editor {
    /// Creates a new editor.
    pub fn new(
        db: &mut Db,
        workspace: Workspace,
        url: Url,
        language: &Language,
        text: &str,
    ) -> Self {
        // initialize the tree-sitter parser and tree
        let mut parser = Parser::new();

        parser
            .set_language(language)
            .expect("failed to set parser language");

        let tree = parser
            .parse(text, None)
            .expect("failed to create initial tree");

        // create the initial file
        let contents = Rope::from_str(text);
        let file = File::new(db, workspace, contents.clone(), url, None);

        // create the editor
        let mut ed = Self {
            contents,
            parser,
            tree,
            file,
            ast: HashMap::new(),
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

        // update the text contents
        self.file.set_contents(db).to(self.contents.clone());

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
        let mut new_ast = HashMap::new();
        let new_root = self.add_node(db, &mut new_ast, self.tree.root_node());
        self.file.set_root(db).to(Some(new_root));
        self.ast = new_ast;
    }

    fn add_node(&self, db: &mut Db, new_ast: &mut HashMap<usize, AstNode>, node: Node) -> AstNode {
        // add the node's children
        let mut children = Children::default();
        let mut fields = Vec::new();
        let mut cursor = node.walk();
        for (idx, child) in node.children(&mut cursor).enumerate() {
            // add the node
            let child = self.add_node(db, new_ast, child);

            // push the child to the list
            children.push(child);

            // add the field, if it exists
            if let Some(field) = node.field_name_for_child(idx as u32) {
                fields.push((field, child));
            }
        }

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

        // if our AST already contains this node, skip adding it. node
        // IDs change when their contents change, so this ensures that we
        // don't modify inputs unnecessarily. we do this after children are
        // iterated so that all of the descendants of old trees are kept
        // before we remove all unencountered nodes after this loop.
        if let Some(ast_node) = self.ast.get(&node.id()) {
            // update the span of an existing node
            ast_node.set_span(db).to(span);

            // add this node to the new AST
            new_ast.insert(node.id(), *ast_node);

            // return this node
            return *ast_node;
        }

        // if we don't have any fields, get text contents of the AST node
        let contents = if fields.is_empty() {
            Some(self.contents.byte_slice(node.byte_range()).to_string())
        } else {
            None
        };

        // create the AST node
        let symbol = node.grammar_name();
        let ast_node = AstNode::new(
            db,
            self.file,
            node.id(),
            symbol,
            span,
            contents,
            children,
            fields,
        );

        // insert the AST node into the new AST
        new_ast.insert(node.id(), ast_node);

        // return the initialized node
        ast_node
    }

    pub fn hover(&self, db: &Db, params: HoverParams) -> Result<Option<Hover>> {
        Ok(saturn_v_frontend::hover(
            db,
            self.file,
            params.text_document_position_params.position.into(),
        )
        .map(|(range, contents)| Hover {
            contents: HoverContents::Scalar(MarkedString::String(contents)),
            range: Some(range.into()),
        }))
    }

    /// Retrieves the handle to the editor's file.
    pub fn get_file(&self) -> File {
        self.file
    }

    /// Retrieves an immutable reference to this editor's contents.
    pub fn get_contents(&self) -> &Rope {
        &self.contents
    }
}
