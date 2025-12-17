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

use std::{collections::HashMap, ops::DerefMut, sync::Arc};

use ropey::Rope;
use salsa::{AsDynDatabase, Setter};
use saturn_v_frontend::{
    file_inlay_hints,
    locate::{entity, entity_info},
    toplevel::{AstNode, Children, Db, File, Point, Span, Workspace},
};
use tokio::sync::Mutex;
use tower_lsp::{
    jsonrpc::{Error, Result},
    lsp_types::{
        request::{GotoImplementationParams, GotoImplementationResponse},
        *,
    },
    Client, LanguageServer, LspService, Server,
};
use tree_sitter::{InputEdit, Language, Node, Parser, Tree};

/// Wasm bindings to the language server.
pub mod wasm;

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
        let stdlib = Default::default();
        let workspace = Workspace::new(&db, HashMap::new(), stdlib);
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

    pub async fn get_file_params(
        &self,
        params: &TextDocumentPositionParams,
    ) -> Result<impl DerefMut<Target = Editor> + 'static> {
        self.get_file(&params.text_document.uri).await
    }

    pub async fn get_file(&self, uri: &Url) -> Result<impl DerefMut<Target = Editor> + 'static> {
        let ed = self
            .editors
            .lock()
            .await
            .get(uri)
            .cloned()
            .ok_or_else(|| Error::invalid_params("file's editor was not loaded"))?;

        Ok(ed.lock_owned().await)
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
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(false),
                    trigger_characters: Some(vec![",".to_string()]),
                    work_done_progress_options: Default::default(),
                    all_commit_characters: None,
                    completion_item: Some(CompletionOptionsCompletionItem {
                        label_details_support: Some(true),
                    }),
                }),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Left(true)),
                inlay_hint_provider: Some(OneOf::Left(true)),
                implementation_provider: Some(ImplementationProviderCapability::Simple(true)),
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
            .get_file_params(&params.text_document_position_params)
            .await?;
        let db = self.db.lock().await;
        ed.hover(&db, params)
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let ed = self.get_file_params(&params.text_document_position).await?;
        let db = self.db.lock().await;
        let at = params.text_document_position.position.into();
        let items = saturn_v_frontend::completion(db.as_dyn_database(), ed.file, at);
        Ok(items.map(CompletionResponse::Array))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let ed = self
            .get_file_params(&params.text_document_position_params)
            .await?;
        let db = self.db.lock().await;
        let at = params.text_document_position_params.position.into();

        let Some(e) = entity(db.as_dyn_database(), ed.file, at) else {
            return Ok(None);
        };

        let info = entity_info(db.as_dyn_database(), e);

        Ok(info
            .def
            .map(|ast| ast.location(db.as_dyn_database()))
            .map(GotoDefinitionResponse::Scalar))
    }

    async fn goto_implementation(
        &self,
        params: GotoImplementationParams,
    ) -> Result<Option<GotoImplementationResponse>> {
        let ed = self
            .get_file_params(&params.text_document_position_params)
            .await?;

        let db = self.db.lock().await;
        let at = params.text_document_position_params.position.into();

        let Some(e) = entity(db.as_dyn_database(), ed.file, at) else {
            return Ok(None);
        };

        let info = entity_info(db.as_dyn_database(), e);

        if info.implementations.is_empty() {
            return Ok(None);
        }

        Ok(Some(GotoDefinitionResponse::Array(
            info.implementations
                .into_iter()
                .map(|ast| ast.location(db.as_dyn_database()))
                .collect(),
        )))
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let ed = self.get_file_params(&params.text_document_position).await?;
        let db = self.db.lock().await;
        let at = params.text_document_position.position.into();

        let Some(e) = entity(db.as_dyn_database(), ed.file, at) else {
            return Ok(None);
        };

        let info = entity_info(db.as_dyn_database(), e);

        Ok(Some(
            info.references
                .into_iter()
                .map(|ast| ast.location(db.as_dyn_database()))
                .collect(),
        ))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let ed = self.get_file_params(&params.text_document_position).await?;
        Ok(None)
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let ed = self.get_file(&params.text_document.uri).await?;
        let db = self.db.lock().await;
        let hints = file_inlay_hints(db.as_dyn_database(), ed.file);

        Ok(Some(
            hints
                .into_iter()
                .map(|(ast, label)| InlayHint {
                    position: ast.span(db.as_dyn_database()).end.into(),
                    label: InlayHintLabel::String(label),
                    kind: Some(InlayHintKind::TYPE),
                    text_edits: None,
                    tooltip: None,
                    padding_left: None,
                    padding_right: None,
                    data: None,
                })
                .collect(),
        ))
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
            // can't pass through result, so dedicated message needs to be sent
            // alternatively it could just log or panic
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
        // if `range` is None, the client replaced the whole document
        if ev.range.is_none() {
            // replace the entire contents
            self.contents = Rope::from_str(&ev.text);

            // reparse from scratch
            self.tree = self
                .parser
                .parse(&ev.text, None)
                .expect("failed to reparse document");

            return Ok(());
        }

        // fetch the range from the ev event (we already handled None above)
        let range = ev.range.as_ref().unwrap();

        // LSP positions are UTF-16 code unit columns; convert them into rope char indices.
        let start_row = range.start.line as usize;
        let start_col = range.start.character as usize;
        let end_row = range.end.line as usize;
        let end_col = range.end.character as usize;

        // get the character indices of the beginning of each line
        let start_line_char = self.contents.try_line_to_char(start_row)?;
        let end_line_char = self.contents.try_line_to_char(end_row)?;

        // determine end-of-line char indices (for clamping)
        let next_line_after_start = match self.contents.try_line_to_char(start_row + 1) {
            Ok(v) => v,
            Err(_) => self.contents.len_chars(),
        };
        let next_line_after_end = match self.contents.try_line_to_char(end_row + 1) {
            Ok(v) => v,
            Err(_) => self.contents.len_chars(),
        };

        // compute absolute char indices for start/end by mapping UTF-16 columns
        let start_char = self.col_to_char(start_line_char, next_line_after_start, start_col);
        let end_char = self.col_to_char(end_line_char, next_line_after_end, end_col);

        // compute column values (UTF-16 columns) for start and old end to feed into InputEdit
        let start_col_char = self.utf16_column(start_line_char, start_char)?;
        let old_end_col_char = self.utf16_column(end_line_char, end_char)?;

        // convert the character indices to byte indices (before mutating the rope)
        let start_byte = self.contents.char_to_byte(start_char);
        let old_end_byte = self.contents.char_to_byte(end_char);

        // perform the edit on the rope
        self.contents.try_remove(start_char..end_char)?;
        self.contents.insert(start_char, &ev.text);

        // compute the new end byte after insertion
        let new_end_byte = start_byte + ev.text.len();

        // derive new_end_row and new_end_col (in char units) from the new_end_byte
        let new_end_row = self.contents.try_byte_to_line(new_end_byte)?;
        let new_end_row_start_char = self.contents.try_line_to_char(new_end_row)?;
        let new_end_char = self.contents.try_byte_to_char(new_end_byte)?;
        let new_end_col = self.utf16_column(new_end_row_start_char, new_end_char)?;

        // edit the parse tree with correct byte + char positions
        use tree_sitter::Point;
        self.tree.edit(&InputEdit {
            start_byte,
            old_end_byte,
            new_end_byte,
            start_position: Point {
                row: start_row,
                column: start_col_char,
            },
            old_end_position: Point {
                row: end_row,
                column: old_end_col_char,
            },
            new_end_position: Point {
                row: new_end_row,
                column: new_end_col,
            },
        });

        Ok(())
    }

    // Map an LSP UTF-16 column value into a Rope char index inside the given line.
    // `line_start_char` and `line_end_char` are absolute char indices for the start of the
    // line and the start of the next line (used to clamp the computation).
    fn col_to_char(
        &self,
        line_start_char: usize,
        line_end_char: usize,
        mut utf16_col: usize,
    ) -> usize {
        let mut offset = 0usize;
        while line_start_char + offset < line_end_char {
            let ch = self.contents.char(line_start_char + offset);
            let units = ch.len_utf16();
            if utf16_col == 0 {
                break;
            }
            if utf16_col < units {
                // requested column falls inside this char; clamp to this char index
                break;
            }
            utf16_col = utf16_col.saturating_sub(units);
            offset += 1;
        }
        line_start_char + offset
    }

    /// Calculates the UTF-16 codepoint column of a given char index in the rope.
    fn utf16_column(&self, line_start_char: usize, target_char: usize) -> ropey::Result<usize> {
        self.contents
            .get_slice(line_start_char..target_char)
            .map(|slice| slice.len_utf16_cu())
            .ok_or(ropey::Error::CharIndexOutOfBounds(
                line_start_char,
                target_char,
            ))
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

            // update children and fields so the AST reflects the current tree
            ast_node.set_children(db).to(children);
            ast_node.set_fields(db).to(fields);

            // add this node to the new AST
            new_ast.insert(node.id(), *ast_node);

            // return this node
            return *ast_node;
        }

        // create the AST node
        let symbol = node.grammar_name();
        let ast_node = AstNode::new(db, self.file, node.id(), symbol, span, children, fields);

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
