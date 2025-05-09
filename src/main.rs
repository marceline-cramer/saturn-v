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

use std::{collections::HashMap, path::PathBuf};

use clap::{Parser, Subcommand};
use saturn_v_frontend::{diagnostic::ReportCache, toplevel::Workspace};
use saturn_v_lsp::{Editor, LspBackend};
use tower_lsp::{LspService, Server};
use tree_sitter::Language;

#[derive(Parser)]
pub struct Args {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Run the Kerolox language server over stdio.
    Lsp,

    /// Checks a Kerolox source file.
    Check {
        /// The path to the source file.
        path: PathBuf,
    },
}

#[tokio::main]
async fn main() {
    let args = Args::parse();

    match args.command {
        Command::Lsp => {
            let stdin = tokio::io::stdin();
            let stdout = tokio::io::stdout();
            let (service, socket) = LspService::new(LspBackend::new);
            Server::new(stdin, stdout, socket).serve(service).await;
        }
        Command::Check { path } => {
            let mut db = saturn_v_frontend::toplevel::Db::new();
            let src = std::fs::read_to_string(&path).unwrap();
            let absolute_path = path.canonicalize().unwrap();
            let url = url::Url::from_file_path(absolute_path).unwrap();
            let language = Language::new(tree_sitter_kerolox::LANGUAGE);
            let ed = Editor::new(&mut db, url.clone(), &language, &src);
            let file = ed.get_file();

            let mut file_urls = HashMap::new();
            file_urls.insert(url, file);

            let workspace = Workspace::new(&db, file_urls);

            let diagnostics = saturn_v_frontend::check_all_diagnostics(&db, workspace);
            let mut cache = ReportCache::new(&db);
            let mut fatal_errors = 0;
            for d in diagnostics {
                if d.is_fatal() {
                    fatal_errors += 1;
                }

                for report in d.to_ariadne(&db) {
                    report.eprint(&mut cache).unwrap();
                }
            }

            eprintln!("finished with {fatal_errors} errors");

            if fatal_errors > 0 {
                eprintln!("check failed");
                return;
            }

            for rule in saturn_v_frontend::parse::file_rules(&db, file)
                .into_values()
                .flatten()
            {
                for body in saturn_v_frontend::infer::typed_rule(&db, rule)
                    .iter()
                    .flat_map(|rule| rule.bodies(&db))
                {
                    let expr = saturn_v_frontend::desugar::desugar_rule_body(
                        &db,
                        Default::default(),
                        body,
                    );

                    eprintln!("{expr:#?}");
                }
            }

            for constraint in saturn_v_frontend::parse::file_constraints(&db, file) {
                let typed = saturn_v_frontend::infer::typed_constraint(&db, constraint);

                let expr = saturn_v_frontend::desugar::desugar_rule_body(
                    &db,
                    Default::default(),
                    typed.body(&db),
                );

                eprintln!("{expr:#?}");
            }
        }
    }
}
