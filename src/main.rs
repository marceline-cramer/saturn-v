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
use salsa::Setter;
use saturn_v_frontend::{diagnostic::ReportCache, toplevel::Workspace};
use saturn_v_lsp::{Editor, LspBackend};
use tower_lsp::{LspService, Server};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
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

    /// Runs a Kerolox source file.
    Run {
        /// The path to the source file.
        path: PathBuf,
    },
}

#[tokio::main]
async fn main() {
    let args = Args::parse();

    let fmt_layer = tracing_subscriber::fmt::layer();

    let env_filter = tracing_subscriber::EnvFilter::builder()
        .with_env_var("SATURN_V_LOG")
        .with_default_directive("saturn_v=debug".parse().unwrap())
        .from_env()
        .expect("failed to parse logging directives");

    tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt_layer)
        .init();

    match args.command {
        Command::Lsp => {
            let stdin = tokio::io::stdin();
            let stdout = tokio::io::stdout();
            let (service, socket) = LspService::new(LspBackend::new);
            Server::new(stdin, stdout, socket).serve(service).await;
        }
        Command::Check { path } => {
            let Some(program) = build_file(&path) else {
                return;
            };

            eprintln!("{program:#?}");

            if let Err(err) = program.validate() {
                eprintln!("{err}");
            }
        }
        Command::Run { path } => {
            let Some(program) = build_file(&path) else {
                return;
            };

            let loader = saturn_v_eval::load::Loader::load_program(&program);
            saturn_v_eval::run(loader).await;
        }
    }
}

pub fn build_file(path: &PathBuf) -> Option<saturn_v_ir::Program<String>> {
    let mut db = saturn_v_frontend::toplevel::Db::new();
    let src = std::fs::read_to_string(path).unwrap();
    let absolute_path = path.canonicalize().unwrap();
    let url = url::Url::from_file_path(absolute_path).unwrap();
    let language = Language::new(tree_sitter_kerolox::LANGUAGE);

    let mut file_urls = HashMap::new();
    let workspace = Workspace::new(&db, file_urls.clone());

    let ed = Editor::new(&mut db, workspace, url.clone(), &language, &src);
    let file = ed.get_file();

    file_urls.insert(url, file);
    workspace.set_files(&mut db).to(file_urls);

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
        return None;
    }

    // TODO: relation names should be mangled in programs with more than one file
    let program = saturn_v_frontend::lower::lower_workspace(&db, workspace)
        .map_relations(|def| def.name(&db).inner.to_string());

    // return built program
    Some(program)
}
