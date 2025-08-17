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
// along with Saturn V. If not, see <https://www.gnu.org/licenses>.

use std::{collections::HashMap, sync::atomic::AtomicU32};

use anyhow::{Context, Result};
use futures_util::StreamExt;
use saturn_v_client::*;
use saturn_v_ir as ir;

use super::*;

/// Spins up a local server and returns a client connected to it.
async fn local_client() -> Result<Client> {
    static PORT: AtomicU32 = AtomicU32::new(3000);

    let port = PORT.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let state = start_server();
    let router = route(state).into_make_service();
    let host = format!("localhost:{port}");
    let listener = tokio::net::TcpListener::bind(&host).await?;

    tokio::spawn(async move {
        axum::serve(listener, router).await.unwrap();
    });

    let url = format!("http://{host}").as_str().try_into().unwrap();
    let client = Client::new(url);
    Ok(client)
}

/// Spins up a local server and gives it [passthru_program].
async fn passthru_client() -> Result<Client> {
    let client = local_client().await?;

    client
        .set_program(&passthru_program())
        .await
        .context("failed to set passthru program")?;

    Ok(client)
}

/// Creates a basic program that feeds an input directly to an output.
fn passthru_program() -> Program {
    let mut relations = HashMap::new();

    relations.insert(
        "Input".to_string(),
        ir::Relation {
            store: "Input".to_string(),
            ty: ir::StructuredType::Primitive(ir::Type::String),
            kind: ir::RelationKind::Basic,
            io: ir::RelationIO::Input,
            facts: vec![],
            rules: vec![],
        },
    );

    relations.insert(
        "Output".to_string(),
        ir::Relation {
            store: "Output".to_string(),
            ty: ir::StructuredType::Primitive(ir::Type::String),
            kind: ir::RelationKind::Basic,
            io: ir::RelationIO::Output,
            facts: vec![],
            rules: vec![ir::Rule {
                head: vec![ir::QueryTerm::Variable(0)],
                body: ir::RuleBody {
                    vars: vec![ir::Type::String],
                    loaded: vec!["Input".to_string()],
                    instructions: ir::Instruction::FromQuery {
                        relation: 0,
                        terms: vec![ir::QueryTerm::Variable(0)],
                    },
                },
            }],
        },
    );

    saturn_v_ir::Program {
        relations,
        constraints: vec![],
    }
}

#[tokio::test]
async fn test_no_program() -> Result<()> {
    let client = local_client().await?;
    let result = client.get_program().await;
    assert!(result.is_err());
    Ok(())
}

#[tokio::test]
async fn test_update_program() -> Result<()> {
    let client = local_client().await?;
    let program = Program::default();
    client.set_program(&program).await?;
    let retrieved = client.get_program().await?;
    assert_eq!(program, retrieved);
    Ok(())
}

#[tokio::test]
async fn test_invalid_program() -> Result<()> {
    let program = Program {
        constraints: vec![],
        relations: vec![ir::Relation {
            store: "Invalid".to_string(),
            ty: StructuredType::Primitive(ir::Type::String),
            kind: ir::RelationKind::Basic,
            io: ir::RelationIO::None,
            facts: vec![vec![ir::Value::Integer(0)]],
            rules: vec![],
        }]
        .into_iter()
        .map(|rel| (rel.store.clone(), rel))
        .collect(),
    };

    let client = local_client().await?;
    let result = client.set_program(&program).await;
    assert!(result.is_err());
    Ok(())
}

#[tokio::test]
async fn test_switch_program() -> Result<()> {
    let client = local_client().await?;

    let program = Program::default();
    client.set_program(&program).await?;
    let retrieved = client.get_program().await?;
    assert_eq!(program, retrieved);

    let program = passthru_program();
    client.set_program(&program).await?;
    let retrieved = client.get_program().await?;
    assert_eq!(program, retrieved);

    Ok(())
}

#[tokio::test]
async fn test_list_inputs() -> Result<()> {
    let client = passthru_client().await?;
    let inputs = client.get_inputs().await?;
    assert_eq!(inputs.len(), 1);
    assert_eq!(inputs[0].name, "Input");
    Ok(())
}

#[tokio::test]
async fn test_input_operations() -> Result<()> {
    let client = passthru_client().await?;
    let input = client.get_input("Input").await?.unwrap();
    let value = "test".to_string();
    input.insert(&value).await?;
    input.remove(&value).await?;
    Ok(())
}

#[tokio::test]
async fn test_list_outputs() -> Result<()> {
    let client = passthru_client().await?;
    let outputs = client.get_outputs().await?;
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].name, "Output");
    Ok(())
}

#[tokio::test]
async fn test_output_operations() -> Result<()> {
    let client = passthru_client().await?;
    let output = client.get_output("Output").await?.unwrap();
    let values = output.get_all::<String>().await?;
    assert_eq!(values, Vec::<String>::new());
    Ok(())
}

#[tokio::test]
async fn test_passthru() -> Result<()> {
    let client = passthru_client().await?;

    let input = client.get_input("Input").await?.unwrap();
    let value = "test".to_string();
    input.insert(&value).await?;

    let output = client.get_output("Output").await?.unwrap();
    let values = output.get_all::<String>().await?;
    assert_eq!(values, vec![value]);

    Ok(())
}

#[tokio::test]
async fn test_output_subscription() -> Result<()> {
    let client = passthru_client().await?;
    let input = client.get_input("Input").await?.unwrap();
    let output = client.get_output("Output").await?.unwrap();
    let mut rx = output.subscribe().await?;
    let value = "test".to_string();
    input.insert(&value).await?;
    assert_eq!(rx.next().await, Some(value));
    Ok(())
}
