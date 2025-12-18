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

use std::sync::atomic::AtomicU32;

use anyhow::{Context, Result};
use futures_util::StreamExt;
use saturn_v_client::*;
use saturn_v_protocol::{ir::Type, *};

use super::*;

/// Spins up a local server and returns a client connected to it.
async fn local_client() -> Result<Client> {
    let _ = tracing_subscriber::fmt::try_init();

    static PORT: AtomicU32 = AtomicU32::new(3000);

    let port = PORT.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let database = Database::temporary().unwrap();
    let state = start_server(database).await?;
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
    let mut program = Program::default();

    program.insert_relation(ir::Relation {
        store: "Input".to_string(),
        ty: ir::StructuredType::Primitive(ir::Type::String),
        kind: ir::RelationKind::Basic,
        io: ir::RelationIO::Input,
        facts: vec![],
        rules: vec![],
    });

    program.insert_relation(ir::Relation {
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
    });

    program
}

#[tokio::test]
async fn test_no_program() -> Result<()> {
    let client = local_client().await?;
    let result = client.get_program().await;
    assert_eq!(server_error(result)?, ServerError::NoProgramLoaded);
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
    let mut program = Program::default();

    program.insert_relation(ir::Relation {
        store: "Invalid".to_string(),
        ty: StructuredType::Primitive(ir::Type::String),
        kind: ir::RelationKind::Basic,
        io: ir::RelationIO::None,
        facts: vec![vec![ir::Value::Integer(0)]],
        rules: vec![],
    });

    let client = local_client().await?;
    let result = client.set_program(&program).await;
    let expected_error = ServerError::InvalidProgram(program.validate().err().unwrap());
    assert_eq!(server_error(result)?, expected_error);
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
async fn test_no_input() -> Result<()> {
    let client = passthru_client().await?;
    let name = "NotAnInput".to_string();
    let ty = StructuredType::Primitive(Type::String);
    let input = client.get_invalid_input(&name, ty);
    let value = "test".to_string();
    let result = input.insert(value).await;
    assert_eq!(server_error(result)?, ServerError::NoSuchInput(name));
    Ok(())
}

#[tokio::test]
async fn test_input_ty_mismatch() -> Result<()> {
    let client = passthru_client().await?;
    let name = "Input".to_string();
    let ty = StructuredType::Primitive(Type::Integer);
    let input = client.get_invalid_input(&name, ty.clone());
    let value = 47;
    let result = input.insert(value).await;

    assert_eq!(
        server_error(result)?,
        ServerError::TypeMismatch {
            expected: StructuredType::Primitive(Type::String),
            got: ty
        }
    );

    Ok(())
}

#[tokio::test]
async fn test_input_operations() -> Result<()> {
    let client = passthru_client().await?;
    let input = client.get_input("Input").await?;
    let value = "test".to_string();
    input.insert(value.clone()).await?;
    input.remove(value).await?;
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
    let output = client.get_output("Output").await?;
    let values = output.get_all::<String>().await?;
    assert_eq!(values, Vec::<String>::new());
    Ok(())
}

#[tokio::test]
async fn test_passthru() -> Result<()> {
    let client = passthru_client().await?;

    let input = client.get_input("Input").await?;
    let value = "test".to_string();
    input.insert(value.clone()).await?;

    tokio::time::sleep(std::time::Duration::from_secs(1)).await;

    let output = client.get_output("Output").await?;
    let values = output.get_all::<String>().await?;
    assert_eq!(values, vec![value]);

    Ok(())
}

#[tokio::test]
async fn test_remove_fact() -> Result<()> {
    let client = local_client().await?;

    let fact = "Fact".to_string();

    let mut program = passthru_program();
    let relation = program.relations.get_mut("Input").unwrap();
    relation.facts.push(vec![ir::Value::String(fact.clone())]);

    client.set_program(&program).await?;

    let input = client.get_input("Input").await?;
    let output = client.get_output("Output").await?;

    tokio::time::sleep(std::time::Duration::from_secs(1)).await;
    let values = output.get_all::<String>().await?;
    assert_eq!(values, vec![fact.clone()], "fact not already present");

    input.remove(fact.clone()).await?;

    tokio::time::sleep(std::time::Duration::from_secs(1)).await;
    let values = output.get_all::<String>().await?;
    assert_eq!(values, vec![fact.clone()], "fact removed");

    Ok(())
}

#[tokio::test]
async fn test_output_subscription() -> Result<()> {
    let client = passthru_client().await?;
    let input = client.get_input("Input").await?;
    let output = client.get_output("Output").await?;
    let mut rx = output.subscribe()?;
    let value = "test".to_string();
    input.insert(value.clone()).await?;
    let received = rx.next().await.unwrap()?;
    assert_eq!(received, TupleUpdate::insert(value));
    Ok(())
}

#[tokio::test]
async fn test_subscription_no_output() -> Result<()> {
    let client = passthru_client().await?;
    let name = "NotAnOutput".to_string();
    let ty = StructuredType::Primitive(Type::String);
    let output = client.get_invalid_output(&name, ty);
    let mut rx = output.subscribe::<String>()?;
    let response = rx.next().await.unwrap();
    assert_eq!(server_error(response)?, ServerError::NoSuchOutput(name));
    Ok(())
}

/// Helper method to expect server errors from client results.
pub fn server_error<T>(result: saturn_v_client::Result<T>) -> Result<ServerError> {
    Ok(result.err().context("not an error")?.into_server_error()?)
}
