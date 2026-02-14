import asyncio
import json
import subprocess
import tempfile
import time

import pytest

from saturn_v_py import PyClient, connect

nextPort = 4000

def default_program_json() -> str:
    # saturn_v_protocol::Program is saturn_v_ir::Program<String>
    return json.dumps({"relations": {}, "constraints": []})


def passthru_program_json(*, fact: str | None = None) -> str:
    input_facts = []
    if fact is not None:
        input_facts = [[{"String": fact}]]

    # Matches the structure of `passthru_program()` from
    # `crates/server/src/api/tests.rs`.
    program = {
        "relations": {
            "Input": {
                "store": "Input",
                "stratum": 0,
                "ty": {"Primitive": "String"},
                "kind": "Basic",
                "io": "Input",
                "facts": input_facts,
                "rules": [],
            },
            "Output": {
                "store": "Output",
                "stratum": 0,
                "ty": {"Primitive": "String"},
                "kind": "Basic",
                "io": "Output",
                "facts": [],
                "rules": [
                    {
                        "head": [{"Variable": 0}],
                        "body": {
                            "vars": ["String"],
                            "loaded": ["Input"],
                            "instructions": {
                                "FromQuery": {
                                    "relation": 0,
                                    "terms": [{"Variable": 0}],
                                }
                            },
                        },
                    }
                ],
            },
        },
        "constraints": [],
    }

    # NOTE: keep formatting compact; server returns pretty JSON.
    return json.dumps(program)


async def load_passthru_program(client: PyClient, *, fact: str | None = None) -> None:
    await client.set_program(passthru_program_json(fact=fact))


@pytest.fixture
def server_url():
    global nextPort
    db = tempfile.mkdtemp()
    port = nextPort
    nextPort += 1

    # wait to compile CLI before running
    subprocess.Popen(["cargo", "build", "-p", "saturn-v"]).wait()

    # launch server
    proc = subprocess.Popen(
        [
            "cargo",
            "run",
            "-p",
            "saturn-v",
            "--",
            "server",
            "--host",
            f"127.0.0.1:{port}",
            "--db",
            db,
        ]
    )

    time.sleep(1)
    yield f"http://127.0.0.1:{port}"
    proc.terminate()


@pytest.fixture
def client(server_url):
    return await connect(server_url)


@pytest.mark.asyncio
async def test_no_program(client):
    with pytest.raises(RuntimeError, match="no program is loaded"):
        await client.get_program()


@pytest.mark.asyncio
async def test_update_program(client):
    await client.set_program(default_program_json())
    retrieved = await client.get_program()

    assert json.loads(retrieved) == json.loads(default_program_json())


@pytest.mark.asyncio
async def test_invalid_program(client):
    with pytest.raises(ValueError):
        await client.set_program("invalid_json")


@pytest.mark.asyncio
async def test_list_inputs(client):
    await load_passthru_program(client)
    inputs = await client.get_inputs()
    assert len(inputs) == 1
    assert inputs[0].name == "Input"
    assert isinstance(inputs[0].id, str) and inputs[0].id


@pytest.mark.asyncio
async def test_no_input(client):
    await load_passthru_program(client)
    with pytest.raises(RuntimeError, match=r"does not exist"):
        await client.get_input("NotAnInput")


@pytest.mark.asyncio
async def test_input_ty_mismatch(client):
    await load_passthru_program(client)
    input_rel = await client.get_input("Input")

    # Insert an integer where a String is expected.
    with pytest.raises(RuntimeError, match=r"type mismatch"):
        await input_rel.insert(47)


@pytest.mark.asyncio
async def test_input_operations(client):
    await load_passthru_program(client)
    input_rel = await client.get_input("Input")

    await input_rel.insert("test")
    await input_rel.remove("test")


@pytest.mark.asyncio
async def test_list_outputs(client):
    await load_passthru_program(client)
    outputs = await client.get_outputs()
    assert len(outputs) == 1
    assert outputs[0].name == "Output"
    assert isinstance(outputs[0].id, str) and outputs[0].id


@pytest.mark.asyncio
async def test_output_operations(client):
    await load_passthru_program(client)
    output_rel = await client.get_output("Output")
    values = await output_rel.get_all()
    assert values == []


@pytest.mark.asyncio
async def test_passthru(client):
    await load_passthru_program(client)

    input_rel = await client.get_input("Input")
    output_rel = await client.get_output("Output")

    await input_rel.insert("test")

    # Give the solver time to propagate.
    await asyncio.sleep(1)

    values = await output_rel.get_all()
    assert values == ["test"]


@pytest.mark.asyncio
async def test_remove_fact(client):
    fact = "Fact"
    await load_passthru_program(client, fact=fact)

    input_rel = await client.get_input("Input")
    output_rel = await client.get_output("Output")

    await asyncio.sleep(1)
    values = await output_rel.get_all()
    assert values == [fact], "fact not already present"

    await input_rel.remove(fact)

    await asyncio.sleep(1)
    values = await output_rel.get_all()
    assert values == [fact], "fact removed"


@pytest.mark.asyncio
async def test_output_subscription(client):
    pytest.skip("Python bindings do not expose output subscriptions")


@pytest.mark.asyncio
async def test_subscription_no_output(client):
    pytest.skip("Python bindings do not expose output subscriptions")
