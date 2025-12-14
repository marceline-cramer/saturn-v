import pytest
import subprocess, tempfile, time
from saturn_v_py import PyClient

nextPort = 4000

@pytest.fixture(scope="session")
def server_url():
    global nextPort
    db = tempfile.mkdtemp()
    port = nextPort
    nextPort += 1

    proc = subprocess.Popen([
        "cargo", "run", "-p", "saturn-v", "--", "server",
        "--host", f"127.0.0.1:{port}",
        "--db", db
    ])

    time.sleep(1)
    yield f"http://127.0.0.1:{port}"
    proc.terminate()

@pytest.fixture
def client(server_url):
    return PyClient(server_url)

@pytest.mark.asyncio
async def test_no_program(client):
    with pytest.raises(Exception):
        await client.get_program()


@pytest.mark.asyncio
async def test_update_program(client):
    # set and get default program
    prog = await client.get_program()  # expecting error first
    # TODO: implement set_program with default program JSON
    pass

@pytest.mark.asyncio
async def test_invalid_program(client):
    # TODO: send invalid program JSON and expect exception
    with pytest.raises(Exception):
        await client.set_program("invalid_json")

@pytest.mark.asyncio
async def test_list_inputs(client):
    # TODO: load passthru program, then list inputs
    pass

@pytest.mark.asyncio
async def test_no_input(client):
    # TODO: list invalid input operations
    pass

@pytest.mark.asyncio
async def test_input_ty_mismatch(client):
    # TODO: insert wrong type and expect exception
    pass

@pytest.mark.asyncio
async def test_input_operations(client):
    # TODO: test insert/remove operations
    pass

@pytest.mark.asyncio
async def test_list_outputs(client):
    # TODO: list outputs after loading program
    pass

@pytest.mark.asyncio
async def test_output_operations(client):
    # TODO: test get_all on outputs
    pass

@pytest.mark.asyncio
async def test_passthru(client):
    # TODO: test passthru functionality
    pass

@pytest.mark.asyncio
async def test_remove_fact(client):
    # TODO: test removing initial fact
    pass

@pytest.mark.asyncio
async def test_output_subscription(client):
    # TODO: test subscriptions
    pass

@pytest.mark.asyncio
async def test_subscription_no_output(client):
    # TODO: subscription on invalid output
    pass
    with pytest.raises(Exception):
        await client.get_program()
