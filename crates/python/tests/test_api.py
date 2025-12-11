import pytest
import subprocess, tempfile, time
from saturn_v_py import PyClient

@pytest.fixture(scope="session")
def server_url():
    db = tempfile.mkdtemp()
    port = "4001"
    proc = subprocess.Popen([
        "cargo", "run", "-p", "cli", "--", "Server",
        "--host", f"127.0.0.1:{port}",
        "--db", db
    ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
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
