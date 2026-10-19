"""Run the migrated Web executable and independent basic Lake consumer."""
import http.client
import json
from pathlib import Path
import signal
import socket
import subprocess
import tempfile
import time

from framework_e2e import free_port

ROOT = Path(__file__).resolve().parents[1]


def run(binary, basic=False):
    port = free_port()
    with tempfile.TemporaryDirectory(prefix="leanserver-web-") as temp:
        with (Path(temp) / "server.log").open("w+") as log:
            server = subprocess.Popen([str(binary), str(port)], cwd=temp, stdout=log, stderr=log)
            try:
                for _ in range(200):
                    if server.poll() is not None:
                        raise RuntimeError(f"Web server exited: {server.returncode}")
                    try:
                        with socket.create_connection(("127.0.0.1", port), timeout=.1):
                            break
                    except OSError:
                        time.sleep(.05)
                else:
                    raise RuntimeError("Web server did not listen")
                client = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
                try:
                    client.request("GET", "/health")
                    response = client.getresponse()
                    assert response.status == 200 and json.loads(response.read())["status"] in ("ok", "healthy")
                    client.request("GET", "/missing")
                    response = client.getresponse()
                    assert response.status == 404
                    response.read()
                    if basic:
                        body = 'a"b\nc'
                        client.request("POST", "/api/users", body=body)
                        response = client.getresponse()
                        assert response.status == 201 and json.loads(response.read())["echo"] == body
                    else:
                        client.request("GET", "/users/42?query=1")
                        response = client.getresponse()
                        assert response.status == 200 and json.loads(response.read())["sql"].endswith("id = 42")
                        client.request("DELETE", "/users/7")
                        response = client.getresponse()
                        assert response.status == 200 and json.loads(response.read())["sql"] == "DELETE FROM users WHERE id = 7"
                finally:
                    client.close()
            except Exception:
                log.flush()
                print((Path(temp) / "server.log").read_text()[-8000:])
                raise
            finally:
                server.send_signal(signal.SIGTERM)
                try:
                    server.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    server.kill()
                    server.wait()
                    raise RuntimeError("Web server failed to stop")
            assert server.returncode == 0
    symbols = subprocess.check_output(["nm", str(binary)], text=True)
    for forbidden in ["lean_crypto_", "lean_sqlite_", "lean_mysql_", "lean_pg_"]:
        assert forbidden not in symbols
    print(f"PASS {binary.name}: actual serving, migrated routes, JSON, shutdown, no optional native stubs")


if __name__ == "__main__":
    run(ROOT / ".lake/build/bin/webserver")
    run(ROOT / "examples/basic-server/.lake/build/bin/basic-server", basic=True)
