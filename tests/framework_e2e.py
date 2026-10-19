"""Network regression gate. Server binary must be built by Lake first.

Run with --tls when openssl and an HTTP/3-enabled curl are on PATH.
OpenSSL is a test certificate/client dependency, never a server link dependency.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import http.client
import json
import os
from pathlib import Path
import signal
import socket
import ssl
import subprocess
import tempfile
import time
import zlib

ROOT = Path(__file__).resolve().parents[1]


def free_port():
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def curl(port, protocol, path="/", headers=(), body=None):
    command = ["curl", "--noproxy", "*", "--silent", "--show-error", "--insecure",
               "--max-time", "30", protocol, "-w", "\n%{http_code} %{http_version}"]
    for header in headers:
        command += ["-H", header]
    if body is not None:
        command += ["--data-binary", "@-"]
    command += [f"https://127.0.0.1:{port}{path}"]
    result = subprocess.run(command, input=body, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"curl {protocol} {path}: {result.stderr.decode(errors='replace')}")
    payload, metadata = result.stdout.rsplit(b"\n", 1)
    status, version = metadata.decode().split()
    return int(status), version, payload


def test_plain(port):
    connection = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
    for headers, status, expected in [({"A": "first:second"}, 200, b"first:second"),
                                      ({"a": "lowercase"}, 200, b"lowercase"),
                                      ({}, 400, b"Missing header A"), ({"A": ""}, 200, b"")]:
        connection.request("GET", "/", headers=headers)
        response = connection.getresponse()
        assert (response.status, response.read()) == (status, expected)
    binary = bytes(range(256)) * 130
    connection.request("POST", "/binary", body=binary)
    response = connection.getresponse()
    assert response.status == 200 and response.read() == binary
    connection.request("POST", "/binary", body=iter([binary[:100], binary[100:]]), encode_chunked=True)
    response = connection.getresponse()
    assert response.status == 200 and response.read() == binary
    for path, status, body in [("/environment", 200, b"effect environment"),
                               ("/error", 500, b"Internal Server Error"),
                               ("/invalid", 500, b"Internal Server Error"),
                               ("/large", 200, b"x" * 100000)]:
        connection.request("GET", path)
        response = connection.getresponse()
        assert (response.status, response.read()) == (status, body)
    connection.request("GET", "/cookies")
    response = connection.getresponse()
    assert [v for k, v in response.getheaders() if k.lower() == "set-cookie"] == ["a=1", "b=2"]
    response.read()
    for encoding, decode in [("gzip", gzip.decompress), ("deflate", zlib.decompress)]:
        connection.request("POST", "/compressed-binary", body=binary, headers={"Accept-Encoding": encoding})
        response = connection.getresponse()
        payload = response.read()
        assert response.status == 200 and response.getheader("content-encoding") == encoding
        assert decode(payload) == binary
    connection.request("GET", "/compressed", headers={"Accept-Encoding": "gzip;q=0"})
    response = connection.getresponse()
    assert response.getheader("content-encoding") is None and response.read() == b"x" * 70000
    connection.request("OPTIONS", "/", headers={"Origin": "https://example.com", "Access-Control-Request-Method": "POST"})
    response = connection.getresponse()
    assert response.status == 204 and response.getheader("access-control-allow-origin") == "https://example.com"
    assert response.read() == b""
    connection.request("GET", "/users/42?x=1")
    response = connection.getresponse()
    assert response.status == 200 and json.loads(response.read())["sql"] == "SELECT * FROM users WHERE id = 42"
    connection.close()

    def request_id(index):
        client = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
        try:
            headers = {"X-Request-Id": f"request-{index}"} if index % 2 == 0 else {}
            client.request("GET", "/request-id", headers=headers)
            response = client.getresponse()
            identifier = response.read().decode()
            assert response.status == 200 and identifier == response.getheader("x-request-id")
            if headers:
                assert identifier == headers["X-Request-Id"]
            return identifier
        finally:
            client.close()

    with ThreadPoolExecutor(max_workers=8) as executor:
        identifiers = list(executor.map(request_id, range(32)))
    assert len(set(identifiers)) == 32
    with socket.create_connection(("127.0.0.1", port), timeout=10) as sock:
        wire = b"GET / HTTP/1.1\r\nHost: localhost\r\nA: fragmented\r\nConnection: close\r\n\r\n"
        for byte in wire:
            sock.sendall(bytes([byte]))
        data = b""
        while chunk := sock.recv(4096):
            data += chunk
        assert data.endswith(b"fragmented") and data.startswith(b"HTTP/1.1 200")
    print("PASS plaintext: headers, keepalive, binary/chunked bodies, effects, exceptions, fragmentation")
    print("PASS Web middleware: CORS preflight, SQL parameter route, binary gzip/zlib, concurrent request IDs")


def test_h2_window(port):
    """Start with a closed stream window, then open it after receiving HEADERS."""
    context = ssl._create_unverified_context()
    context.set_alpn_protocols(["h2"])
    with socket.create_connection(("127.0.0.1", port), timeout=10) as tcp:
        with context.wrap_socket(tcp, server_hostname="localhost") as sock:
            assert sock.selected_alpn_protocol() == "h2"

            def send(kind, flags, stream, payload=b""):
                sock.sendall(len(payload).to_bytes(3, "big") + bytes([kind, flags]) +
                             stream.to_bytes(4, "big") + payload)

            def exact(size):
                result = b""
                while len(result) < size:
                    part = sock.recv(size - len(result))
                    if not part:
                        raise RuntimeError("HTTP/2 closed before END_STREAM")
                    result += part
                return result

            def receive():
                header = exact(9)
                return header[3], header[4], int.from_bytes(header[5:], "big"), exact(int.from_bytes(header[:3], "big"))

            sock.sendall(b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n")
            send(4, 0, 0, b"\x00\x04\x00\x00\x00\x00")
            # HPACK static method/scheme; literal path and authority.
            send(1, 5, 1, b"\x82\x87\x04\x06/large\x01\x09localhost")
            while True:
                kind, flags, stream, payload = receive()
                if kind == 4 and not flags & 1:
                    send(4, 1, 0)
                if kind == 1 and stream == 1:
                    break
                assert kind != 0, "DATA sent with zero stream window"
            sock.settimeout(.2)
            try:
                while True:
                    kind, _, _, payload = receive()
                    assert kind != 0 or not payload, "DATA sent with zero stream window"
            except TimeoutError:
                pass
            sock.settimeout(10)
            send(8, 0, 0, (100000).to_bytes(4, "big"))
            send(8, 0, 1, (100000).to_bytes(4, "big"))
            body = b""
            while True:
                kind, flags, stream, payload = receive()
                if kind == 0 and stream == 1:
                    body += payload
                    if flags & 1:
                        break
            assert body == b"x" * 100000
    print("PASS HTTP/2: zero initial window, WINDOW_UPDATE, complete 100 KB response")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tls", action="store_true")
    parser.add_argument("--skip-http3", action="store_true", help="For clients built without HTTP/3")
    parser.add_argument("--server", type=Path, default=ROOT / ".lake/build/bin/framework_server")
    args = parser.parse_args()
    server_binary = args.server.resolve()
    with tempfile.TemporaryDirectory(prefix="leanserver-e2e-") as temp:
        port = free_port()
        command = [str(server_binary), str(port)]
        if args.tls:
            cert, key = str(Path(temp) / "cert.pem"), str(Path(temp) / "key.pem")
            subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
                            "-keyout", key, "-out", cert, "-days", "1", "-subj", "/CN=localhost"],
                           check=True, capture_output=True)
            command += [cert, key]
        log_path = Path(temp) / "server.log"
        with log_path.open("w+") as log:
            server = subprocess.Popen(command, cwd=temp, stdout=log, stderr=log)
            try:
                deadline = time.monotonic() + 20
                while time.monotonic() < deadline:
                    if server.poll() is not None:
                        raise RuntimeError(f"server exited: {server.returncode}")
                    try:
                        with socket.create_connection(("127.0.0.1", port), timeout=.2):
                            break
                    except OSError:
                        time.sleep(.05)
                else:
                    raise RuntimeError("server did not start")
                test_plain(port)
                if args.tls:
                    test_h2_window(port)
                    protocols = [("--http1.1", "1.1"), ("--http2", "2")]
                    if not args.skip_http3:
                        protocols.append(("--http3-only", "3"))
                    for protocol, version in protocols:
                        assert curl(port, protocol, headers=["A: encrypted"]) == (200, version, b"encrypted")
                        assert curl(port, protocol) == (400, version, b"Missing header A")
                        data = bytes(range(256))
                        assert curl(port, protocol, "/binary", body=data) == (200, version, data)
                        assert curl(port, protocol, "/environment") == (200, version, b"effect environment")
                        assert curl(port, protocol, "/request-id", headers=["X-Request-Id: protocol-id"]) == (200, version, b"protocol-id")
                        if version != "3":
                            assert curl(port, protocol, "/large") == (200, version, b"x" * 100000)
                            large_body = bytes(range(256)) * 400
                            assert curl(port, protocol, "/binary", body=large_body) == (200, version, large_body)
                            status, actual, compressed = curl(port, protocol, "/compressed", headers=["Accept-Encoding: gzip"])
                            assert (status, actual, gzip.decompress(compressed)) == (200, version, b"x" * 70000)
                        print(f"PASS {protocol}: actual version, header present/missing, binary body, effect")
            except Exception:
                log.flush()
                print(log_path.read_text()[-16000:])
                raise
            finally:
                server.send_signal(signal.SIGTERM)
                try:
                    server.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    server.kill()
                    server.wait()
                    raise RuntimeError("server failed to stop after SIGTERM")
            assert server.returncode == 0, server.returncode
            print("PASS graceful shutdown")
    dynamic = subprocess.check_output(["readelf", "-d", str(server_binary)], text=True)
    symbols = subprocess.check_output(["nm", str(server_binary)], text=True)
    for forbidden in ["libssl", "libcrypto", "libsqlite", "libpq", "libmysql"]:
        assert forbidden not in dynamic, forbidden
    for forbidden in ["lean_crypto_", "lean_sqlite_", "lean_mysql_", "lean_pg_"]:
        assert forbidden not in symbols, forbidden
    print("PASS native boundary: no OpenSSL/database libraries or stubs")


if __name__ == "__main__":
    main()
