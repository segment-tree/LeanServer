# Basic HTTP server

This independent Lake package depends on the local LeanServer checkout. It
imports `LeanServerPure` and `LeanServer.Server.HTTPServer`, builds a pure
`WebAppState Id`, and runs it through the existing server. Lake compiles
`src/Network.c` automatically; no Makefile, OpenSSL, certificate, or database
driver is required.

From the repository root:

```sh
lake -d examples/basic-server build
examples/basic-server/.lake/build/bin/basic-server 8080
```

The optional port defaults to 8080; the example binds to `127.0.0.1`.
The old `server.config` file is not read. For an externally reachable service,
change `host` in `Main.lean` to the desired address.

```sh
curl http://127.0.0.1:8080/health
curl -X POST --data 'hello' http://127.0.0.1:8080/api/users
```

| Method | Path | Response |
|---|---|---|
| GET | `/` | HTML welcome page |
| GET | `/health` | Static JSON health response |
| GET | `/api/info` | Server information |
| GET | `/metrics` | Static example values, not runtime measurements |
| POST | `/api/users` | JSON body echo with status 201; no database write |

The current DSL and runtime boundary look like this:

```lean
import LeanServerPure
import LeanServer.Server.HTTPServer

open LeanServer LeanServer.WebApp

def app : WebAppState Id := webApp do
  get "/" fun _ => WebApp.htmlResponse "<h1>Hello!</h1>"
  get "/health" fun _ => WebApp.jsonResponse "{\"ok\":true}"

def main : IO Unit :=
  LeanServer.serve { host := "127.0.0.1", port := 8080 }
    (m := Id) (fun value => pure value) app.dispatch
```

See [the application API](../../docs/APPLICATION_API.md) for other effects,
TLS configuration, migration details, and current runtime limitations.
