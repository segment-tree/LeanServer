# Application API (0.2 development)

The new application API is available through `LeanServerPure`. The existing
`LeanServer.Server.HTTPServer` runs it directly. A minimal service links the
project's `src/Network.c` and the normal Lean/system runtime; it does not import
`Crypto.FFI`, database drivers, or their native stubs. TLS uses the existing Lean
implementation. Lake builds the native archive automatically, including when
LeanServer is a dependency of another package.

## Run the header example

From this checkout:

```sh
lake build header_echo
.lake/build/bin/header_echo --host 127.0.0.1 --port 8080
```

In another terminal:

```sh
curl -H 'A: hello' http://127.0.0.1:8080/  # 200, hello
curl http://127.0.0.1:8080/                # 400, Missing header A
```

Header names use ASCII case-insensitive lookup. An empty `A` value produces an
empty 200 response. HTTP method names remain case-sensitive.

`examples/header-echo` is a separate Lake consumer, using a path dependency on
this checkout. It contains application code only:

```sh
lake -d examples/header-echo build
examples/header-echo/.lake/build/bin/header-echo
```

That example binds port 8080 on all interfaces. Its binary can be deployed as a
normal Linux executable, subject to its `ldd` system/runtime dependencies. No
certificate or `server.config` is needed for plaintext HTTP.

To use a Git dependency, replace the consumer's `path` entry with `git` and `rev`
pointing at a repository and commit containing these changes. They are currently
local and uncommitted; upstream `main` does not yet provide this API.

## Application and effects

```lean
import LeanServerPure
import LeanServer.Server.HTTPServer

open LeanServer.HTTP

def app : Handler Id := fun ctx =>
  match ctx.request.headers.get? "A" with
  | some value => Response.text value
  | none => Response.text "Missing header A" 400

def main : IO Unit :=
  LeanServer.serve { host := "127.0.0.1", port := 8080 }
    (m := Id) (fun value => pure value) app
```

`Handler m = Context → m Response`. `Middleware m` wraps a handler, so it can
run effects before and after the handler or return early. `Router m` is an
immutable value; selection is pure, dispatch executes the selected handler.
The first registered matching route wins. Route groups scope middleware to
their mounted routes. Middleware request order is left to right and response
order is right to left.

For `ReaderT Env IO`, pass `(fun action => action environment)` to `serve`.
For `IO`, use `serveIO`. State and error effects require an interpreter chosen
by the caller; the server does not silently discard application state or
invent an error policy for `Except`. The interpreter can be called concurrently,
so shared mutable state needs the application's chosen synchronization.

Requests and responses contain `ByteArray` bodies. Header arrays preserve
duplicates (`get?` selects the first; `getAll` selects all). The runtime owns
framing headers, filters connection-specific response headers, and suppresses
bodies for HEAD/204/304. Invalid responses and uncaught IO errors become 500.

Health status, aggregation, JSON serialization, and response construction now
live in `HTTP.Health`, which is exported by `LeanServerPure`. Actual probes in
`Server.HealthCheck` remain IO: reading files, time and runtime state are effects.
An `Id` application can model health policy but cannot execute an IO probe.

## TLS and protocols

```sh
.lake/build/bin/header_echo --port 8443 --tls --cert /path/cert.pem --key /path/key.pem
```

This enables the existing Lean TLS runtime with HTTP/1.1 and HTTP/2. `--h3`
additionally enables the experimental QUIC/HTTP/3 listener on the same UDP port.
Certificates are required only for TLS/QUIC. Certificate generation tools used
in tests do not become server dependencies.

All four paths invoke the supplied application. Tested interoperability includes
small header and binary requests on all four paths, and 100 KB uploads/responses
on HTTP/1.1 and HTTP/2. HTTP/2 response buffering respects the peer's stream
window, including zero-window requests followed by WINDOW_UPDATE.

Current boundaries:

- Linux; one running server per process; buffered request/response bodies.
- Request limits are configurable through `ServerConfig.limits`. Oversized
  HTTP/1 requests receive an error; the H2 receive loop closes a connection
  when a body exceeds its configured bound.
- HTTP/3 still inherits incomplete large-response packetization, flow-control
  resumption, and receive reassembly from the original runtime. It is an
  interoperability prototype, not a completed production transport.
- No generic streaming, WebSocket, or SSE application API in this change.
- Socket timeouts do not cancel arbitrary application effects. Shutdown waits
  for active tasks, so handlers must complete or provide their own cancellation.
- Pure handler/router theorems are specific statements. Neither compiling Lean
  code nor excluding OpenSSL proves the whole parser, TLS engine, or IO runtime
  correct. The compiler/runtime, OS and network FFI remain trusted components.

## Migration status

| Previous API | New API | Status |
|---|---|---|
| Global `registerRoute` / `findRegisteredRoute` | Local `HTTP.Router m`, `.dispatch` | Core entry points and integration tests migrated |
| `runHTTPServer server` | `serve config runEffect handler` / `serveIO` | Migrated |
| Global application middleware registry | Explicit `HTTP.Middleware m` list | Removed from core |
| Health policy mixed into runtime probes | `HTTP.Health` plus `Server.HealthCheck` | Split |
| Manual `make`, relative `Network.o` | Lake `network` target and runtime library | Implemented |
| `Web.Framework`, `WebApplication`, `WebApplicationSimple` duplicate application models | Aliases/builders over the canonical types | Migrated; exported by `LeanServerPure` |
| Legacy text middleware in `Main` | Canonical effect-polymorphic middleware | Migrated; byte bodies stay intact |
| Global request context / tracing hook | Context locals / explicit tracing middleware | Removed |
| Database managers inside Web Context | Application environment; optional `Db.Web` helpers | Explicit managers and updated results |

The incompatible migration is applied. `Web.Context` and `Web.Response` alias
`HTTP.Context` and `HTTP.Response`; `Web.Router m` forwards to `HTTP.Router m`.
There is one dispatch implementation. The old `WebAppState` and `WebApplication`
names now take a monad parameter and alias that router too. Use `request.target`,
`ctx.path`, `response.status`, and response headers; application types no longer
carry an HTTP/2 stream ID or a separate `contentType` field.

The `WebApp` DSL uses `open LeanServer.WebApp`, `webApp do ...` and `WebAppState Id`
(or another monad). Configure networking when calling `serve`; the old
`defaultWebAppConfig`, driver fields and initialization-only `startWebApp`
functions are gone. `webserver` and `examples/basic-server` now actually listen
through the existing HTTPServer. The sample's `/users/:id` endpoints preview SQL;
they do not claim to execute database operations.

`Web.Template` preserves the original renderer, including raw interpolation:
callers must escape untrusted HTML. `Web.ORM` preserves the original SQL string
builders; use driver parameters for untrusted values. Neither module imports
drivers. Optional `Db.Web` retains query execution helpers with explicit manager
arguments and returns the updated manager. Shared database state belongs in the
application's chosen effect and needs its own concurrency policy.

Pure CORS, content-negotiation and compression middleware work with any monad
and are exported by `LeanServerPure`. CORS validates Origin, method and requested
headers before dispatching a preflight. Compression encodes real binary bodies,
honors q=0, and preserves Vary from other middleware. The retained compressor
uses stored DEFLATE blocks: correct gzip/zlib framing, no size reduction.

`HTTP.logging`, `HTTP.requestId`, `HTTP.basicAuth` and `HTTP.rateLimit` accept
application effects. `rateLimitStep` is a pure fixed-window transition; callers
atomically supply time and state. `RequestId.requestIdMiddlewareWith` adds the
legacy configurable header names with an explicit generation effect; its IO
convenience function uses random bytes. `withRequestContext` is now a ReaderT
scope. IO tracing records the actual handler duration and exceptions; its
collector synchronizes concurrent updates. `tracingMiddlewareWith` accepts an
explicit backend for applications using other effects.

Low-level legacy protocol/helper types in HTTPServer remain for existing server
extensions and their proofs; the new application path does not convert through
those string-based response models. The broader protocol/security audit and
migration of unrelated deployment extensions are separate work.

## Reproduce validation

```sh
lake build LeanServerPure header_echo framework_tests framework_server webapptests webserver test_integration
.lake/build/bin/framework_tests
.lake/build/bin/webapptests
.lake/build/bin/test_integration
python3 tests/framework_e2e.py
python3 tests/framework_e2e.py --tls
lake -d examples/header-echo build
lake -d examples/basic-server build
python3 tests/web_e2e.py
```

TLS tests require `openssl` for a temporary certificate and curl with HTTP/2
and HTTP/3 support. Use `--tls --skip-http3` with an HTTP/2-only curl. The tests
run the server from a temporary working directory, check actual negotiated
protocol versions, stop it with SIGTERM, and inspect native dependencies and
symbols. `.github/workflows/framework.yml` adds a clean CI build without
`make`, OpenSSL development headers, or prebuilt project native objects.

For an isolated build, use `lake -R -KbuildDir=/absolute/empty/directory build
LeanServerPure framework_tests webapptests`, check that it has no `native/` directory,
then build `header_echo framework_server` with the same option. Only
`native/Network.o` should appear. Pass `--server /absolute/empty/directory/bin/framework_server`
to the network tests. `-R` is required when changing the build-directory option
because Lake caches the elaborated configuration. Run `lake -R build` without
the option afterward to restore the normal directory. Finish each build before
changing that option; concurrent builds with different settings in the same
checkout share Lake's configuration cache.
