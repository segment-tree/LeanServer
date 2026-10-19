# Application framework implementation

This work follows the agreed upstream refactor at commit 24b916a.

## Delivery gates

- [x] Pure HTTP types, effect-polymorphic handler/router, dispatch proofs.
- [x] Explicit application injection into plaintext and TLS HTTP/1.1.
- [x] HTTP/2 and HTTP/3 adapters preserve headers and binary bodies (H3 small-request interoperability only).
- [x] Remove application registries and consolidate Web APIs; separate health policy from IO.
- [x] Lake builds Network.c automatically; downstream package requires no Makefile.
- [x] Protocol, effect, downstream build and native dependency tests; migration documentation.

The user explicitly confirmed the incompatible Web migration on 2026-09-25.
All Web application models now alias the canonical HTTP API. Main and the Web
executables use explicit handlers and middleware. Template and SQL-builder
algorithms are preserved as pure modules; driver helpers are optional and use
explicit manager arguments. IO probes remain in the runtime.

## Decisions

- Preserve HTTP method case (HTTP methods are case sensitive).
- Header lookup compares ASCII names case-insensitively and preserves duplicates.
- Applications choose their monad and explicitly supply its interpreter to IO.
- Socket operations and runtime health probes remain IO. Pure health policy and response construction do not import the server.
- One running server per process remains the runtime boundary for this release.
- Linux is the initial target. Bodies are bounded byte buffers.
- Existing protocol internals are reused; test results, rather than advertised protocol names, determine interoperability claims.

## Validation record

2026-09-25, Lean 4.29.1 on Linux:

- 30 pure framework checks: Id/ReaderT/StateM/Except, header lookup, framing,
  binary bodies, QPACK, routes/groups, middleware ordering and short circuit,
  injected request-id generation, response validation, health policy/JSON.
- Existing application integration suite: 20/20; failures now return a nonzero
  process status. Added concurrent connection admission/release, 32 concurrent
  tracing spans, and handler-exception recording regressions. Tasks are joined
  with `IO.wait` in both tests and server shutdown.
- Existing HTTP/2 model suite: 51/51. Existing TLS model loopback: 45/45.
  These suites are not full RFC conformance proofs.
- Migrated Web suite: 31 checks for aliases, Id/ReaderT/StateM, routes/groups,
  templates, SQL builders, JSON escaping, CORS/Basic auth/rate-limit short circuit,
  Vary preservation and encoding negotiation. Compile checks also cover common
  facade dot notation and definitional forwarding to the canonical API.
- Real socket tests: plaintext, TLS HTTP/1.1, HTTP/2, HTTP/3 with negotiated
  version checks, present/absent A, binary data and ReaderT IO environment.
- HTTP/1.1 and HTTP/2: 100 KB response, 102400-byte binary upload/echo.
  Raw HTTP/2 client verifies initial zero stream window and later WINDOW_UPDATE.
- Exception/invalid-response conversion to 500, duplicate Set-Cookie, HTTP/1
  keepalive/chunked/fragmented input, SIGTERM shutdown.
- Real gzip/zlib decoding of binary responses; 32 concurrent request IDs;
  credentialed CORS preflight; parameter routes; tracing propagation and collection.
- `readelf` and `nm`: no OpenSSL/database dependencies or stub symbols.
- Independent `examples/header-echo` and `examples/basic-server` Lake consumers
  build without make. The migrated `webserver` and basic consumer serve real
  routes from an unrelated working directory; JSON escaping and shutdown pass.
- Final fresh build `/tmp/leanserver-framework-clean.wwUzQw`: pure library plus
  framework/Web tests build without `native/`; runtime build produces only
  `native/Network.o` (plus Lake metadata), with no optional native archive.
  That fresh runtime passes integration tests and real socket/dependency checks
  on all four transport paths. The normal Lake build configuration is restored.
- New CI workflow covers the clean pure/runtime split and consumer build.
  CI itself has not been run remotely.

See [APPLICATION_API.md](APPLICATION_API.md) for runnable usage and migration.

## Preserved, changed, remaining

Preserved: original crypto/protocol algorithms, existing proof/spec modules,
legacy optional database/crypto modules. Web API names now forward to the
canonical HTTP types. TLS flight construction
now accepts configured certificate/key paths. The new core does not import
optional backends.

Added: canonical byte-oriented HTTP data, effect-polymorphic routing/middleware,
explicit effect interpreter, bounded HTTP/1 parser, HPACK/QPACK application
adapters, Lake native dependency ownership, deployable Id and ReaderT IO
examples, proof statements and regression tests.

Necessary runtime repairs: full writes, fresh receive buffers, configurable
binding, TLS record fragmentation for large H2 frames, pending H2 responses and
window updates, receive-window replenishment, body bounds and pool accounting.

Remaining protocol work: expand HTTP/3 packetization, reassembly and flow-control
resumption; broader protocol validation and runtime state isolation. Generic
streaming and multi-server/process support remain outside this application API
release. Deployment extensions still have legacy low-level helpers. This patch
does not establish whole-server security or correctness.

## Existing failures outside the migration

Compiling the old executable catalog found two failures in unmodified sources:
`tests/TestDatabase.lean` calls `initDatabaseManager` with an obsolete signature
and ends with stray XML text; `tests/DatabaseExamples.lean` has no root `main`
for its executable target. All other existing executable targets built. These
optional database targets are not part of the pure/runtime build or its CI gate.
