# Frontend / Backend

This example contains two independent plaintext HTTP services. The frontend
listens on `0.0.0.0:8080`, checks two simple request headers, and forwards
authenticated requests to the backend on `127.0.0.1:8081`.

The credentials are deliberately plain headers for this minimal example:

```http
X-Username: Tom
X-Password: 123456
```

Missing, duplicated, or incorrect credentials return `401 Unauthorized`.
Successful requests to `/resource` are sent to the backend. The backend only
supports `GET`; `POST` and other methods return `405 Method Not Allowed`.
The response also includes the received request target, so query forwarding is
visible in the example.

The proxy core accepts a plan that returns one or more upstream calls and a
response combiner. Calls are executed sequentially in plan order, so the same
handler supports both ordinary proxying and response fanout. The local
`proxy-tests` executable exercises two mocked upstreams without opening sockets.

`Proxy.lean` owns HTTP framing: it replaces Host and Content-Length and removes
the listed connection headers. Application headers are otherwise preserved.
Callers supply request rewrites through their plan, or through
`singlePlan upstream rewrite` (the default rewrite is `id`). For example,
`singlePlan upstream (fun r => { r with target := "/rewritten" })` changes the
target. This frontend uses `singlePlan backendAddr backendRequest` to remove
credential headers after authenticating the original request.

The frontend and backend business handlers are also available without their
process entrypoints: `FrontendCore.lean` exposes `frontendWith`, and
`BackendCore.lean` exposes `backendCore`. Both accept any `Monad`, so policy
tests can use deterministic `StateM` or `Id` models while the executable
wrappers continue to use real `IO` sockets.

Source layout:

- The example root contains the service entrypoints, business handlers, and proxy.
- `Proof/` contains all proofs, exchange models, and graph constructions.
- `Test/` contains the proxy, frontend policy, and backend policy tests.

Build and run from the repository root:

```sh
lake -d examples/frontend-backend build
lake -d examples/frontend-backend build proxy-tests
examples/frontend-backend/.lake/build/bin/proxy-tests
lake -d examples/frontend-backend build frontend-policy-tests backend-policy-tests
examples/frontend-backend/.lake/build/bin/frontend-policy-tests
examples/frontend-backend/.lake/build/bin/backend-policy-tests

# terminal 1
examples/frontend-backend/.lake/build/bin/backend

# terminal 2
examples/frontend-backend/.lake/build/bin/frontend
```

Try the service:

```sh
curl -i http://127.0.0.1:8080/resource
curl -i -H 'X-Username: Tom' -H 'X-Password: 123456' \
  http://127.0.0.1:8080/resource
curl -i -X POST -H 'X-Username: Tom' -H 'X-Password: 123456' \
  http://127.0.0.1:8080/resource
```

The first request returns 401, the second returns the backend sample JSON, and
the third returns 405 with `Allow: GET`. The frontend removes the credential
headers before forwarding. This example uses plaintext HTTP intentionally and
is suitable for local testing, not production authentication.

Lake builds `src/Network.c` automatically. No Makefile, OpenSSL, or database
driver is required.

## Proof status

Build proofs explicitly; the default executable build does not check them:

```sh
lake -d examples/frontend-backend build Proof.Proofv2 Proof.GraphExamples
```

`Proof/Proofv2.lean` proves the policy on the specified, fixed frontend/backend
network. The final theorem is:

```lean
theorem remote_resource_iff_credentials
    (source : Upstream)
    (contracts : Contracts (frontendBackendGraph source))
    (wire : ByteArray) (hRequest : ResourceInput wire) :
    observed (frontendBackendGraph source) contracts wire = expectedResource wire ↔
      credentialsMatch (context wire) = true
```

`source` is the client's IP and source port, with no restriction on either.
`wire` is its raw HTTP request. The graph is defined independently of the
request. `contracts` supplies the two reliable operations described below.
`hRequest` restricts the parsed request to the resource endpoint and the proved
size limits. The conclusion compares the client's received response status and
body with the backend's expected resource response. It does not compare every
response header. Correct credentials mean exactly one X-Username value `Tom`
and exactly one X-Password value `123456`; missing, incorrect, or duplicate
credential headers fail the check.

### Fixed graph and execution

`Proof/NetworkGraph.lean` defines a generic network DAG:

- `nodes : List (Handler AppM)` stores actual handlers, with arbitrary service
  count. There are no frontend/backend program labels in the graph type.
- `none` is the distinguished client node; `some i` is service `i`. The client
  initiates the request and receives its response, and has no handler.
- `routes caller callee` expresses network reachability, independently of calls
  made during execution. Responses travel back over the established connection;
  they do not require another directed call edge.
- `addresses` and `resolve` associate services with their upstream addresses;
  their consistency is part of a well-formed graph.
- `clientAddress` stores the source endpoint. `entry` selects the initial service
  called by the client. `noIncomingClient` excludes new calls into the client.
- Decreasing node ranks prove acyclicity and termination of nested dispatch.

`AppM` describes a returned value or an upstream request with its continuation.
Its monad laws are proved. Existing polymorphic handlers run in it without
rewriting application policy. `Proof/NetworkExecution.lean` interprets every
upstream effect by resolving its address, checking the network route, sending
encoded bytes, parsing the received request, and executing the actual handler
stored at the target node. It recursively processes any further calls that
handler makes. There is no fixed call depth or fuel bound.

`Proof/ApplicationGraph.lean` defines `frontendBackendGraph source`. It stores
`frontendWith callUpstream` and `backendCore` as its two service handlers and
has the fixed client→frontend and frontend→backend routes. The backend route
remains present for incorrect credentials; the frontend simply does not call it.
`frontendBackendGraph_application` proves the service identities, backend
address, and required routes from this definition. These are not additional
premises supplied to the final theorem.

`resource_iff_on_network` is the supporting theorem for any network with the
specified frontend/backend handlers and routes. `Proof/GraphExamples.lean`
instantiates it on a network with four services plus the client, branching
routes, a shared backend, and two arbitrary extra handlers. The generic model
is therefore not restricted to the application's three-node topology.

The earlier interaction-record graph and `ApplicationInput` constructor were
removed. Execution no longer creates or removes network edges. The graph is
passed to the interpreter and is never modified by a request. The separate old
pure policy model has also been removed. See [the proof file map](Proof/README.md)
for every current module's role and dependencies.

### Complete list of environmental contracts

There is no separate `Environment` parameter. Each contract packages its
operation with its reliability proof, so these structures live in `Type`:

| Contract | Operation | Required property |
| --- | --- | --- |
| `SocketContracts graph` | `send caller callee direction payload` | For any nodes, direction and payload, bytes entering the network equal the submitted payload. |
| `TransportContracts graph` | `receive caller callee direction payload` | For every reachable caller→callee route, in either direction, received bytes equal the payload. |

`Contracts graph` contains exactly `socket` and `transport`. Neither mentions
HTTP, credentials, resources, handler results, or parsing success. `delivered_eq`
proves their composition preserves bytes. Execution uses these operations for
the client request, upstream request, backend response, and frontend response.
These are complete, reliable operations; partial writes, errors, retry timing,
and liveness of the real socket implementation are outside this model.

There is no `RuntimeCorrespondence`, `clientParsed`, `CodecContracts`,
`ExecutionProperties`, or `ExecutionEvidence` parameter. No response or parsed
request is independently supplied and equated to what the handler should do.

### Request scope and close mode

`completeRequest wire` invokes the real `parseHTTP1` and returns a request only
if one complete request consumes the supplied bytes. `ResourceInput wire`
requires that this computed result satisfies:

| Field | Restriction |
| --- | --- |
| `method` | `GET` |
| `path` | `/resource`; a query string is allowed |
| `forwardingConstraint.headerCount` | Fewer than 64 original headers, including duplicates and headers later removed |
| `forwardingConstraint.headerBytes` | Sum of UTF-8 bytes of all header names and values ≤48 KiB, excluding separators |
| `forwardingConstraint.targetBytes` | Complete request target, including query, ≤8 KiB in UTF-8 |
| `forwardingConstraint.bodyBytes` | Decoded body ≤10 MiB |

Successful, complete parsing remains part of the request scope; it is not a
separate assertion relating two independently supplied request representations.
These restrictions do not assume correct credentials and were not tightened
for the network proof. They are theorem conditions, not new application checks.

`context wire` builds a context from that parser result. It uses a default
request only to make the notation total on invalid input; `ResourceInput`
excludes that branch, and the interpreter never dispatches this fallback.
Execution supplies the actual peer address from the graph; the credential
predicate depends only on the parsed request headers.

`responseClose request` uses exactly the expression in `handlePlainHTTP`:

```lean
((request.headers.get? "connection").getD "").toLower == "close"
```

Both frontend and backend compute it from their own received request. There is
no free `close` parameter in execution or the final theorem. General codec
lemmas still quantify over both close modes. The policy proof works for the
backend's computed mode without an additional mode assumption.

### Proof dependencies

The proof executes the real application cores and uses the existing pure HTTP
encoders/parsers:

- `frontend_run` and `backend_run` prove that interpreting the application effects
  gives the results of the existing handlers.
- `invoke_resource` derives successful forwarded parsing and the backend result
  from the input request, reliable operations, and graph dispatch. Backend
  request equality, parsing success, and resource output are not assumed.
- `observed_of_request` connects the computed frontend response with the bytes
  decoded at the client using the two contracts.
- The accepted branch uses the backend resource roundtrip and re-encoding proofs.
  The rejected branch uses the 401 roundtrip; status 401 cannot equal resource
  status 200. Together these prove both directions of the final equivalence.

The existing codec proofs were preserved. Response-specific pure lemmas formerly
inside `Proofv2.lean` were moved to `Proof/ResponseCodecProofs.lean`:

- `Proof/ForwardingProofs.lean` proves the forwarded header bound of 57680 bytes
  under the existing constraints, below the parser's 65536-byte limit.
- `Proof/CodecProofs.lean` proves the complete forwarding roundtrip and preservation
  of method, target and body. Original requests may use chunked framing; the
  proxy encodes the decoded body with Content-Length.
- `Proof/ServiceProofs.lean` proves application rewriting and handler properties.
- The decimal, UTF-8, split/join, trimming, header and framing proof modules prove
  the constituent parser/encoder facts without codec contracts.
- `resource_roundtrip`, `unauthorized_roundtrip`, and `encodeHTTP1_wire` prove
  response decoding and frontend re-encoding preserve the required status/body.

There are no admissions in the final proof. Its axiom audit includes Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`, plus the existing
`native_decide` dependencies used by codec proofs. No new business axiom or
handler-behavior premise was introduced.

### Verification boundary

This proves the specified graph's handler execution model under reliable system
and network operations. It does not verify the deployed IO server, C, OS, or
socket implementation, nor a refinement from the actual IO loops to this model.
`decodeResponse` remains the complete-response specification observer; it is
not the proxy's incremental `readBackendResponse` with its 1 MiB limit.
Similarly, the theorem starts with complete request bytes and does not prove
that every chunking of those bytes passes the real server's intermediate buffer
limit. These IO correspondence obligations remain outside the theorem; they
were not replaced by new premises. No service, proxy, or codec implementation
was changed to make this proof succeed.
