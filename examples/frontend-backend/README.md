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
lake -d examples/frontend-backend build Proof.Proof Proof.Proofv2 Proof.GraphExamples
```

`Proof/Proof.lean` is the original model. `Proof/Proofv2.lean` records the frontend and
backend connection bytes and partial sends. It computes the upstream call from
execution of the frontend code.
`Proof/ServiceProofs.lean` proves properties of the application code. Frontend-owned
credential removal followed by the generic proxy encoder preserves the old
combined encoder byte for byte (`encodeUpstreamRequest_unchanged`).
`Proof/ForwardingProofs.lean` defines input size constraints and proves bounds for the
actual encoder. `encodeUpstreamHead` is the header section used directly by
`encodeUpstreamRequest`; extracting it preserves the same byte-equivalence proof.
`Proof/CodecProofs.lean` proves invariants of the actual parser and body preservation
by the actual encoders. Successful request parsing supplies valid method, target,
and headers, including when the parser takes the chunked body branch. These are
derived from `parseHTTP1`, not additional input restrictions. Credential and
protocol-header filtering preserves header validity. The complete forwarding
roundtrip also proves that the parser finds the encoder's header boundary,
recovers the method, target, and body, and consumes all forwarded bytes.

The following properties are proved rather than assumed in `Contracts`:

- For a resource request, rejected credentials cause no upstream call.
- Accepted credentials cause exactly one call with `backendAddr` and the
  frontend-rewritten request. The rewrite preserves method, target, and body.
  These follow from the handler's execution, without runtime contracts
  (`frontend_authorized_calls`). `upstreamRequest` connects calls to ordered
  child edges; `application_calls_match` proves their target addresses agree.
- For the frontend-rewritten request, the retained headers contain neither
  username nor password headers, and
  the actual header serializer uses these retained headers. This does **not
  yet prove** that the backend's parsed headers omit credentials.
- `wireResponse` always satisfies `Response.valid`, including the generated
  decimal Content-Length and Connection headers.
- The fixed 401 response has a complete encoding/decoding roundtrip in either
  connection mode (`unauthorized_roundtrip`).
- `json_response_roundtrip` proves the actual encoder/observer roundtrip for
  status 200, the fixed JSON content type, and **any binary body**, for both
  connection modes. `resource_roundtrip` and `forwarded_resource_roundtrip`
  therefore have no remaining codec admissions.
- `remote_resource_requires_credentials` proves the necessary-credentials
  direction with transport, runtime correspondence, and the explicit application topology, without
  any admitted codec theorem. The final iff theorem reuses this direction.
- `backend_request_delivered` derives complete parsing of the bytes received by
  the backend and preservation of method, target, and body. It uses request
  transport, frontend call/encoding correspondence, and the forwarding theorem;
  neither a backend parsing assumption nor `backendReply` supplies this result.
- `forwarded_request_roundtrip` independently proves that every originally parsed
  GET request satisfying `ForwardingConstraint` parses completely after forwarding,
  with unchanged method, target, and body. It uses no transport/runtime contracts.
- `responseHeaders_wire`, `wireResponse_wire`, and `encodeHTTP1_wire` prove that
  rebuilding framing headers and re-encoding a valid ordinary GET response is
  equivalent to encoding the original response for the client's connection mode.
  These lemmas contain no `sorry` and use no unfinished roundtrip proof.

`ResourceRequest.forwardingConstraint` applies to the original parsed request,
before credential removal:

| Field | Restriction |
| --- | --- |
| `headerCount` | Fewer than 64 headers, counting duplicates and headers later removed. |
| `headerBytes` | Sum of UTF-8 bytes of all header names and values is at most 48 KiB; excludes separators. |
| `targetBytes` | Target, including query, is at most 8 KiB in UTF-8. |
| `bodyBytes` | Decoded body is at most 10 MiB. |

These replace the earlier limit on the complete raw request. They are theorem
premises, not new runtime rejection rules. They impose no credential-validity
requirement and do not prohibit duplicate application headers or binary bodies.

For GET requests to the configured backend, the encoder's exact header size is
target bytes + retained header content bytes + 4 × retained header count + 76
+ Content-Length decimal bytes. The constant includes the generated protocol
fields and the final empty line. `forwarded_head_bound` proves:

```text
encoded header size ≤ 8192 + 49152 + 4 × 63 + 76 + 8 = 57680 < 65536
```

`forwarded_size_limits` proves that both header and body fit the default parser
limits without transport, runtime, or codec assumptions. `backend_received_size`
connects the size bound to delivered backend bytes using transport and runtime
correspondence; it does not use codec fields. The complete request roundtrip
combines these bounds with the syntax, framing, and body-extraction proofs.

`Proof/ExchangeGraph.lean` defines the common finite interaction graph. Nodes have a
program label, optional listening address, and a natural-number rank. Each
`upstream` edge has a caller, callee, parent request, byte records, source IP and
port, and response connection mode. Responses use the same edge in reverse;
only request directions contribute to the DAG.

`entry` identifies the external request. `children edge` is an ordered list of
calls made while handling that request. Structural proofs enforce valid finite
IDs, one root, consistent parent/caller relationships, complete child lists,
no duplicate child IDs, and strictly increasing node ranks. `acyclic` proves
there is no nonempty directed cycle. Multiple calls to the same service are
separate edges and may have different parents; nodes do not store a single
shared request. These are rooted interaction graphs for one external request,
not arbitrary disconnected deployments or request-merging workflows.

`Proofv2.Exchange` extends this graph with the original parsed request. Its
`client`, `sourceIP`, `sourcePort`, and `clientClose` are computed from the entry
edge, not independently stored. `backendEdge` is a computed convenience view of
the first entry child. The graph itself is not restricted to one child:
`frontend_calls_length_le_one` and `frontend_children` prove that restriction for
this application from its code and call correspondence.

`Contracts` bundles only `transport` and `runtime`:

- `TransportContracts.edges` requires `StableTransport` on every interaction.
- `RuntimeCorrespondence` connects execution to the graph as described below.

`Proof/ApplicationExchange.lean` constructs this application's graph from an
`ApplicationInput`: the original request, client source IP/port, client byte
records, optional backend byte records, and client close mode. These are data,
not proof fields. `input.exchange` chooses the one-edge or two-edge construction.
It sets the node programs, addresses, parent relationships, and connection modes.
`ApplicationInput.topology` proves their consistency with the application for
every input, without transport, runtime, credential, or codec premises.
`FrontendBackendTopology` remains a property used in generic helper lemmas; it
is not a `Contracts` field or a caller-supplied premise of the final theorem.

| Runtime field | Remaining assumption |
| --- | --- |
| `clientParsed` | The entry request bytes parse completely as `e.request`. |
| `upstreamRequest` | Each child edge sends the encoding of its corresponding call, using `Requests`. |
| `replies` | Every edge sends the output computed by its receiving node's program, using `Replies`. |

`Aligned` relates two lists element by element, including equal length.
`upstreamRequest` already supplies the ordered correspondence and equal lengths,
so the separate `callsMatch` field has been deleted. `frontend_calls_cases`
proves directly from the application code that execution either makes no call
or calls `backendAddr` once. `application_calls_match` combines this with the
constructed graph's callee addresses and `upstreamRequest` to prove the former
field's complete statement, including target matching. It needs no additional
topology, transport, valid-credential, or request-size premise. `callCount` and
`frontend_children` now use `upstreamRequest` for their length equality.
The parent/child invariants prevent responses from another request being used as
this request's children. `exchange_edges` proves that with the current topology
and runtime correspondence, every edge is either the entry or the optional
backend call.

`Requests connection calls` equates successfully sent request bytes with the
call encodings. In the graph correspondence each edge receives a singleton call.
`Replies connection respond` requires successful response sends to equal
`output` whenever `respond (bytes connection.requestReads) = some output`.
It assumes neither parsing success nor the existence of output. External client
requests are not constrained by a service `Requests` contract.

`replyBytes e edge` selects the actual frontend or backend computation according
to the callee's program. The frontend parses this edge's input and uses this
edge's own child response, peer address, and close mode. The backend parses its
received bytes and runs `backendCore`, using the edge's close mode. The existing
forwarding proof establishes successful backend parsing and field preservation;
no backend request or response content is independently supplied.
`frontend_reply_iff` still establishes equivalence with the earlier frontend
send equality under `clientParsed`. `RuntimeCorrespondence.frontendReply` and
`backendReply` are derived helpers, not independent contract fields.

The graph's program type is generic. The current application interpreter and
call correspondence remain specific to this frontend, which issues at most one
call, and this backend. This change does not prove arbitrary DAG application
policies or implement a general multi-call effect interpreter. The data model
already supports multiple ordered children, shared service nodes, and arbitrary
finite depth; those applications can extend the execution layer separately.

`Proof/ApplicationExchange.lean` provides constructors and topology proofs for both current
shapes: client → frontend with no backend call, and client → frontend → backend.
They accept arbitrary byte records, request, and client source IP/port; they do
not bake transport reliability or authorization into construction.
`Proof/GraphExamples.lean` constructs a branching diamond with a shared receiving service and
proves that the two requests to that service have distinct parent requests.

`CodecContracts` remains deleted. The codec proof modules are unchanged and
contain no admissions. Stable transport only equates sent and received bytes;
`Requests`/`Replies` still connect those records with code output. Opaque IO,
C, and OS behavior is not verified by these contracts.

The final `remote_resource_iff_credentials` takes `input : ApplicationInput`,
`contracts : Contracts input.exchange`, and `hRequest : ResourceRequest input.exchange`.
It applies to the graph constructed by `input.exchange` and obtains topology
from the construction theorem internally. No caller supplies a topology proof.
The existing request restrictions remain; ordered address matching is now
proved rather than assumed. No codec or authentication assumption was added. The proof modules contain no
`sorry`, and the final theorem's axiom dependencies contain no `sorryAx`.

The backend handler input comes from the received-byte parser by definition.
`backend_decoded_fields` proves field preservation and complete consumption for
every successful result of that parser, using the proved forwarding roundtrip.
The response theorem
applies to `resource target` by treating its JSON output simply as body bytes.
The proved re-encoding lemmas reuse this result for the frontend response
(`forwarded_resource_roundtrip`). The rejected branch continues to use the
already proved fixed 401 roundtrip. Thus no separate frontend codec admission
is needed.

The response proof is built from these results:

- `Proof/DecimalProofs.lean`: `(toString n).toNat? = some n` for every natural number.
- `Proof/AsciiHTTPProofs.lean`: the actual legacy `splitOn` recovers ASCII rows joined
  by CRLF and fields separated by a colon, under the stated separator conditions.
- `Proof/TrimProofs.lean`: the actual `trimAscii` removes a prepended space and preserves
  a value containing no whitespace; this applies to the generated decimal length.
- `Proof/ResponseHeadProofs.lean`: the four JSON response lines are recovered,
  `parseHeader` recovers Content-Length, and `findBytes` locates the first
  CRLFCRLF at the end of the head. The prefix proof also excludes false matches
  across concatenation boundaries.
- `Proofv2.decode_json_frame`: UTF-8 decoding applies only to the head, the parsed
  length matches the body size, and byte extraction returns the original body.
  `json_response_roundtrip` connects this frame to the actual `encodeHTTP1`.

The request proof is built from these results:

- `Proof/StringJoinProofs.lean` and `Proof/HTTPStringProofs.lean`: the actual legacy `splitOn`
  recovers fields and CRLF-separated rows using UTF-8 byte positions. These
  lemmas support Unicode targets and values, empty colon-separated segments,
  and values containing multiple colons.
- `TrimProofs.trim_mem`: trimming only removes characters, preserving the
  validity constraints of arbitrary header values.
- `Proof/RequestHeadProofs.lean`: every serialized retained header parses successfully,
  keeping its name and a valid, possibly normalized value. The actual encoder
  produces the proved request line and header rows. The decoded Host is unique
  and nonempty, Content-Length is unique, and Transfer-Encoding is absent.
- `Proof/RequestFramingProofs.lean`: a UTF-8 encoding of a character other than CR
  cannot contain byte 13; nonempty header rows therefore cannot create an early
  CRLFCRLF, including at concatenation boundaries.
- `Proof/HTTPDecimalProofs.lean`: the HTTP parser's stricter private decimal routine
  accepts `toString n` and returns `n`. A local syntax bridge references the
  existing legacy private constant for proof access; it adds no axiom or
  replacement parser. Its name must track the codec's private name if that
  module is reorganized.
- `CodecProofs.forwarded_request_roundtrip`: the original parse supplies valid
  fields, the existing constraints supply size bounds, and the actual parser
  checks reduce to the proved header facts. It then extracts precisely the
  original body and leaves no bytes unconsumed. No equality of whole requests
  or of all header values is needed.

`#print axioms` also confirms that `json_response_roundtrip`, `resource_roundtrip`,
and `forwarded_resource_roundtrip` do not depend on `sorryAx`. Some fixed-string
checks use Lean's `native_decide`, so these proofs include its native evaluation
trust dependency. No new transport/runtime assumptions or codec premises were
introduced. No arbitrary-header roundtrip or JSON serialization property is
claimed.

### Scope of the completed proof

These proofs use the existing encoders and parsers. No service implementation,
proxy behavior, or codec implementation was changed to make the proof succeed.
The request theorem allows the original parse to take either the fixed-length
or chunked branch; forwarding encodes the decoded body with Content-Length.

Separately, the proxy's 1 MiB response-body limit needs a bound on the resource
JSON produced from the target when verifying the IO reader. `decodeResponse`
has no such limit and remains a specification observer. Runtime correspondence
with IO, C, sockets, and the OS is still assumed. The pure roundtrip theorems do
not verify that correspondence.
