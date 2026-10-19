# Header echo

A separate Lake package using `LeanServerPure` and the existing
`LeanServer.Server.HTTPServer`. Its `Handler Id` returns the first `A` header
value (case-insensitive name), or status 400 with `Missing header A`.

## Conditional proof

`App.lean` contains the handler used by the executable. `Proof.lean` proves
that an accepted HTTP/1.1 request whose first parsed `A` value is `v`, and
whose method is not `HEAD`, is encoded with body `v.toUTF8`. It also proves
that the response `Content-Length` is the UTF-8 byte count. The response head
is the same response encoded for `HEAD`, which has no payload; the observed
body is the bytes after that head in the first response.

`remote_echo` quantifies over every source IP and source port. Its
`StableTransport` premise assumes that the server receives the client's bytes
in order (regardless of read chunking); each socket send reports a length
within its offered buffer, and the corresponding prefixes arrive at the same
client in order. The theorem concerns an
accepted connection and a complete, successfully parsed first request; it
does not claim that every remote address can connect. Socket/C/OS behavior is
trusted under this premise, not proved.

`runtimeCorrespondence` is a separate, unproved premise: the actual server
must write the bytes produced by the pure parse, handler, and encoder path.
Proving that its IO path satisfies this premise requires a server refinement
proof outside this example. The result here is therefore a conditional
end-to-end statement, not a proof of the running server or client HTTP parser.

The main `remote_echo` theorem also requires that `Response.text v` passes the
framework's response validation. Its fixed content-type token check uses an
opaque standard-library string operation. `remote_echo_checked` discharges
this condition with `native_decide`; that convenience theorem additionally
trusts Lean's native evaluator for the fixed string computation. The separate
`text_content_length` theorem also uses `native_decide` for fixed header names.

From the repository root:

```sh
lake -d examples/header-echo build
examples/header-echo/.lake/build/bin/header-echo
```

The service listens on `0.0.0.0:8080`; configure that address in `Main.lean`.

```sh
curl -H 'A: hello' http://127.0.0.1:8080/
curl http://127.0.0.1:8080/
```

Lake builds the dependency's `src/Network.c` automatically. No OpenSSL, database
stubs, Makefile, or certificate is required. The executable can run from another
directory; check its normal Lean/system dependencies with `ldd` before deploying.

The dependency currently points to this modified checkout. A Git dependency
must point to a commit containing the framework changes; upstream `main` does
not yet include them. See [APPLICATION_API.md](../../docs/APPLICATION_API.md).
