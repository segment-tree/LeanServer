import LeanServerPure
import examples.HeaderEchoApp

open LeanServer.HTTP

private def check (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError s!"FAIL {label}")

private def request (bytes : ByteArray) : IO Request :=
  match parseHTTP1 bytes with
  | .ok (some (request, rest)) =>
    if rest.isEmpty then pure request else throw (IO.userError "Unexpected remainder")
  | _ => throw (IO.userError "Expected parsed request")

def main : IO Unit := do
  let req ← request "GET /?x=a?b HTTP/1.1\r\nHost: localhost\r\na: value:with:colons\r\nA: second\r\n\r\n".toUTF8
  check "case insensitive lookup and duplicate order" (req.headers.getAll "A" == #["value:with:colons", "second"])
  let ctx := Context.ofRequest req
  check "query split once" (ctx.path == "/" && ctx.rawQuery == some "x=a?b")
  check "Id handler" ((headerEcho (m := Id) ctx).body == "value:with:colons".toUTF8)
  check "missing A" ((headerEcho (m := Id) (Context.ofRequest {})).status == 400)
  let binary := ByteArray.mk #[0, 255, 13, 10, 128]
  let head := "POST /binary HTTP/1.1\r\nHost: localhost\r\nContent-Length: 5\r\n\r\n".toUTF8
  let parsed ← request (head ++ binary)
  check "binary request body" (parsed.body == binary)
  for i in [:head.size + binary.size] do
    match parseHTTP1 ((head ++ binary).extract 0 i) with
    | .ok none => pure ()
    | _ => throw (IO.userError s!"Incomplete request accepted at {i}")
  let chunked ← request ("POST / HTTP/1.1\r\nHost: localhost\r\nTransfer-Encoding: chunked\r\n\r\n5\r\n".toUTF8 ++
    binary ++ "\r\n0\r\nX-Trailer: yes\r\n\r\n".toUTF8)
  check "chunked binary body" (chunked.body == binary)
  for headers in ["Content-Length: 1\r\nContent-Length: 2", "Transfer-Encoding: chunked\r\nContent-Length: 2",
      "Bad Header: value", "Content-Length: -1"] do
    check "malformed framing rejected" (!(parseHTTP1 s!"POST / HTTP/1.1\r\nHost: x\r\n{headers}\r\n\r\nxx".toUTF8).isOk)
  let fields : Headers := #[⟨":method", "POST"⟩, ⟨":path", "/binary"⟩, ⟨":scheme", "https"⟩,
    ⟨":authority", "localhost"⟩, ⟨"a", "value"⟩, ⟨"a", "second"⟩]
  for version in [Version.http2, .http3] do
    match fromFields version fields binary with
    | .error _ => throw (IO.userError "Protocol adapter failed")
    | .ok r => check "H2/H3 fields preserve bytes and duplicates" (r.body == binary && r.headers.getAll "A" == #["value", "second"])
  check "QPACK literal roundtrip" (QPACK.decode (QPACK.encode fields) == some fields)
  check "QPACK static fields" ((QPACK.decode (ByteArray.mk #[0, 0, 0xd1, 0xd7, 0xc1])).map (·.size) == some 3)
  check "QPACK rejects dynamic reference at zero capacity" ((QPACK.decode (ByteArray.mk #[0, 0, 0x80])).isNone)
  let router : Router Id := ({} : Router Id)
    |>.get "/users/:id" (fun c => Response.text ((c.param "id").getD ""))
    |>.get "/users/*" (fun _ => Response.text "fallback")
  check "first route and parameter extraction" ((router.dispatch (Context.ofRequest { target := "/users/42?q=1" })).body == "42".toUTF8)
  check "404" ((router.dispatch (Context.ofRequest { target := "/missing" })).status == 404)
  check "methods remain case sensitive" ((router.dispatch (Context.ofRequest { target := "/users/42", method := "get" })).status == 404)
  let short : Middleware (StateM Nat) := fun _ _ => do
    modify (· + 1)
    pure (Response.text "denied" 403)
  let effectHandler : Handler (StateM Nat) := fun _ => do
    modify (· + 100)
    pure (Response.text "unexpected")
  let (response, state) := (short effectHandler ctx).run 0
  check "short circuit prevents handler effect" (response.status == 403 && state == 1)
  let reader : Handler (ReaderT String Id) := fun _ => do return Response.text (← read)
  check "ReaderT effect" ((reader ctx "environment").body == "environment".toUTF8)
  let except : Handler (Except String) := fun _ => .error "application failure"
  check "Except effect" (!(except ctx).isOk)
  let record (name : String) : Middleware (StateM (List String)) := fun next c => do
    modify (· ++ [name ++ " before"])
    let response ← next c
    modify (· ++ [name ++ " after"])
    return response
  let base : Handler (StateM (List String)) := fun _ => do
    modify (· ++ ["handler"])
    return Response.text "ok"
  let (_, events) := (Middleware.all [record "a", record "b"] base ctx).run []
  check "middleware request and response order"
    (events == ["a before", "b before", "handler", "b after", "a after"])
  let child : Router Id := ({} : Router Id)
    |>.get "/:id" (fun c => Response.text ((c.param "id").getD ""))
    |>.use (mapResponse (·.withHeader "x-group" "yes"))
  let grouped := ({} : Router Id).group "/api" child
  let groupResponse := grouped.dispatch (Context.ofRequest { target := "/api/42" })
  check "group prefix and middleware"
    (groupResponse.body == "42".toUTF8 && groupResponse.headers.get? "x-group" == some "yes")
  check "group middleware stays scoped"
    ((grouped.dispatch (Context.ofRequest { target := "/elsewhere" })).headers.get? "x-group" == none)
  let generate : StateM Nat String := do modify (· + 1); return "generated"
  let withId := requestId generate (fun _ => pure (Response.text "ok"))
  let (idResponse, calls) := (withId (Context.ofRequest { headers := #[⟨"X-Request-Id", "supplied"⟩] })).run 0
  check "supplied request id skips generation effect"
    (idResponse.headers.get? "x-request-id" == some "supplied" && calls == 0)
  let invalid := (Response.text "x").withHeader "x-bad" "injected\r\nheader: y"
  check "response injection rejected" (!invalid.valid)
  check "HEAD has no payload" ((responseBody "HEAD" (Response.text "hello")).isEmpty)
  check "exhausted health policy" (!(LeanServer.threadPoolHealth 100 100).isUp)
  let health : LeanServer.HealthCheckResult := { name := "quoted\"name", status := .unhealthy "failure\nreason", durationMs := 0 }
  check "health JSON escaping" (Lean.Json.parse health.toJSON).isOk
  check "health HTTP status" ((LeanServer.healthCheckResponse {overall := .unhealthy "failure", checks := [health], serverUpMs := 0, timestamp := 0}).status == 503)
