import Proxy

namespace FrontendBackend

open LeanServer
open LeanServer.HTTP

private def check (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

private def firstUpstream : Upstream := { host := "backend-a", port := 9001 }
private def secondUpstream : Upstream := { host := "backend-b", port := 9002 }

private def twoCalls (ctx : Context) : List ForwardCall :=
  [ { upstream := firstUpstream, request := ctx.request }
  , { upstream := secondUpstream, request := { ctx.request with target := "/rewritten" } } ]

private def mockRequest (upstream : Upstream) (request : Request) :
    StateM (List String) UpstreamResult := do
  modify (· ++ [upstream.host ++ ":" ++ toString upstream.port])
  pure (.success (Response.text (upstream.host ++ request.target)))

private def combineBodies [Monad m] : Context → List UpstreamResult → m Response
  | _, results =>
    pure (Response.text (String.intercalate "|" (results.map fun result =>
      match result with
      | .success response => String.fromUTF8! response.body
      | .failure message => "failure:" ++ message)))

private def failingRequest (_ : Upstream) (_ : Request) : StateM Unit UpstreamResult :=
  pure (.failure "unreachable")

def proxyTestsMain : IO Unit := do
  let request : Request := { target := "/input" }
  let handler : Handler (StateM (List String)) :=
    proxyHandler twoCalls mockRequest combineBodies
  let (response, calls) := (handler (Context.ofRequest request)).run []
  check "fanout calls each upstream in order" (calls == ["backend-a:9001", "backend-b:9002"])
  check "fanout preserves request-specific rewrites"
    (String.fromUTF8! response.body == "backend-a/input|backend-b/rewritten")

  let single : Handler (StateM (List String)) :=
    proxyHandler (singlePlan firstUpstream) mockRequest firstUpstreamResponse
  let (singleResponse, singleCalls) := (single (Context.ofRequest request)).run []
  check "single upstream is the same generic handler" (singleCalls == ["backend-a:9001"])
  check "single upstream returns its response" (String.fromUTF8! singleResponse.body == "backend-a/input")

  let failed : Handler (StateM Unit) :=
    proxyHandler (singlePlan firstUpstream) failingRequest firstUpstreamResponse
  let (failedResponse, _) := (failed (Context.ofRequest request)).run ()
  check "upstream failure combines as 502" (failedResponse.status == 502)

  let original : Request :=
    { target := "/input?x=1", body := ByteArray.mk #[0, 255, 13, 10]
      headers := #[⟨"X-Username", "caller-user"⟩, ⟨"X-Password", "caller-password"⟩,
        ⟨"X-Trace", "one"⟩, ⟨"X-Trace", "two"⟩,
        ⟨"Host", "client-host"⟩, ⟨"Content-Length", "999"⟩, ⟨"Connection", "keep-alive"⟩] }
  let [rewritten] := singlePlan firstUpstream
    (fun r => { r with method := "POST", target := "/rewritten?x=1" })
    (Context.ofRequest original)
    | throw (IO.userError "singlePlan did not produce exactly one call")
  let encoded := encodeUpstreamRequest rewritten.upstream rewritten.request
  let parsedCorrectly := match parseHTTP1 encoded with
    | .ok (some (forwarded, rest)) =>
      rest.isEmpty && forwarded.method == "POST" && forwarded.target == "/rewritten?x=1" &&
      forwarded.body == original.body &&
      forwarded.headers.getAll "x-username" == #["caller-user"] &&
      forwarded.headers.getAll "x-password" == #["caller-password"] &&
      forwarded.headers.getAll "x-trace" == #["one", "two"] &&
      forwarded.headers.getAll "host" == #["backend-a:9001"] &&
      forwarded.headers.getAll "content-length" == #["4"] &&
      forwarded.headers.getAll "connection" == #["close"]
    | _ => false
  check "caller rewrites request; proxy preserves application headers and rebuilds framing" parsedCorrectly

end FrontendBackend

def main : IO Unit := FrontendBackend.proxyTestsMain
