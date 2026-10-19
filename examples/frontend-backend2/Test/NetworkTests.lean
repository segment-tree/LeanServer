import Proof.Proof

namespace FrontendBackend2.Test

open LeanServer.HTTP Proof

private def check (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

/-- A concrete inhabitant of exactly the two environmental contracts. -/
def reliable (graph : NetworkGraph) : Contracts graph where
  socket := { send := fun _ _ _ payload => payload, sent := by intros; rfl }
  transport := { receive := fun _ _ _ payload => payload, delivered := by intros; rfl }

private def source : Upstream := ⟨"198.51.100.9", 54321⟩
private def graph := frontendBackendGraph source

private def credentials : String := "X-Username: Tom\r\nX-Password: 123456\r\n"

private def raw (body : ByteArray) (headers : String := credentials)
    (target : String := "/resource") (close : Bool := true) : ByteArray :=
  ("GET " ++ target ++ " HTTP/1.1\r\nHost: example\r\n" ++ headers ++
    "Content-Length: " ++ toString body.size ++ "\r\n" ++
    (if close then "Connection: close\r\n" else "") ++ "\r\n").toUTF8 ++ body

private def isResource (wire : ByteArray) : Bool :=
  match observed graph (reliable graph) wire, expectedResource wire with
  | some actual, some expected => actual.status == expected.status && actual.body == expected.body
  | _, _ => false

private def isRejected (wire : ByteArray) : Bool :=
  match observed graph (reliable graph) wire with
  | some response => response.status == 401 && response.body == "Unauthorized".toUTF8
  | none => false

private def routedTo (wire : ByteArray) (address : Upstream) : Bool :=
  match completeRequest wire with
  | none => false
  | some request =>
    let result := ServiceProofs.runFrontend (.success (Response.text "ok")) (Context.ofRequest request)
    match result.2 with
    | [call] => call.upstream == address && call.request.body == request.body &&
        call.request.headers.getAll "x-username" == #[] &&
        call.request.headers.getAll "x-password" == #[]
    | _ => false

private def twoHopPayload (wire : ByteArray) : Bool := Id.run do
  let some request := completeRequest wire | return false
  let some middle := completeRequest (encodeUpstreamRequest (selectedRelay request) (backendRequest request))
    | return false
  let relayCalls := ((relayWith (ServiceProofs.recordUpstream (.success (Response.text "ok")))
    (Context.ofRequest middle)).run []).2
  let [call] := relayCalls | return false
  let some finalRequest := completeRequest (encodeUpstreamRequest call.upstream call.request)
    | return false
  return call.upstream == backendAddr && finalRequest.method == request.method &&
    finalRequest.target == request.target && finalRequest.body == request.body &&
    finalRequest.headers.getAll "x-username" == #[] &&
    finalRequest.headers.getAll "x-password" == #[] &&
    finalRequest.headers.getAll "x-trace" == #["retained : value"] &&
    finalRequest.headers.getAll "host" == #["127.0.0.1:8081"]

def networkTestsMain : IO Unit := do
  for (label, body, address) in [
      ("odd", "a".toUTF8, leftAddr), ("even", "ab".toUTF8, rightAddr),
      ("empty", ByteArray.empty, rightAddr),
      ("binary odd", ByteArray.mk #[255, 0, 13, 10, 128], leftAddr),
      ("binary even", ByteArray.mk #[255, 0, 13, 10], rightAddr)] do
    let wire := raw body
    check s!"{label}: selected branch and full graph resource" (routedTo wire address && isResource wire)

  check "query target and keep-alive response"
    (isResource (raw "abc".toUTF8 credentials "/resource?x=1&y=two" false))
  for body in ["a".toUTF8, "ab".toUTF8] do
    check "missing credentials rejected" (isRejected (raw body ""))
    check "wrong password rejected" (isRejected (raw body "X-Username: Tom\r\nX-Password: wrong\r\n"))
    check "wrong username rejected" (isRejected (raw body "X-Username: Other\r\nX-Password: 123456\r\n"))
    check "duplicate username rejected" (isRejected (raw body (credentials ++ "x-USERNAME: Tom\r\n")))
    check "duplicate password rejected" (isRejected (raw body (credentials ++ "x-PASSWORD: 123456\r\n")))

  let chunked := ("GET /resource HTTP/1.1\r\nHost: example\r\n" ++ credentials ++
    "Transfer-Encoding: chunked\r\n\r\n1\r\na\r\n2\r\nbc\r\n0\r\n\r\n").toUTF8
  check "chunked parity uses decoded body (3 bytes)" (routedTo chunked leftAddr && isResource chunked)
  let chunkedEven := ("GET /resource HTTP/1.1\r\nHost: example\r\n" ++ credentials ++
    "Transfer-Encoding: chunked\r\n\r\n1\r\na\r\n1\r\nb\r\n0\r\n\r\n").toUTF8
  check "chunked even body uses right" (routedTo chunkedEven rightAddr && isResource chunkedEven)

  check "two hops preserve binary payload, target, trace and remove credentials"
    (twoHopPayload (raw (ByteArray.mk #[255, 0, 13, 10, 128])
      (credentials ++ "X-Trace:\tretained : value \t\r\n") "/resource?through=relay"))

  -- 63 original headers, almost 48 KiB of header content, and an 8 KiB target.
  let longValue := String.ofList (List.replicate (48 * 1024 - 128) 'z')
  let longTarget := "/resource?" ++ String.ofList (List.replicate (8 * 1024 - 10) 'q')
  let padding := String.join (List.replicate 58 "X:\r\n")
  let boundary := raw "abc".toUTF8 (credentials ++ padding ++ "X:" ++ longValue ++ "\r\n") longTarget false
  let some request := completeRequest boundary | throw (IO.userError "boundary request did not parse")
  check "boundary input stays in the original theorem scope"
    (request.headers.size == 63 && headerContentBytes request.headers ≤ 48 * 1024 &&
      request.target.utf8ByteSize == 8 * 1024)
  check "boundary request survives both encodings" (isResource boundary)

  let otherGraph := frontendBackendGraph ⟨"203.0.113.27", 1⟩
  let wire := raw "a".toUTF8
  check "changing source IP and source port preserves observation"
    (match observed graph (reliable graph) wire, observed otherGraph (reliable otherGraph) wire with
     | some a, some b => a.status == b.status && a.body == b.body
     | _, _ => false)
  for node in [(1 : Fin 4), 2, 3] do
    check "client cannot enter a relay or backend directly"
      ((observedAt graph (reliable graph) node wire).isNone)
  check "incomplete request is not dispatched"
    ((observed graph (reliable graph) "GET /resource HTTP/1.1\r\n".toUTF8).isNone)

end FrontendBackend2.Test

def main : IO Unit := FrontendBackend2.Test.networkTestsMain
