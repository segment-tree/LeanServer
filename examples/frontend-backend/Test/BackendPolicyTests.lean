import BackendCore

namespace FrontendBackend

open LeanServer
open LeanServer.HTTP

private def check (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {name}" else throw (IO.userError s!"FAIL {name}")

def backendPolicyTestsMain : IO Unit := do
  let getResponse := backendCore (m := Id)
    (Context.ofRequest { method := "GET", target := "/resource?from=frontend" })
  let getBody := String.fromUTF8! getResponse.body
  check "backend core serves GET resource"
    (getResponse.status == 200 && getBody.contains "sample-value" &&
      getBody.contains "/resource?from=frontend")

  let postResponse := backendCore (m := Id)
    (Context.ofRequest { method := "POST", target := "/resource" })
  check "backend core rejects non-GET"
    (postResponse.status == 405 && postResponse.headers.get? "allow" == some "GET")

  let missingResponse := backendCore (m := Id)
    (Context.ofRequest { method := "GET", target := "/missing" })
  check "backend core rejects unknown route" (missingResponse.status == 404)

end FrontendBackend

def main : IO Unit := FrontendBackend.backendPolicyTestsMain
