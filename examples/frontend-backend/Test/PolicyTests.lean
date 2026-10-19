import FrontendCore

namespace FrontendBackend

open LeanServer
open LeanServer.HTTP

private def check (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

private def recordingUpstream (upstream : Upstream) (request : Request) :
    StateM (List ForwardCall) UpstreamResult := do
  modify (· ++ [{ upstream, request }])
  pure (.success (Response.text "backend response"))

private def request (headers : Headers := #[]) (target : String := "/resource") : Context :=
  Context.ofRequest { target, headers }

def frontendPolicyTestsMain : IO Unit := do
  let unauthenticated := (frontendWith recordingUpstream (request)).run []
  check "frontend rejects missing credentials"
    (unauthenticated.1.status == 401 && unauthenticated.2.isEmpty)

  let wrongPassword := (frontendWith recordingUpstream
    (request #[⟨"X-Username", "Tom"⟩, ⟨"X-Password", "wrong"⟩])).run []
  check "frontend rejects wrong credentials"
    (wrongPassword.1.status == 401 && wrongPassword.2.isEmpty)

  let duplicateUsername := (frontendWith recordingUpstream
    (request #[⟨"X-Username", "Tom"⟩, ⟨"X-Username", "Tom"⟩,
      ⟨"X-Password", "123456"⟩])).run []
  check "frontend rejects duplicate credentials"
    (duplicateUsername.1.status == 401 && duplicateUsername.2.isEmpty)

  let login := (frontendWith recordingUpstream
    (request #[] "/login")).run []
  check "login endpoint does not call backend"
    (login.1.status == 200 && login.2.isEmpty)

  let authenticated := (frontendWith recordingUpstream
    (request #[⟨"X-Username", "Tom"⟩, ⟨"X-Password", "123456"⟩,
      ⟨"X-Trace", "keep-me"⟩] "/resource?x=1")).run []
  let correctCall := match authenticated.2 with
    | [call] =>
      call.upstream == backendAddr && call.request.method == "GET" &&
      call.request.target == "/resource?x=1" &&
      call.request.headers.getAll "x-username" == #[] &&
      call.request.headers.getAll "x-password" == #[] &&
      call.request.headers.getAll "x-trace" == #["keep-me"]
    | _ => false
  check "frontend selects backend and removes credentials before the upstream call"
    (authenticated.1.status == 200 &&
      String.fromUTF8! authenticated.1.body == "backend response" &&
      correctCall)

end FrontendBackend

def main : IO Unit := FrontendBackend.frontendPolicyTestsMain
