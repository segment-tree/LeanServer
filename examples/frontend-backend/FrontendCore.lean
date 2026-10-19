import LeanServerPure
import LeanServer.Server.HTTPServer
import Proxy

namespace FrontendBackend

open LeanServer
open LeanServer.HTTP

def unauthorizedResponse : Response := Response.text "Unauthorized" 401

theorem unauthorized_status : unauthorizedResponse.status = 401 := by
  rfl

def credentialsMatch (ctx : Context) : Bool :=
  ctx.request.headers.getAll "x-username" == #["Tom"] &&
    ctx.request.headers.getAll "x-password" == #["123456"]

def backendAddr : Upstream := { host := "127.0.0.1", port := 8081 }

/-- Credentials are frontend policy, not part of the generic proxy protocol. -/
def omitBackendHeader (header : Header) : Bool :=
  let name := headerName header.name
  name == "x-username" || name == "x-password"

def backendRequest (request : Request) : Request :=
  { request with headers := request.headers.filter fun h => !omitBackendHeader h }

def frontendWith [Monad m]
    (requestUpstream : Upstream → Request → m UpstreamResult) : Handler m := fun ctx =>
  if ctx.path == "/login" then
    pure (Response.text "Supply X-Username and X-Password headers")
  else if !credentialsMatch ctx then
    pure unauthorizedResponse
  else
    proxyHandler (singlePlan backendAddr backendRequest) requestUpstream firstUpstreamResponse ctx

def frontend : Handler IO := frontendWith requestUpstreamIO

end FrontendBackend
