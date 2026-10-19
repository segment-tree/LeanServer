import LeanServerPure
import LeanServer.Server.HTTPServer
import Proxy

namespace FrontendBackend2

open LeanServer
open LeanServer.HTTP

def unauthorizedResponse : Response := Response.text "Unauthorized" 401

theorem unauthorized_status : unauthorizedResponse.status = 401 := by
  rfl

def credentialsMatch (ctx : Context) : Bool :=
  ctx.request.headers.getAll "x-username" == #["Tom"] &&
    ctx.request.headers.getAll "x-password" == #["123456"]

def backendAddr : Upstream := { host := "127.0.0.1", port := 8081 }
def leftAddr : Upstream := { host := "127.0.0.1", port := 8082 }
def rightAddr : Upstream := { host := "127.0.0.1", port := 8083 }

/-- Credentials are frontend policy, not part of the generic proxy protocol. -/
def omitBackendHeader (header : Header) : Bool :=
  let name := headerName header.name
  name == "x-username" || name == "x-password"

def backendRequest (request : Request) : Request :=
  { request with headers := request.headers.filter fun h => !omitBackendHeader h }

def selectedRelay (request : Request) : Upstream :=
  if request.body.size % 2 == 1 then leftAddr else rightAddr

def frontendWith [Monad m]
    (requestUpstream : Upstream → Request → m UpstreamResult) : Handler m := fun ctx =>
  if ctx.path == "/login" then
    pure (Response.text "Supply X-Username and X-Password headers")
  else if !credentialsMatch ctx then
    pure unauthorizedResponse
  else
    proxyHandler (singlePlan (selectedRelay ctx.request) backendRequest)
      requestUpstream firstUpstreamResponse ctx

def relayWith [Monad m]
    (requestUpstream : Upstream → Request → m UpstreamResult) : Handler m :=
  proxyHandler (singlePlan backendAddr id) requestUpstream firstUpstreamResponse

def frontend : Handler IO := frontendWith requestUpstreamIO

end FrontendBackend2
