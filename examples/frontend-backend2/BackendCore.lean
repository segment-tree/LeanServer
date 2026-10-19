import LeanServerPure
import LeanServer.Server.HTTPServer

namespace FrontendBackend2

open LeanServer
open LeanServer.HTTP

def resource (target : String) : Response :=
  Response.json (Lean.Json.mkObj [
    ("resource", Lean.toJson "sample"),
    ("value", Lean.toJson "sample-value"),
    ("target", Lean.toJson target)]).compress

def backendCore [Monad m] : Handler m := fun ctx =>
  if ctx.path != "/resource" then
    pure (Response.notFound "Backend route not found")
  else if ctx.request.method == "GET" then
    pure (resource ctx.request.target)
  else
    pure ((Response.text "Backend supports GET only" 405).withHeader "allow" "GET")

def backend : Handler IO := backendCore

end FrontendBackend2
