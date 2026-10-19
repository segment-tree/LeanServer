import LeanServerPure
import LeanServer.Server.HTTPServer

/-!
# Exemplo Básico de Servidor — LeanServer

Demonstra a utilização real da DSL monádica de routing (#18)
e do framework WebApplication para definir endpoints.
-/

open LeanServer
open LeanServer.WebApp

/-- Definição da aplicação usando a DSL monádica de routes -/
def myApp : WebAppState Id := webApp do
  -- Página principal
  get "/" fun _ => WebApp.htmlResponse "<h1>Olá do LeanServer! 🚀</h1><p>Servidor HTTP em Lean 4</p>"

  -- Health check endpoint
  get "/health" fun _ => WebApp.jsonResponse "{\"status\":\"ok\"}"

  -- Informações do servidor
  get "/api/info" fun _ => WebApp.jsonResponse (
    "{\"server\":\"LeanServer\",\"version\":\"0.2.0\",\"protocol\":\"HTTP/1.1\"}"
  )

  -- Métricas simples
  get "/metrics" fun _ => do
    let resp ← WebApp.jsonResponse "{\"requests_total\":0,\"uptime_seconds\":0}"
    pure (resp.withStatus 200)

  -- Criação de recurso (POST)
  post "/api/users" fun ctx => do
    let body := String.fromUTF8! ctx.request.body
    let resp ← WebApp.jsonResponse (Lean.Json.mkObj [
      ("created", Lean.toJson true), ("echo", Lean.toJson body)]).compress
    pure (resp.withStatus 201)

def main (args : List String) : IO Unit := do
  let port := (args.headD "8080").toNat?.getD 0
  if port == 0 || port > 65535 then throw (IO.userError "Invalid port")
  LeanServer.serve { host := "127.0.0.1", port := port.toUInt16 }
    (m := Id) (fun value => pure value) myApp.dispatch
