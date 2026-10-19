import LeanServer.Server.HTTPServer
import examples.HeaderEchoApp
import LeanServer.Server.RequestId
import LeanServer.Web.SampleWebApp

open LeanServer.HTTP

def application : Handler (ReaderT String IO) := fun ctx => do
  if ctx.path == "/binary" then return { body := ctx.request.body }
  if ctx.path == "/error" then throw (IO.userError "test exception")
  if ctx.path == "/environment" then return Response.text (← read)
  if ctx.path == "/compressed" then return Response.ok (String.ofList (List.replicate 70000 'x'))
  if ctx.path == "/compressed-binary" then return {
    headers := #[⟨"content-type", "text/plain"⟩], body := ctx.request.body }
  if ctx.path == "/request-id" then return Response.text ((ctx.local "request-id").getD "missing")
  if ctx.path.startsWith "/users" then return ← LeanServer.createSampleWebApp.dispatch ctx
  if ctx.path == "/large" then return Response.text (String.ofList (List.replicate 100000 'x'))
  if ctx.path == "/invalid" then return (Response.text "bad").withHeader "x-bad" "a\r\nb"
  if ctx.path == "/cookies" then return { headers := #[⟨"set-cookie", "a=1"⟩, ⟨"set-cookie", "b=2"⟩] }
  headerEcho ctx

def main (args : List String) : IO Unit := do
  let port := (args.headD "18081").toNat?.getD 18081
  let tls := args.length > 1
  let config : LeanServer.ServerConfig := {
    port := port.toUInt16
    host := "127.0.0.1"
    enableTLS := tls
    enableHTTP2 := tls
    enableHTTP3 := tls
    certPath := args[1]?.getD "cert.pem"
    keyPath := args[2]?.getD "key.pem"
    requestTimeoutMs := 5000 }
  LeanServer.serve config
    (fun action => action "effect environment")
    (Middleware.all [
      LeanServer.RequestId.requestIdMiddlewareWith (liftM (LeanServer.RequestId.generateRequestId)),
      LeanServer.advancedCORSMiddleware { allowedOrigins := [.exact "https://example.com"], allowCredentials := true },
      LeanServer.compressionMiddleware {}
    ] application)
