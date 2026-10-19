-- Real HTTPS Server Main
import LeanServer.Server.HTTPServer

def main : IO Unit := do
  LeanServer.serveIO { port := 4433, enableTLS := true, enableHTTP2 := true }
    (fun _ => pure (LeanServer.HTTP.Response.text "LeanServer"))
