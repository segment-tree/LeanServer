import LeanServerPure
import LeanServer.Server.HTTPServer
import examples.HeaderEchoApp

private def option (args : List String) (name fallback : String) : String :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => value
  | _ => fallback

def main (args : List String) : IO Unit := do
  let port := (option args "--port" "8080").toNat?.getD 8080
  if port == 0 || port > 65535 then throw (IO.userError "Invalid port")
  let tls := args.contains "--tls"
  LeanServer.serve {
    port := port.toUInt16
    host := option args "--host" "127.0.0.1"
    enableTLS := tls
    enableHTTP2 := tls
    enableHTTP3 := args.contains "--h3"
    certPath := option args "--cert" "cert.pem"
    keyPath := option args "--key" "key.pem"
  } (m := Id) (fun value => pure value) headerEcho
