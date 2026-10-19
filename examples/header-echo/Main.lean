import LeanServerPure
import LeanServer.Server.HTTPServer
import Proof

def main : IO Unit :=
  LeanServer.serve { host := "0.0.0.0", port := 8080 }
    (m := Id) (fun value => pure value) HeaderEchoExample.application
