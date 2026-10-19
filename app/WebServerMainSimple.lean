import LeanServer.Web.SampleWebApp
import LeanServer.Server.HTTPServer

/-- Run the same router used by WebAppTests through the library's actual server. -/
def main (args : List String) : IO Unit := do
  let port := (args.headD "8080").toNat?.getD 0
  if port == 0 || port > 65535 then throw (IO.userError "Invalid port")
  LeanServer.serve { host := "127.0.0.1", port := port.toUInt16 }
    (m := Id) (fun value => pure value) LeanServer.createSampleWebApp.dispatch
