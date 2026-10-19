import FrontendCore

namespace FrontendBackend

private def optionValue (args : List String) (name fallback : String) : String :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => value
  | _ => fallback

def frontendMain (args : List String) : IO Unit := do
  let port := (optionValue args "--port" "8080").toNat?.getD 8080
  if port == 0 || port > 65535 then throw (IO.userError "Invalid frontend port")
  LeanServer.serveIO { host := "0.0.0.0", port := port.toUInt16 } frontend

end FrontendBackend

def main (args : List String) : IO Unit := FrontendBackend.frontendMain args
