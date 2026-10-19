import BackendCore

namespace FrontendBackend

private def port (args : List String) : UInt16 :=
  (args.headD "8081").toNat?.getD 8081 |>.toUInt16

def backendMain (args : List String) : IO Unit := do
  LeanServer.serveIO { host := "127.0.0.1", port := port args } backend

end FrontendBackend

def main (args : List String) : IO Unit := FrontendBackend.backendMain args
