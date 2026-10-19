import FrontendCore

namespace FrontendBackend2

def relay : LeanServer.HTTP.Handler IO := relayWith requestUpstreamIO

def relayMain (port : UInt16) : IO Unit :=
  LeanServer.serveIO { host := "127.0.0.1", port } relay

end FrontendBackend2
