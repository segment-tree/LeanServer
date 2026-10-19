import LeanServerPure
import LeanServer.Crypto.Crypto
import LeanServer.Protocol.HTTP2
import LeanServer.Protocol.HTTP3
import LeanServer.Protocol.WebSocketOverHTTP2
import LeanServer.Server.LoadBalancer
import LeanServer.Server.HTTPServer
import LeanServer.Server.CORSMiddleware
import LeanServer.Server.ContentNegotiation
import LeanServer.Server.ResponseCompression
import LeanServer.Server.RequestId
import LeanServer.Server.DistributedTracing
import LeanServer.Server.HealthCheck
import LeanServer.Server.Metrics
import LeanServer.Server.GracefulShutdown
import LeanServer.Server.ConfigReload
import Init.System.IO

open LeanServer
open UInt32

def main : IO Unit := do
  IO.eprintln "🚀 Starting Real Lean 4 HTTPS Server..."

  -- Register external middleware (see ROADMAP.md F2.1)
  IO.eprintln "🔧 Registering middleware pipeline..."
  let middlewares : List (HTTP.Middleware IO) := [
    RequestId.requestIdMiddleware {},  -- X-Request-Id header
    advancedCORSMiddleware {},        -- Configurable CORS
    contentNegotiationMiddleware,     -- Content-Type negotiation
    compressionMiddleware {},         -- Response compression (gzip)
    tracingMiddleware
  ]
  IO.eprintln "   ✅ Registered: RequestId, CORS, ContentNegotiation, Compression"

  -- Register health endpoints (see ROADMAP.md F2.2)
  IO.eprintln "🩺 Registering health & metrics endpoints..."
  let router : HTTP.Router IO := ({} : HTTP.Router IO).get "/health/deep" fun _ => do
    let report ← deepHealthCheck "cert.pem" "key.pem"
    pure (healthCheckResponse report)
  let router := router.get "/ready" fun _ => do
    let report ← readinessCheck
    pure (healthCheckResponse report)
  let router := router.get "/livez" fun _ => do
    let report ← livenessCheck
    pure (healthCheckResponse report)

  -- Register metrics endpoint (see ROADMAP.md F2.3)
  let router := router.get "/metrics" fun _ => do
    let body ← generatePrometheusMetrics
    return (HTTP.Response.text body).withHeader "content-type" "text/plain; version=0.0.4; charset=utf-8"
  IO.eprintln "   ✅ Registered: /health/deep, /ready, /livez, /metrics"

  -- Register graceful shutdown coordinator (see ROADMAP.md F2.4)
  IO.eprintln "🛑 Registering graceful shutdown coordinator..."
  let shutdownCoord ← ShutdownCoordinator.create { drainTimeoutMs := 30000, pollIntervalMs := 500 }
  registerShutdownHandler do
    let _ ← shutdownCoord.runShutdown
    let summary ← shutdownCoord.summary
    IO.eprintln s!"   📊 Shutdown summary: phase={summary.phase}, duration={summary.durationMs}ms, connectionsAtStart={summary.connectionsAtStart}"
  IO.eprintln "   ✅ ShutdownCoordinator registered (drain=30s, poll=500ms)"

  -- Register config hot-reload handler (see ROADMAP.md F2.5)
  IO.eprintln "🔄 Registering config hot-reload..."
  startConfigWatcher "server.config" 10  -- poll every 10 seconds
  registerReloadHandler do
    IO.eprintln "🔄 SIGHUP received — reloading server.config..."
    let diff ← forceConfigReload "server.config"
    match diff with
    | some d =>
      IO.eprintln s!"   ✅ Config reloaded ({d.changes.length} changes)"
      for c in d.changes do
        IO.eprintln s!"   • {c}"
    | none => IO.eprintln "   ℹ️  No config changes detected"
  IO.eprintln "   ✅ ConfigReload registered (poll=10s, SIGHUP supported)"

  -- Load Credentials
  IO.eprintln "🔑 Loading credentials..."
  let certOpt ← LeanServer.loadCertificateDER "cert.pem"
  let keyOpt ← LeanServer.loadPrivateKey "key.pem"

  if Option.isNone certOpt || Option.isNone keyOpt then
    IO.eprintln "❌ Failed to load cert.pem or key.pem"
    IO.eprintln "⚠️ Please generate them: openssl req -x509 -newkey rsa:2048 -keyout key.pem -out cert.pem -days 365 -nodes"
    return

  IO.eprintln "✅ Credentials loaded"

  LeanServer.serveIO { port := 4433, enableTLS := true, enableHTTP2 := true }
    (HTTP.Middleware.all middlewares router.dispatch)
