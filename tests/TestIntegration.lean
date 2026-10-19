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

/-!
# Integration Test (ROADMAP F2.7)

Validates that all F2 module integrations work correctly:
- F2.1: Middleware pipeline (explicit list & apply)
- F2.2: Health endpoints (explicit router)
- F2.3: Metrics endpoint (explicit router)
- F2.4: Graceful shutdown handler (registry)
- F2.5: Config hot-reload handler (registry)
- F2.6: Explicit distributed tracing middleware
-/

open LeanServer

def passed (name : String) : IO Unit :=
  IO.println s!"  ✅ {name}"

/-- Check if `needle` appears as a substring in `haystack` -/
def contains (haystack needle : String) : Bool :=
  let hn := haystack.length
  let nn := needle.length
  if nn > hn || nn == 0 then nn == 0
  else Id.run do
    let chars := haystack.toList
    let nchars := needle.toList
    for i in List.range (hn - nn + 1) do
      let slice := (chars.drop i).take nn
      if slice == nchars then return true
    return false

def failed (name : String) (reason : String) : IO Unit :=
  IO.eprintln s!"  ❌ {name}: {reason}"

def assert (name : String) (cond : Bool) (failMsg : String := "assertion failed") : IO Bool := do
  if cond then
    passed name
    return true
  else
    failed name failMsg
    return false

def main : IO Unit := do
  IO.println "🧪 Running Integration Tests (ROADMAP F2.7)"
  IO.println ""

  let mut total := 0
  let mut pass := 0

  -- Concurrent admission/release must preserve the same counts observed by probes.
  let admissions ← (List.range 32).mapM fun i => IO.asTask (poolAdmit 0 (10000 + i))
  for task in admissions do
    if !(← IO.ofExcept (← IO.wait task)) then throw (IO.userError "Unexpected pool admission failure")
  let (active, _, _) ← getPoolStats
  let observed ← getActiveThreadCount
  if active != 32 || observed != 32 then throw (IO.userError "Connection count lost during concurrent admission")
  let releases ← (List.range 32).mapM fun i => IO.asTask (poolRelease (10000 + i))
  for task in releases do IO.ofExcept (← IO.wait task)
  let (remaining, _, _) ← getPoolStats
  if remaining != 0 then throw (IO.userError "Connection count leaked after release")
  passed "Concurrent pool admission, probe counts, release"

  -- ==========================================
  -- F2.1: Middleware Pipeline
  -- ==========================================
  IO.println "── F2.1: Middleware Pipeline ──"

  let mws : List (HTTP.Middleware IO) := [
    RequestId.requestIdMiddleware {}, advancedCORSMiddleware {},
    contentNegotiationMiddleware, compressionMiddleware {} ]
  total := total + 1
  let ok ← assert "Explicit middleware pipeline" (mws.length == 4)
  if ok then pass := pass + 1

  let ctx := HTTP.Context.ofRequest { headers := #[⟨"x-request-id", "incoming-id"⟩,
    ⟨"origin", "https://example.com"⟩] }
  let handler : HTTP.Handler IO := fun ctx =>
    pure (HTTP.Response.text ((ctx.local "request-id").getD "missing"))
  let applied ← HTTP.Middleware.all mws handler ctx
  total := total + 1
  let ok ← assert "Request ID available inside handler and response"
    (applied.body == "incoming-id".toUTF8 && applied.headers.get? "x-request-id" == some "incoming-id")
  if ok then pass := pass + 1
  total := total + 1
  let ok ← assert "Canonical middleware adds CORS and Vary"
    (applied.headers.get? "access-control-allow-origin" == some "*" && (applied.headers.get? "vary").isSome)
  if ok then pass := pass + 1

  -- ==========================================
  -- F2.2: Health Endpoints
  -- ==========================================
  IO.println "── F2.2: Health Endpoints ──"

  -- Test: register health route
  total := total + 1
  let router : HTTP.Router IO := ({} : HTTP.Router IO).get "/health/deep" fun _ => do
    let report ← deepHealthCheck "cert.pem" "key.pem"
    pure (healthCheckResponse report)
  let found := (HTTP.selectRoute "GET" "/health/deep" router.routes).map (·.1.handler)
  let ok ← assert "Register /health/deep route" found.isSome
  if ok then pass := pass + 1

  -- Test: register readiness route
  total := total + 1
  let router := router.get "/ready" fun _ => do
    let report ← readinessCheck
    pure (healthCheckResponse report)
  let found := (HTTP.selectRoute "GET" "/ready" router.routes).map (·.1.handler)
  let ok ← assert "Register /ready route" found.isSome
  if ok then pass := pass + 1

  -- Test: register liveness route
  total := total + 1
  let router := router.get "/livez" fun _ => do
    let report ← livenessCheck
    pure (healthCheckResponse report)
  let found := (HTTP.selectRoute "GET" "/livez" router.routes).map (·.1.handler)
  let ok ← assert "Register /livez route" found.isSome
  if ok then pass := pass + 1

  -- Test: call health handler
  total := total + 1
  match found with
  | some handler =>
    let resp ← handler (HTTP.Context.ofRequest {})
    let isJson := ((resp.headers.get? "content-type").getD "").startsWith "application/json"
    let ok ← assert "Health response is JSON" isJson
      s!"contentType={((resp.headers.get? "content-type").getD "")}"
    if ok then pass := pass + 1
  | none =>
    failed "Health response is JSON" "no handler found"

  IO.println ""

  -- ==========================================
  -- F2.3: Metrics Endpoint
  -- ==========================================
  IO.println "── F2.3: Metrics Endpoint ──"

  -- Test: register metrics route
  total := total + 1
  let router := router.get "/metrics" fun _ => do
    let body ← generatePrometheusMetrics
    return (HTTP.Response.text body).withHeader "content-type" "text/plain; version=0.0.4; charset=utf-8"
  let found := (HTTP.selectRoute "GET" "/metrics" router.routes).map (·.1.handler)
  let ok ← assert "Register /metrics route" found.isSome
  if ok then pass := pass + 1

  -- Test: call metrics handler and verify Prometheus format
  total := total + 1
  match found with
  | some handler =>
    let resp ← handler (HTTP.Context.ofRequest {})
    let hasHelp := contains (String.fromUTF8! resp.body) "# HELP" || contains (String.fromUTF8! resp.body) "leanserver"
    let ok ← assert "Metrics response is Prometheus format" hasHelp
      s!"body length={resp.body.size}"
    if ok then pass := pass + 1
  | none =>
    failed "Metrics response is Prometheus format" "no handler found"

  IO.println ""

  -- ==========================================
  -- F2.4: Graceful Shutdown
  -- ==========================================
  IO.println "── F2.4: Graceful Shutdown ──"

  -- Test: register shutdown handler
  total := total + 1
  let shutdownCalled ← IO.mkRef false
  registerShutdownHandler do
    shutdownCalled.set true
  let handler ← getShutdownHandler
  let ok ← assert "Register shutdown handler" handler.isSome
  if ok then pass := pass + 1

  -- Test: invoke shutdown handler
  total := total + 1
  match handler with
  | some h =>
    h
    let called ← shutdownCalled.get
    let ok ← assert "Shutdown handler invoked" called
    if ok then pass := pass + 1
  | none =>
    failed "Shutdown handler invoked" "no handler"

  -- Test: ShutdownCoordinator creates correctly
  total := total + 1
  let coord ← ShutdownCoordinator.create { drainTimeoutMs := 5000 }
  let isDraining ← coord.isDraining
  let ok ← assert "ShutdownCoordinator starts in running state" (!isDraining)
  if ok then pass := pass + 1

  IO.println ""

  -- ==========================================
  -- F2.5: Config Hot-Reload
  -- ==========================================
  IO.println "── F2.5: Config Hot-Reload ──"

  -- Test: register reload handler
  total := total + 1
  let reloadCalled ← IO.mkRef false
  registerReloadHandler do
    reloadCalled.set true
  let handler ← getReloadHandler
  let ok ← assert "Register reload handler" handler.isSome
  if ok then pass := pass + 1

  -- Test: invoke reload handler
  total := total + 1
  match handler with
  | some h =>
    h
    let called ← reloadCalled.get
    let ok ← assert "Reload handler invoked" called
    if ok then pass := pass + 1
  | none =>
    failed "Reload handler invoked" "no handler"

  -- Test: force config reload (file may not exist = graceful no-op)
  total := total + 1
  let diff ← forceConfigReload "nonexistent_config_12345.conf"
  let ok ← assert "Force reload of missing file returns none" diff.isNone
  if ok then pass := pass + 1

  IO.println ""

  -- ==========================================
  -- F2.6: Distributed Tracing
  -- ==========================================
  IO.println "── F2.6: Distributed Tracing ──"

  let observed ← IO.mkRef ""
  let traced ← tracingMiddleware (fun ctx => do
    observed.set ((ctx.local "traceparent").getD "")
    pure (HTTP.Response.text "traced")) (HTTP.Context.ofRequest {})
  total := total + 1
  let ok ← assert "Tracing spans actual handler"
    ((← observed.get) == (traced.headers.get? "traceparent").getD "" && !(← observed.get).isEmpty)
  if ok then pass := pass + 1
  total := total + 1
  let ok ← assert "Traceparent has four fields"
    ((((traced.headers.get? "traceparent").getD "").splitOn "-").length == 4)
  if ok then pass := pass + 1
  total := total + 1
  let ok ← assert "Span is collected after handler" (!(← drainSpans).isEmpty)
  if ok then pass := pass + 1

  let tracingTasks ← (List.range 32).mapM fun _ => IO.asTask do
    tracingMiddleware (fun _ => pure (HTTP.Response.text "ok")) (HTTP.Context.ofRequest {})
  for task in tracingTasks do
    let _ ← IO.ofExcept (← IO.wait task)
  let collected ← drainSpans
  if collected.length != 32 then
    throw (IO.userError s!"Lost spans during concurrent collection: expected 32, got {collected.length}")
  let failedAsExpected ← try
    let _ ← tracingMiddleware (fun _ => throw (IO.userError "traced failure")) (HTTP.Context.ofRequest {})
    pure false
  catch _ => pure true
  let failureSpans ← drainSpans
  if !failedAsExpected || !(failureSpans.any (fun span => span.status == .error_)) then
    throw (IO.userError "Tracing swallowed exception or lost error span")
  passed "Concurrent tracing and exception recording"

  -- ==========================================
  -- Route lookup: non-existent route returns none
  -- ==========================================
  IO.println "── Negative Tests ──"

  total := total + 1
  let notFound := HTTP.selectRoute "DELETE" "/nonexistent" router.routes
  let ok ← assert "Non-existent route returns none" notFound.isNone
  if ok then pass := pass + 1

  total := total + 1
  let wrongMethod := HTTP.selectRoute "POST" "/health/deep" router.routes
  let ok ← assert "Wrong method returns none" wrongMethod.isNone
  if ok then pass := pass + 1

  IO.println ""

  -- ==========================================
  -- Summary
  -- ==========================================
  IO.println "══════════════════════════════════════"
  if pass == total then
    IO.println s!"✅ All {pass}/{total} integration tests passed!"
  else
    IO.println s!"❌ {pass}/{total} integration tests passed ({total - pass} failed)"
    IO.eprintln s!"FAIL: {total - pass} test(s) failed"
    throw (IO.userError s!"{total - pass} integration tests failed")
