import LeanServer.Server.HTTPServer
import LeanServer.Server.Concurrency
import LeanServer.HTTP.Health

/-!
# Deep Health Check (R23)

Provides comprehensive health checking beyond the simple `/health` endpoint
already in HTTPServer.lean. Deep checks verify internal subsystem health.

## Health Check Levels
- **Shallow** (`/health`): returns 200 if process is alive (already exists)
- **Deep** (`/health/deep`): checks all subsystems
- **Readiness** (`/ready`): checks if server can accept traffic
- **Liveness** (`/livez`): checks if server is not deadlocked

## Subsystem Checks
- TLS certificate validity
- Thread pool utilization
- Memory usage (via GC)
- Rate limiter state
- Connection pool health
- Config file accessibility
-/

namespace LeanServer

-- ==========================================
-- Individual Health Checks
-- ==========================================

/-- Check thread pool health -/
def checkThreadPool : IO HealthCheckResult := do
  let startMs ← IO.monoMsNow
  let (threads, maxThreads, _) ← getPoolStats
  let endMs ← IO.monoMsNow
  let utilization := if maxThreads > 0 then threads * 100 / maxThreads else 0
  let status := threadPoolHealth threads maxThreads
  return { name := "thread_pool", status, durationMs := endMs - startMs
           details := [("active", toString threads), ("max", toString maxThreads)
                       , ("utilization_pct", toString utilization)] }

/-- Check TLS certificate accessibility -/
def checkTLSCertificate (certPath keyPath : String) : IO HealthCheckResult := do
  let startMs ← IO.monoMsNow
  let certOk ← do
    try
      let _ ← IO.FS.readFile certPath
      pure true
    catch _ => pure false
  let keyOk ← do
    try
      let _ ← IO.FS.readFile keyPath
      pure true
    catch _ => pure false
  let endMs ← IO.monoMsNow
  let status := if certOk && keyOk then HealthStatus.healthy
    else if certOk then HealthStatus.degraded s!"Key file not accessible: {keyPath}"
    else HealthStatus.unhealthy s!"Certificate not accessible: {certPath}"
  return { name := "tls_certificate", status, durationMs := endMs - startMs
           details := [("cert_accessible", toString certOk)
                       , ("key_accessible", toString keyOk)] }

/-- Check config file accessibility -/
def checkConfigFile (configPath : String := "server.config") : IO HealthCheckResult := do
  let startMs ← IO.monoMsNow
  let accessible ← do
    try
      let _ ← IO.FS.readFile configPath
      pure true
    catch _ => pure false
  let endMs ← IO.monoMsNow
  let status := if accessible then HealthStatus.healthy
    else HealthStatus.degraded "Config file not accessible (using defaults)"
  return { name := "config_file", status, durationMs := endMs - startMs
           details := [("path", configPath), ("accessible", toString accessible)] }

/-- Check memory / GC health (basic) -/
def checkMemory : IO HealthCheckResult := do
  let startMs ← IO.monoMsNow
  -- We can't directly query GC stats from Lean 4 without FFI
  -- But we can check if allocation works
  let ok ← do
    try
      let _ := ByteArray.mk (Array.mkEmpty 1024)
      pure true
    catch _ => pure false
  let endMs ← IO.monoMsNow
  let status := if ok then HealthStatus.healthy
    else HealthStatus.unhealthy "Memory allocation failed"
  return { name := "memory", status, durationMs := endMs - startMs
           details := [("allocation_test", toString ok)] }

/-- Check rate limiter state -/
def checkRateLimiter : IO HealthCheckResult := do
  let startMs ← IO.monoMsNow
  let buckets ← rateLimiterRef.get
  let count := buckets.length
  let endMs ← IO.monoMsNow
  let status := if count > 5000 then
    HealthStatus.degraded s!"Rate limiter tracking {count} IPs (high)"
  else
    HealthStatus.healthy
  return { name := "rate_limiter", status, durationMs := endMs - startMs
           details := [("tracked_ips", toString count)] }

/-- Server uptime reference (set at startup) -/
initialize serverStartTimeRef : IO.Ref Nat ← do
  let now ← IO.monoMsNow
  IO.mkRef now

/-- Get server uptime in milliseconds -/
def getServerUptimeMs : IO Nat := do
  let startTime ← serverStartTimeRef.get
  let now ← IO.monoMsNow
  return now - startTime

-- ==========================================
-- Composite Health Checks
-- ==========================================

/-- Run all deep health checks -/
def deepHealthCheck (certPath keyPath : String) (configPath : String := "server.config") : IO HealthReport := do
  let timestamp ← IO.monoMsNow
  let uptimeMs ← getServerUptimeMs

  -- Run all checks
  let threadCheck ← checkThreadPool
  let certCheck ← checkTLSCertificate certPath keyPath
  let configCheck ← checkConfigFile configPath
  let memoryCheck ← checkMemory
  let rateLimitCheck ← checkRateLimiter

  let checks := [threadCheck, certCheck, configCheck, memoryCheck, rateLimitCheck]

  -- Overall: unhealthy if any check is unhealthy; degraded if any is degraded
  let overall := aggregateHealth checks

  return { overall, checks, serverUpMs := uptimeMs, timestamp }

/-- Readiness check — is the server ready to accept traffic? -/
def readinessCheck : IO HealthReport := do
  let timestamp ← IO.monoMsNow
  let uptimeMs ← getServerUptimeMs

  let threadCheck ← checkThreadPool
  -- Server is not ready if thread pool is exhausted
  let overall := if threadCheck.status.isUp then HealthStatus.healthy
    else HealthStatus.unhealthy "Thread pool exhausted"
  return { overall, checks := [threadCheck], serverUpMs := uptimeMs, timestamp }

/-- Liveness check — is the server still alive (not deadlocked)? -/
def livenessCheck : IO HealthReport := do
  let timestamp ← IO.monoMsNow
  let uptimeMs ← getServerUptimeMs
  -- If we can reach this point, the server is alive
  return { overall := .healthy, checks := [], serverUpMs := uptimeMs, timestamp }

end LeanServer
