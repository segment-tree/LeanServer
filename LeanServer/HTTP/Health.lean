import LeanServer.HTTP.Types
import Lean.Data.Json

namespace LeanServer

/-- Health status of a subsystem -/
inductive HealthStatus where
  | healthy
  | degraded (reason : String)
  | unhealthy (reason : String)
  deriving Inhabited, BEq, Repr

instance : ToString HealthStatus where
  toString
    | .healthy       => "HEALTHY"
    | .degraded r    => s!"DEGRADED: {r}"
    | .unhealthy r   => s!"UNHEALTHY: {r}"

/-- Overall health status -/
def HealthStatus.isUp : HealthStatus → Bool
  | .healthy     => true
  | .degraded _  => true
  | .unhealthy _ => false

/-- A single health check result -/
structure HealthCheckResult where
  name     : String
  status   : HealthStatus
  durationMs : Nat
  details  : List (String × String) := []
  deriving Inhabited, Repr

/-- Composite health check report -/
structure HealthReport where
  overall    : HealthStatus
  checks     : List HealthCheckResult
  serverUpMs : Nat
  timestamp  : Nat
  version    : String := "0.2.0"
  deriving Inhabited, Repr


/-- Pure policy used by the IO probe and by model-based tests. -/
def threadPoolHealth (threads maximum : Nat) : HealthStatus :=
  if maximum == 0 || threads ≥ maximum then .unhealthy "Thread pool exhausted"
  else if threads * 100 > maximum * 90 then .degraded "Thread utilization above 90%"
  else .healthy

def aggregateHealth (checks : List HealthCheckResult) : HealthStatus :=
  checks.foldl (fun acc c =>
    match acc, c.status with
    | .unhealthy _, _ => acc
    | _, .unhealthy reason => .unhealthy reason
    | .degraded _, _ => acc
    | _, .degraded reason => .degraded reason
    | _, _ => acc) .healthy

def HealthCheckResult.json (result : HealthCheckResult) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", toJson result.name),
    ("status", toJson (match result.status with
      | .healthy => "UP" | .degraded _ => "DEGRADED" | .unhealthy _ => "DOWN")),
    ("duration_ms", Lean.toJson result.durationMs),
    ("message", toJson (match result.status with
      | .healthy => "" | .degraded reason | .unhealthy reason => reason)),
    ("details", Lean.Json.mkObj (result.details.map fun (k,v) => (k, toJson v))) ]
where
  toJson := Lean.toJson (α := String)

def HealthCheckResult.toJSON (result : HealthCheckResult) : String := result.json.compress

def HealthReport.toJSON (report : HealthReport) : String :=
  (Lean.Json.mkObj [
    ("status", Lean.toJson (match report.overall with
      | .healthy => "UP" | .degraded _ => "DEGRADED" | .unhealthy _ => "DOWN")),
    ("version", Lean.toJson report.version),
    ("uptime_ms", Lean.toJson report.serverUpMs),
    ("timestamp", Lean.toJson report.timestamp),
    ("checks", Lean.Json.arr (report.checks.toArray.map HealthCheckResult.json)) ]).compress

def healthCheckResponse (report : HealthReport) : HTTP.Response :=
  (HTTP.Response.json report.toJSON (if report.overall.isUp then 200 else 503)).withHeader
    "cache-control" "no-cache, no-store"

/-- Healthy status is always up -/
theorem healthy_is_up : HealthStatus.healthy.isUp = true := rfl

/-- Unhealthy status is never up -/
theorem unhealthy_is_not_up (r : String) : (HealthStatus.unhealthy r).isUp = false := rfl

/-- Degraded status is still up -/
theorem degraded_is_up (r : String) : (HealthStatus.degraded r).isUp = true := rfl


theorem threadPoolHealth_exhausted (threads maximum : Nat) (h : maximum ≤ threads) :
    threadPoolHealth threads maximum = .unhealthy "Thread pool exhausted" := by
  simp [threadPoolHealth, h]

end LeanServer
