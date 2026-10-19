import LeanServer.HTTP.Router
import LeanServer.Core.Base64

namespace LeanServer.HTTP

/-- Response transformations work in every monad, including Id. -/
def mapResponse [Monad m] (f : Response → Response) : Middleware m :=
  fun next ctx => return f (← next ctx)

def cors [Monad m] (origin : String := "*") : Middleware m :=
  mapResponse (·.withHeader "access-control-allow-origin" origin)

def securityHeaders [Monad m] : Middleware m := fun next ctx => do
  let response := (← next ctx).withHeader "x-content-type-options" "nosniff"
    |>.withHeader "x-frame-options" "DENY"
  return if ctx.connection.secure then
    response.withHeader "strict-transport-security" "max-age=31536000; includeSubDomains"
    else response

/-- The application supplies the logging effect; no IO constraint on the middleware. -/
def logging [Monad m] (write : String → m Unit) : Middleware m := fun next ctx => do
  write s!"{ctx.request.method} {ctx.request.target}"
  next ctx

/-- Header propagation plus an explicitly supplied ID generation effect. -/
def requestId [Monad m] (generate : m String) : Middleware m := fun next ctx => do
  let id ← match ctx.request.headers.get? "x-request-id" with
    | some id => pure id
    | none => generate
  let response ← next (ctx.setLocal "request-id" id)
  return response.withHeader "x-request-id" id

/-- Trace creation can be interpreted by IO or a deterministic model. -/
def tracing [Monad m] (start : Option String → m String) : Middleware m := fun next ctx => do
  let trace ← start (ctx.request.headers.get? "traceparent")
  let response ← next (ctx.setLocal "traceparent" trace)
  return response.withHeader "traceparent" trace

def basicAuth [Monad m] (check : String → String → m Bool) : Middleware m := fun next ctx => do
  let denied := (Response.text "Unauthorized" 401).withHeader "www-authenticate" "Basic realm=\"LeanServer\""
  let some authorization := ctx.request.headers.get? "authorization" | return denied
  let [scheme, token] := authorization.splitOn " " | return denied
  if headerName scheme != "basic" then return denied
  let some decoded := LeanServer.Base64.decode token | return denied
  let some credentials := String.fromUTF8? decoded | return denied
  let parts := credentials.splitOn ":"
  if parts.length < 2 then return denied
  if ← check parts.head! (String.intercalate ":" parts.tail!) then
    next (ctx.setLocal "authenticated" "true")
  else return denied

structure RateLimitState where
  count : Nat := 0
  windowStart : Nat := 0
  deriving Repr, BEq

inductive RateLimitDecision where
  | allowed (remaining : Nat)
  | limited (retryAfterMs : Nat)
  deriving Repr, BEq

/-- Fixed-window policy. The caller atomically reads/updates state and supplies time. -/
def rateLimitStep (now maxRequests windowMs : Nat) (state : RateLimitState) :
    RateLimitDecision × RateLimitState :=
  let state := if now - state.windowStart ≥ windowMs then { count := 0, windowStart := now } else state
  if state.count ≥ maxRequests then
    (.limited (windowMs - (now - state.windowStart)), state)
  else
    (.allowed (maxRequests - state.count - 1), { state with count := state.count + 1 })

def rateLimit [Monad m] (acquire : m RateLimitDecision) : Middleware m := fun next ctx => do
  match ← acquire with
  | .limited retryAfterMs =>
    return (Response.text "Too Many Requests" 429).withHeader "retry-after" (toString ((retryAfterMs + 999) / 1000))
  | .allowed remaining =>
    let response ← next (ctx.setLocal "rate-limit-remaining" (toString remaining))
    return response.withHeader "x-ratelimit-remaining" (toString remaining)

end LeanServer.HTTP
