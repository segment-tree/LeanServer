import LeanServer.HTTP.Middleware

/-!
# Advanced CORS Middleware (R25)

Configurable CORS (Cross-Origin Resource Sharing) middleware with support for:
- Per-origin allow lists (not just wildcard)
- Configurable allowed methods and headers
- Credentials support
- Preflight caching
- Origin validation with pattern matching

## Usage
```lean
let corsConfig : CORSConfig := {
  allowedOrigins := [.exact "https://example.com", .pattern "*.example.com"]
  allowCredentials := true
  maxAge := 3600
}
let middleware := advancedCORSMiddleware corsConfig
```

Extends the basic `corsMiddleware` in HTTPServer.lean with production features.
-/

namespace LeanServer

-- ==========================================
-- CORS Configuration Types
-- ==========================================

/-- Origin matching pattern -/
inductive OriginPattern where
  /-- Match any origin -/
  | wildcard
  /-- Match exact origin -/
  | exact (origin : String)
  /-- Match pattern (supports leading wildcard: *.example.com) -/
  | pattern (pat : String)
  deriving Inhabited, BEq, Repr

/-- CORS configuration -/
structure CORSConfig where
  /-- Allowed origins -/
  allowedOrigins   : List OriginPattern := [.wildcard]
  /-- Allowed HTTP methods -/
  allowedMethods   : List String := ["GET", "POST", "PUT", "DELETE", "PATCH", "OPTIONS", "HEAD"]
  /-- Allowed request headers -/
  allowedHeaders   : List String := ["Content-Type", "Authorization", "X-Requested-With", "Accept", "Origin"]
  /-- Headers exposed to the client -/
  exposedHeaders   : List String := ["X-Request-Id", "X-Correlation-Id"]
  /-- Whether credentials (cookies, auth) are allowed -/
  allowCredentials : Bool := false
  /-- Max age (seconds) for preflight cache -/
  maxAge           : Nat := 86400
  /-- Whether to add Vary: Origin header -/
  varyOrigin       : Bool := true
  deriving Inhabited, Repr

/-- CORS preflight result -/
inductive CORSResult where
  | allowed (origin : String)
  | denied
  | preflight (origin : String)
  deriving Inhabited, BEq, Repr

-- ==========================================
-- Origin Matching
-- ==========================================

/-- Check if a string ends with a suffix -/
private def endsWith (s suffix : String) : Bool :=
  if suffix.length > s.length then false
  else s.drop (s.length - suffix.length) == suffix

/-- Check if an origin matches a pattern -/
def matchOrigin (origin : String) (pat : OriginPattern) : Bool :=
  match pat with
  | .wildcard => true
  | .exact o  => origin == o
  | .pattern p =>
    if p.startsWith "*." then
      let suffix := (p.drop 1).toString  -- drop the * but keep the .
      endsWith origin suffix || origin == (p.drop 2).toString  -- also match bare domain
    else
      origin == p

/-- Check if an origin is allowed by the CORS config -/
def isOriginAllowed (origin : String) (config : CORSConfig) : Bool :=
  config.allowedOrigins.any (matchOrigin origin)

/-- Check if a method is allowed -/
def isMethodAllowed (method : String) (config : CORSConfig) : Bool :=
  config.allowedMethods.any (· == method)

/-- Check if a header is allowed (case-insensitive) -/
def isHeaderAllowed (header : String) (config : CORSConfig) : Bool :=
  config.allowedHeaders.any (fun h => h.toLower == header.toLower)

-- ==========================================
-- CORS Header Generation
-- ==========================================

/-- Generate CORS headers for an allowed request -/
def corsResponseHeaders (origin : String) (config : CORSConfig) : List (String × String) := Id.run do
  let mut headers : List (String × String) := []

  -- Access-Control-Allow-Origin
  let allowOrigin := if config.allowCredentials then
    origin  -- Can't use * with credentials
  else
    match config.allowedOrigins with
    | [.wildcard] => "*"
    | _ => origin
  headers := headers ++ [("access-control-allow-origin", allowOrigin)]

  -- Credentials
  if config.allowCredentials then
    headers := headers ++ [("access-control-allow-credentials", "true")]

  -- Exposed headers
  if !config.exposedHeaders.isEmpty then
    headers := headers ++ [("access-control-expose-headers", String.intercalate ", " config.exposedHeaders)]

  -- Vary header
  if config.varyOrigin then
    headers := headers ++ [("vary", "Origin")]

  return headers

/-- Generate CORS preflight response headers -/
def corsPreflightHeaders (origin : String) (config : CORSConfig) : List (String × String) := Id.run do
  let mut headers := corsResponseHeaders origin config

  -- Allowed methods
  headers := headers ++ [("access-control-allow-methods", String.intercalate ", " config.allowedMethods)]

  -- Allowed headers
  headers := headers ++ [("access-control-allow-headers", String.intercalate ", " config.allowedHeaders)]

  -- Max age
  headers := headers ++ [("access-control-max-age", toString config.maxAge)]

  return headers

-- ==========================================
-- CORS Middleware
-- ==========================================

/-- Process a CORS request with full origin validation.
    Call this at the server level where headers are available. -/
def processCORSRequest (method : String) (headers : List (String × String))
    (config : CORSConfig) : CORSResult :=
  let origin := match headers.find? (fun (k, _) => k.toLower == "origin") with
    | some (_, v) => v
    | none => ""
  if origin.isEmpty then .allowed ""  -- Same-origin request
  else if !isOriginAllowed origin config then .denied
  else if method == "OPTIONS" then .preflight origin
  else .allowed origin

/-- Apply validated CORS fields without replacing other Vary values. -/
def applyCORSResult (resp : HTTP.Response) (result : CORSResult) (config : CORSConfig) : HTTP.Response :=
  let add (response : HTTP.Response) (fields : List (String × String)) :=
    fields.foldl (fun acc (name, value) =>
      if name == "vary" then acc.vary value else acc.withHeader name value) response
  match result with
  | .allowed origin => if origin.isEmpty then resp else add resp (corsResponseHeaders origin config)
  | .denied => HTTP.Response.text "CORS origin not allowed" 403
  | .preflight origin => add { status := 204 } (corsPreflightHeaders origin config)

/-- Reads Origin and preflight fields before calling the application. -/
def advancedCORSMiddleware [Monad m] (config : CORSConfig := {}) : HTTP.Middleware m := fun next ctx => do
  let some origin := ctx.request.headers.get? "origin" | return ← next ctx
  if !isOriginAllowed origin config then return HTTP.Response.text "CORS origin not allowed" 403
  let requestedMethod := ctx.request.headers.get? "access-control-request-method"
  if ctx.request.method == "OPTIONS" && requestedMethod.isSome then
    let headers := ((ctx.request.headers.get? "access-control-request-headers").getD "").splitOn ","
    if !isMethodAllowed (requestedMethod.getD "") config ||
        headers.any (fun h => !h.trimAscii.toString.isEmpty && !isHeaderAllowed h.trimAscii.toString config) then
      return HTTP.Response.text "CORS preflight not allowed" 403
    return applyCORSResult {} (.preflight origin) config
  return applyCORSResult (← next ctx) (.allowed origin) config

-- ==========================================
-- Proofs
-- ==========================================

/-- Wildcard pattern matches any origin -/
theorem wildcard_matches_any (origin : String) :
    matchOrigin origin .wildcard = true := by
  simp [matchOrigin]

/-- Exact pattern matches itself -/
theorem exact_matches_self (origin : String) :
    matchOrigin origin (.exact origin) = true := by
  simp [matchOrigin]

end LeanServer
