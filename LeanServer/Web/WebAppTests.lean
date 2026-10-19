import LeanServerPure
import LeanServer.Web.SampleWebApp

open LeanServer.HTTP

private def check (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {name}" else throw (IO.userError s!"FAIL {name}")

-- Both old entry points dispatch the canonical type definitionally.
example (router : LeanServer.WebApplication Id) (request : Request) :
    LeanServer.handleWebRequest router request = router.dispatch (Context.ofRequest request) := rfl
example (router : LeanServer.WebAppState Id) (request : Request) :
    LeanServer.handleWebAppRequest router request = router.dispatch (Context.ofRequest request) := rfl

-- The facade must support ordinary qualified calls and alias dot notation.
example (response : LeanServer.Web.Response) :
    response.withHeader "x-test" "yes" = LeanServer.HTTP.Response.withHeader response "x-test" "yes" := rfl
example (ctx : LeanServer.Web.Context) : ctx.paramOr "id" "" = LeanServer.HTTP.Context.paramOr ctx "id" "" := rfl
example (mw : LeanServer.Web.Middleware Id) :
    LeanServer.Web.Middleware.compose LeanServer.Web.Middleware.identity mw = mw := rfl
example (mw : LeanServer.Web.Middleware Id) :
    LeanServer.Web.Middleware.all [mw] = mw := rfl

def main : IO Unit := do
  let app := LeanServer.createSampleWebApp (m := Id)
  check "sample route count" (app.routes.length == 8)
  let health := LeanServer.handleWebRequest app { target := "/health" }
  check "sample health" (health.status == 200 && health.headers.get? "content-type" == some "application/json")
  let user := LeanServer.handleWebRequest app { target := "/users/42?ignored=1" }
  check "sample parameter route" (user.status == 200 &&
    String.fromUTF8! user.body == "{\"sql\":\"SELECT * FROM users WHERE id = 42\"}")
  check "sample invalid user id" ((LeanServer.handleWebRequest app { target := "/users/not-a-number" }).status == 400)
  check "sample not found" ((LeanServer.handleWebRequest app { target := "/missing" }).status == 404)
  let userJson := LeanServer.userToJson { name := "A\"B", email := "a\nb", age := 30 }
  check "user JSON escapes quotes and controls" (Lean.Json.parse userJson).isOk
  let echoed := LeanServer.handleWebRequest app { method := "POST", target := "/users", body := "a\"b\nc".toUTF8 }
  check "sample body JSON escaping" (Lean.Json.parse (String.fromUTF8! echoed.body)).isOk

  let router : LeanServer.Web.Router (StateM Nat) := LeanServer.Web.buildRouter do
    LeanServer.Web.routeGroup "/api" [mapResponse (·.withHeader "x-group" "yes")] do
      LeanServer.Web.routeGet "/:id" fun ctx => do
        modify (· + 1)
        return Response.text (ctx.paramOr "id" "")
  let (response, count) := (router.dispatch (Context.ofRequest { target := "/api/7" })).run 0
  check "Web DSL executes StateM handler" (response.body == "7".toUTF8 && count == 1)
  check "Web DSL scopes group middleware" (response.headers.get? "x-group" == some "yes")
  let missing := (router.dispatch (Context.ofRequest { target := "/other" })).run 0
  check "Web DSL leaves unmatched effects untouched" (missing.1.status == 404 && missing.2 == 0)
  let reader : LeanServer.WebAppState (ReaderT String Id) := LeanServer.webApp do
    LeanServer.WebApp.get "/" fun _ => do LeanServer.WebApp.htmlResponse (← read)
  check "WebApp DSL accepts ReaderT" ((reader.dispatch (Context.ofRequest {}) "environment").body == "environment".toUTF8)
  let ctx := Context.ofRequest { target := "/path?key=a=b&empty=&flag&key=second" }
  check "query retains equals and empty values" (ctx.query "key" == some "a=b" && ctx.query "empty" == some "" && ctx.query "flag" == some "")
  let fallback := (({} : Router Id).withNotFound (fun _ => Response.text "custom" 410)).dispatch ctx
  check "custom fallback" (fallback.status == 410)
  check "template interpolation" (LeanServer.Web.renderTemplate "Hello {{name}}" [("name", "Lean")] == "Hello Lean")
  check "template conditional" (LeanServer.Web.renderTemplate "{{#if yes}}ok{{/if}}" [("yes", "1")] == "ok")
  check "template iteration" (LeanServer.Web.renderTemplate "{{#each xs}}{{item}};{{/each}}" [("xs", "a;b")] == "a;b;")
  check "template partial" (LeanServer.Web.renderTemplate "{{> p}}" [("x", "value")] [("p", "{{x}}")] == "value")
  let sql := LeanServer.Web.QueryBuilder.from "users" |>.select ["id"] |>.where_ "age >= 18" |>.orderByAsc "id" |>.limit 10
  check "preserved SQL builder" (sql.toSQL == "SELECT id FROM users WHERE age >= 18 ORDER BY id ASC LIMIT 10")

  let next : Handler (StateM Nat) := fun _ => do modify (· + 1); return Response.text "handler"
  let authenticated := basicAuth (fun user password => pure (user == "user" && password == "pass")) next
  let denied := (authenticated (Context.ofRequest {})).run 0
  check "auth short circuit prevents handler effect" (denied.1.status == 401 && denied.2 == 0)
  let accepted := (authenticated (Context.ofRequest { headers := #[⟨"authorization", "Basic dXNlcjpwYXNz"⟩] })).run 0
  check "auth decodes user and password" (accepted.1.status == 200 && accepted.2 == 1)
  let cors := LeanServer.advancedCORSMiddleware (m := StateM Nat) {
    allowedOrigins := [.exact "https://example.com"], allowCredentials := true } next
  let preflight := (cors (Context.ofRequest { method := "OPTIONS", headers := #[
    ⟨"Origin", "https://example.com"⟩, ⟨"Access-Control-Request-Method", "POST"⟩] })).run 0
  check "CORS preflight bypasses handler" (preflight.1.status == 204 && preflight.2 == 0)
  check "credentialed CORS reflects validated origin"
    (preflight.1.headers.get? "access-control-allow-origin" == some "https://example.com")
  let badMethod := (cors (Context.ofRequest { method := "OPTIONS", headers := #[
    ⟨"origin", "https://example.com"⟩, ⟨"access-control-request-method", "post"⟩] })).run 0
  check "CORS methods remain case sensitive" (badMethod.1.status == 403 && badMethod.2 == 0)
  let badHeader := (cors (Context.ofRequest { method := "OPTIONS", headers := #[
    ⟨"origin", "https://example.com"⟩, ⟨"access-control-request-method", "POST"⟩,
    ⟨"access-control-request-headers", "x-forbidden"⟩] })).run 0
  check "CORS rejects disallowed preflight header" (badHeader.1.status == 403 && badHeader.2 == 0)
  let rejected := (cors (Context.ofRequest { headers := #[⟨"origin", "https://attacker.test"⟩] })).run 0
  check "CORS rejects origin before effects" (rejected.1.status == 403 && rejected.2 == 0)
  let varied := (Response.text "ok").vary "Accept" |>.vary "Origin" |>.vary "accept"
  check "Vary preserves independent middleware fields" (varied.headers.get? "vary" == some "Accept, Origin")
  check "gzip q=0 excluded" (LeanServer.selectEncoding "gzip;q=0, deflate;q=1" == LeanServer.CompressionEncoding.deflate)
  check "encoding exact name" (LeanServer.selectEncoding "notgzip" == LeanServer.CompressionEncoding.identity)
  check "encoding wildcard respects explicit exclusion" (LeanServer.selectEncoding "gzip;q=0, *;q=0.5" == LeanServer.CompressionEncoding.deflate)
  let limited := (rateLimit (pure (.limited 1501)) next (Context.ofRequest {})).run 0
  check "rate limit short circuit and rounded retry" (limited.1.status == 429 && limited.2 == 0 &&
    limited.1.headers.get? "retry-after" == some "2")
  let (decision, state) := rateLimitStep 60000 1 60000 { count := 1, windowStart := 0 }
  check "rate limit resets at window boundary" (decision == RateLimitDecision.allowed 0 && state.count == 1 && state.windowStart == 60000)
