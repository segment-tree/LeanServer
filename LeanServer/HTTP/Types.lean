import Std

/-! Transport-independent application data. No networking or native dependencies. -/
namespace LeanServer.HTTP

inductive Version where
  | http1_1 | http2 | http3
  deriving BEq, Repr, Inhabited

structure Header where
  name : String
  value : String
  deriving BEq, Repr, Inhabited

abbrev Headers := Array Header

/-- ASCII case folding, used only for HTTP field names. Methods remain case sensitive. -/
def headerName (name : String) : String :=
  name.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def Headers.getAll (headers : Headers) (name : String) : Array String :=
  (headers.filter fun h => headerName h.name == headerName name).map (·.value)

/-- Returns the first occurrence; use `getAll` when duplicate fields are meaningful. -/
def Headers.get? (headers : Headers) (name : String) : Option String :=
  (headers.find? fun h => headerName h.name == headerName name).map (·.value)

def Headers.set (headers : Headers) (name value : String) : Headers :=
  (headers.filter fun h => headerName h.name != headerName name).push ⟨name, value⟩

def isToken (s : String) : Bool := !s.isEmpty && s.toList.all fun c =>
  c.toNat < 128 && (c.isAlphanum || "!#$%&'*+-.^_`|~".contains c)

def Header.valid (h : Header) : Bool :=
  isToken h.name && h.value.toList.all (fun c => c == '\t' || (c.toNat ≥ 32 && c.toNat != 127))

structure Request where
  method : String := "GET"
  target : String := "/"
  scheme : Option String := none
  authority : Option String := none
  version : Version := .http1_1
  headers : Headers := #[]
  body : ByteArray := ByteArray.empty
  deriving Inhabited

structure ConnectionInfo where
  peerAddress : Option String := none
  localAddress : Option String := none
  secure : Bool := false
  deriving Repr, Inhabited

structure Context where
  request : Request
  connection : ConnectionInfo := {}
  path : String
  rawQuery : Option String := none
  pathParams : List (String × String) := []
  locals : List (String × String) := []
  deriving Inhabited

def Context.ofRequest (request : Request) (connection : ConnectionInfo := {}) : Context :=
  let parts := request.target.splitOn "?"
  { request, connection, path := parts.head!
    rawQuery := if parts.length > 1 then some (String.intercalate "?" parts.tail!) else none }

def Context.param (ctx : Context) (name : String) : Option String :=
  (ctx.pathParams.find? (fun p => p.1 == name)).map Prod.snd

def Context.paramOr (ctx : Context) (name fallback : String) : String :=
  (ctx.param name).getD fallback

/-- Raw query fields; percent decoding is left to the application. Split at the first '='. -/
def parseQueryString (query : String) : List (String × String) :=
  (query.splitOn "&").filterMap fun field =>
    if field.isEmpty then none else
      let parts := field.splitOn "="
      some (parts.head!, String.intercalate "=" parts.tail!)

def Context.query (ctx : Context) (name : String) : Option String :=
  ((parseQueryString (ctx.rawQuery.getD "")).find? (fun p => p.1 == name)).map Prod.snd

def Context.local (ctx : Context) (name : String) : Option String :=
  (ctx.locals.find? (fun p => p.1 == name)).map Prod.snd

def Context.setLocal (ctx : Context) (name value : String) : Context :=
  { ctx with locals := (name, value) :: ctx.locals }

structure Response where
  status : UInt16 := 200
  headers : Headers := #[]
  body : ByteArray := ByteArray.empty
  deriving Inhabited

def Response.text (body : String) (status : UInt16 := 200) : Response :=
  { status, headers := #[⟨"content-type", "text/plain; charset=utf-8"⟩], body := body.toUTF8 }

def Response.json (body : String) (status : UInt16 := 200) : Response :=
  { status, headers := #[⟨"content-type", "application/json"⟩], body := body.toUTF8 }

def Response.html (body : String) : Response :=
  { headers := #[⟨"content-type", "text/html; charset=utf-8"⟩], body := body.toUTF8 }

def Response.ok (body : String) (contentType : String := "text/plain; charset=utf-8") : Response :=
  { headers := #[⟨"content-type", contentType⟩], body := body.toUTF8 }

def Response.redirect (url : String) (status : UInt16 := 302) : Response :=
  { status, headers := #[⟨"location", url⟩] }

def Response.notFound (message : String := "Not Found") : Response := Response.text message 404
def Response.error (status : UInt16) (message : String) : Response := Response.text message status

def Response.withStatus (resp : Response) (status : UInt16) : Response :=
  { resp with status }

def Response.withHeader (resp : Response) (name value : String) : Response :=
  { resp with headers := resp.headers.set name value }

def Response.vary (resp : Response) (field : String) : Response :=
  let current := String.intercalate ", " (resp.headers.getAll "vary").toList
  let fields := (current.splitOn ",").map (fun s => s.trimAscii.toString)
  if fields.any (fun s => s == "*" || headerName s == headerName field) then resp
  else resp.withHeader "vary" (if current.isEmpty then field else current ++ ", " ++ field)

def Response.valid (resp : Response) : Bool :=
  resp.status ≥ 200 && resp.status ≤ 599 && resp.headers.all Header.valid

abbrev Handler (m : Type → Type) := Context → m Response
abbrev Middleware (m : Type → Type) := Handler m → Handler m

namespace Middleware

def identity : Middleware m := id

/-- The first middleware is outermost: request order a,b; response order b,a. -/
def compose (a b : Middleware m) : Middleware m := fun next => a (b next)

def all (middlewares : List (Middleware m)) (next : Handler m) : Handler m :=
  middlewares.foldr (fun mw handler => mw handler) next

def when (predicate : Context → Bool) (middleware : Middleware m) : Middleware m :=
  fun next ctx => if predicate ctx then middleware next ctx else next ctx

/-- Adapt a pre-handler check, including short circuit responses. -/
def before [Monad m] (check : Context → m (Except Response Context)) : Middleware m :=
  fun next ctx => do
    match ← check ctx with
    | .error response => pure response
    | .ok context => next context

theorem identity_apply (handler : Handler m) : identity handler = handler := rfl
theorem all_nil (handler : Handler m) : all [] handler = handler := rfl
theorem compose_assoc (a b c : Middleware m) :
    compose (compose a b) c = compose a (compose b c) := rfl

end Middleware
end LeanServer.HTTP
