import LeanServer.HTTP.Types

namespace LeanServer.HTTP

inductive RouteSegment where
  | literal (value : String)
  | param (name : String)
  | wildcard
  deriving Repr, Inhabited

def parsePattern (path : String) : List RouteSegment :=
  ((path.splitOn "/").filter (· != "")).map fun segment =>
    if segment == "*" then .wildcard
    else if segment.startsWith ":" then .param (segment.drop 1).toString
    else .literal segment

/-- Wildcards match only at the end. Empty path segments follow the original DSL. -/
def matchSegments : List RouteSegment → List String → Option (List (String × String))
  | [], [] => some []
  | [.wildcard], _ => some []
  | .literal expected :: rest, actual :: tail =>
    if expected == actual then matchSegments rest tail else none
  | .param name :: rest, actual :: tail =>
    (matchSegments rest tail).map ((name, actual) :: ·)
  | _, _ => none

structure Route (m : Type → Type) where
  method : String
  pattern : List RouteSegment
  handler : Handler m
  middleware : List (Middleware m) := []

structure Router (m : Type → Type) where
  routes : List (Route m) := []
  middleware : List (Middleware m) := []
  notFound : Option (Handler m) := none

def Router.add (router : Router m) (method path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m :=
  { router with routes := router.routes ++ [⟨method, parsePattern path, handler, middleware⟩] }

def Router.new : Router m := {}

def Router.get (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m :=
  router.add "GET" path handler middleware

def Router.post (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m :=
  router.add "POST" path handler middleware

def Router.put (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := router.add "PUT" path handler middleware
def Router.delete (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := router.add "DELETE" path handler middleware
def Router.patch (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := router.add "PATCH" path handler middleware

def Router.withNotFound (router : Router m) (handler : Handler m) : Router m :=
  { router with notFound := some handler }

def Router.use (router : Router m) (middleware : Middleware m) : Router m :=
  { router with middleware := router.middleware ++ [middleware] }

/-- Mount a router; its middleware applies only to its routes. -/
def Router.group (router : Router m) (pathPrefix : String) (child : Router m) : Router m :=
  { router with routes := router.routes ++ child.routes.map fun route =>
      { route with pattern := parsePattern pathPrefix ++ route.pattern
                   middleware := child.middleware ++ route.middleware } }

/-- Selection is pure even when the selected handler performs effects. -/
def selectRoute (method path : String) : List (Route m) → Option (Route m × List (String × String))
  | [] => none
  | route :: rest =>
    if route.method == method || route.method == "*" then
      match matchSegments route.pattern ((path.splitOn "/").filter (· != "")) with
      | some params => some (route, params)
      | none => selectRoute method path rest
    else selectRoute method path rest

def Router.dispatch [Monad m] (router : Router m) : Handler m :=
  Middleware.all router.middleware fun ctx =>
    match selectRoute ctx.request.method ctx.path router.routes with
    | some (route, params) =>
      Middleware.all route.middleware route.handler { ctx with pathParams := params }
    | none => match router.notFound with
      | some handler => handler ctx
      | none => pure (Response.text "Not Found" 404)

abbrev RouteM (m : Type → Type) := StateM (Router m) Unit

def route (method path : String) (handler : Handler m) : RouteM m :=
  modify (·.add method path handler)

def buildRouter (builder : RouteM m) : Router m := (builder.run {}).2

theorem selectRoute_nil (method path : String) :
    selectRoute (m := m) method path [] = none := rfl

theorem dispatch_empty [Monad m] (ctx : Context) :
    Router.dispatch (m := m) {} ctx = pure (Response.text "Not Found" 404) := rfl

theorem dispatch_selected [Monad m] (router : Router m) (ctx : Context)
    (route : Route m) (params : List (String × String))
    (hMiddleware : router.middleware = [])
    (hMatch : selectRoute ctx.request.method ctx.path router.routes = some (route, params)) :
    router.dispatch ctx = Middleware.all route.middleware route.handler { ctx with pathParams := params } := by
  simp [Router.dispatch, hMiddleware, Middleware.all, hMatch]

end LeanServer.HTTP
