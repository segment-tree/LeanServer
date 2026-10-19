import LeanServer.HTTP.Middleware
import LeanServer.Web.Template
import LeanServer.Web.ORM

/-! Web convenience API over the canonical, effect-polymorphic HTTP application model.
No database drivers, socket runtime, or hidden application state. -/
namespace LeanServer.Web

abbrev Context := HTTP.Context
abbrev Response := HTTP.Response
abbrev Handler (m : Type → Type) := HTTP.Handler m
abbrev Middleware (m : Type → Type) := HTTP.Middleware m
abbrev Router (m : Type → Type) := HTTP.Router m
abbrev RouteEntry (m : Type → Type) := HTTP.Route m
abbrev RouteM (m : Type → Type) := HTTP.RouteM m
abbrev RouteSegment := HTTP.RouteSegment
abbrev PathParams := List (String × String)

namespace Response
export HTTP.Response (text ok html json redirect notFound error)
def withHeader (response : Response) (name value : String) : Response :=
  HTTP.Response.withHeader response name value
def withStatus (response : Response) (status : UInt16) : Response :=
  HTTP.Response.withStatus response status
def vary (response : Response) (field : String) : Response := HTTP.Response.vary response field
end Response
namespace Context
export HTTP.Context (ofRequest)
def param (ctx : Context) (name : String) : Option String := HTTP.Context.param ctx name
def paramOr (ctx : Context) (name fallback : String) : String := HTTP.Context.paramOr ctx name fallback
def query (ctx : Context) (name : String) : Option String := HTTP.Context.query ctx name
def «local» (ctx : Context) (name : String) : Option String := HTTP.Context.local ctx name
def setLocal (ctx : Context) (name value : String) : Context := HTTP.Context.setLocal ctx name value
end Context
namespace Middleware
export HTTP.Middleware (identity compose all before when)
end Middleware
namespace Router
def new : Router m := {}
def add (router : Router m) (method path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := HTTP.Router.add router method path handler middleware
def get (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := HTTP.Router.get router path handler middleware
def post (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := HTTP.Router.post router path handler middleware
def put (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := HTTP.Router.put router path handler middleware
def delete (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := HTTP.Router.delete router path handler middleware
def patch (router : Router m) (path : String) (handler : Handler m)
    (middleware : List (Middleware m) := []) : Router m := HTTP.Router.patch router path handler middleware
def use (router : Router m) (middleware : Middleware m) : Router m := HTTP.Router.use router middleware
def group (router : Router m) (pfx : String) (child : Router m) : Router m := HTTP.Router.group router pfx child
def dispatch [Monad m] (router : Router m) : Handler m := HTTP.Router.dispatch router
def withNotFound (router : Router m) (handler : Handler m) : Router m := HTTP.Router.withNotFound router handler
end Router

abbrev parseQueryString := HTTP.parseQueryString
def extractQueryParams (target : String) : String × List (String × String) :=
  let ctx := HTTP.Context.ofRequest { target }
  (ctx.path, parseQueryString (ctx.rawQuery.getD ""))

def loggingMiddleware [Monad m] (write : String → m Unit) : Middleware m := HTTP.logging write
def corsMiddleware [Monad m] (origin : String := "*") : Middleware m := HTTP.cors origin
def requestIdMiddleware [Monad m] (generate : m String) : Middleware m := HTTP.requestId generate
def basicAuthMiddleware [Monad m] (check : String → String → m Bool) : Middleware m :=
  HTTP.basicAuth check
def rateLimitMiddleware [Monad m] (acquire : m HTTP.RateLimitDecision) : Middleware m :=
  HTTP.rateLimit acquire

def routeGet (path : String) (handler : Handler m) : RouteM m := HTTP.route "GET" path handler
def routePost (path : String) (handler : Handler m) : RouteM m := HTTP.route "POST" path handler
def routePut (path : String) (handler : Handler m) : RouteM m := HTTP.route "PUT" path handler
def routeDelete (path : String) (handler : Handler m) : RouteM m := HTTP.route "DELETE" path handler
def routePatch (path : String) (handler : Handler m) : RouteM m := HTTP.route "PATCH" path handler
def routeUse (middleware : Middleware m) : RouteM m := modify (·.use middleware)
def routeGroup (pfx : String) (middleware : List (Middleware m) := [])
    (builder : RouteM m) : RouteM m :=
  modify fun router => router.group pfx
    (builder.run { middleware }).2
def buildRouter (builder : RouteM m) : Router m := HTTP.buildRouter builder

end LeanServer.Web
