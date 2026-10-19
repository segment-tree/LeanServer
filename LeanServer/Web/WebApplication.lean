import LeanServer.Web.Framework

/-! Compatibility names for the unified HTTP API.
Construct applications purely; pass the resulting router to HTTPServer.serve.
Database managers belong to the application's effect environment, not Context. -/
namespace LeanServer

abbrev RequestContext := HTTP.Context
abbrev WebAppResponseBuilder := HTTP.Response
abbrev WebAppRouteHandler := HTTP.Handler
abbrev WebAppState := HTTP.Router
abbrev RouteBuilder := HTTP.RouteM

def initWebApp : WebAppState m := {}
def addWebAppRoute (app : WebAppState m) (method path : String)
    (handler : WebAppRouteHandler m) : WebAppState m := app.add method path handler
def addWebAppMiddleware (app : WebAppState m) (middleware : HTTP.Middleware m) : WebAppState m :=
  app.use middleware

def createWebAppResponse (statusCode : UInt16 := 200) (body : String := "")
    (contentType : String := "text/plain; charset=utf-8") : WebAppResponseBuilder :=
  (HTTP.Response.ok body contentType).withStatus statusCode
def webAppJsonResponse := HTTP.Response.json
def webAppHtmlResponse := HTTP.Response.html
def webAppErrorResponse := HTTP.Response.error

def webAppSessionMiddleware [Monad m] : HTTP.Middleware m := fun next ctx =>
  let ctx := match ctx.request.headers.get? "x-session-id" with
    | some sessionId => ctx.setLocal "session-id" sessionId
    | none => ctx
  next ctx

def handleWebAppRequest [Monad m] (app : WebAppState m) (request : HTTP.Request) : m HTTP.Response :=
  app.dispatch (HTTP.Context.ofRequest request)

def WebApp.get (path : String) (handler : WebAppRouteHandler m) : RouteBuilder m := HTTP.route "GET" path handler
def WebApp.post (path : String) (handler : WebAppRouteHandler m) : RouteBuilder m := HTTP.route "POST" path handler
def WebApp.put (path : String) (handler : WebAppRouteHandler m) : RouteBuilder m := HTTP.route "PUT" path handler
def WebApp.delete (path : String) (handler : WebAppRouteHandler m) : RouteBuilder m := HTTP.route "DELETE" path handler
def WebApp.patch (path : String) (handler : WebAppRouteHandler m) : RouteBuilder m := HTTP.route "PATCH" path handler
def WebApp.use (middleware : HTTP.Middleware m) : RouteBuilder m := modify (·.use middleware)
def webApp (builder : RouteBuilder m) : WebAppState m := HTTP.buildRouter builder

def WebApp.jsonResponse [Monad m] (data : String) : m WebAppResponseBuilder := pure (HTTP.Response.json data)
def WebApp.htmlResponse [Monad m] (html : String) : m WebAppResponseBuilder := pure (HTTP.Response.html html)
def WebApp.errorResponse [Monad m] (code : UInt16) (message : String) : m WebAppResponseBuilder :=
  pure (HTTP.Response.error code message)

end LeanServer
