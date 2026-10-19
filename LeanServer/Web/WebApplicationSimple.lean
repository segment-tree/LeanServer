import LeanServer.Web.WebApplication

/-! The former Simple variant now shares the same request, response, router and effects. -/
namespace LeanServer

abbrev ResponseBuilder := HTTP.Response
abbrev SimpleRouteHandler := HTTP.Handler
abbrev WebApplication := HTTP.Router

def initWebApplication : WebApplication m := {}
def addRoute (app : WebApplication m) (method path : String)
    (handler : SimpleRouteHandler m) : WebApplication m := app.add method path handler

abbrev createResponse := createWebAppResponse
abbrev jsonResponse := HTTP.Response.json
abbrev htmlResponse := HTTP.Response.html
abbrev errorResponse := HTTP.Response.error

def handleWebRequest [Monad m] (app : WebApplication m) (request : HTTP.Request) : m HTTP.Response :=
  app.dispatch (HTTP.Context.ofRequest request)

end LeanServer
