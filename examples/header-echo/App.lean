import LeanServerPure

open LeanServer.HTTP

namespace HeaderEchoExample

def application : Handler Id := fun ctx =>
  match ctx.request.headers.get? "A" with
  | some value => Response.text value
  | none => Response.text "Missing header A" 400

theorem present (ctx : Context) (value : String)
    (h : ctx.request.headers.get? "A" = some value) :
    application ctx = Response.text value := by
  simp [application, h]

theorem missing (ctx : Context)
    (h : ctx.request.headers.get? "A" = none) :
    (application ctx).status = 400 := by
  simp [application, h, Response.text]

end HeaderEchoExample
