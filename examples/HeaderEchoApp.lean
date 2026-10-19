import LeanServer.HTTP.Router

open LeanServer.HTTP

/-- The same application can run in Id, IO, or an application-specific effect. -/
def headerEcho [Monad m] : Handler m := fun ctx =>
  pure <| match ctx.request.headers.get? "A" with
    | some value => Response.text value
    | none => Response.text "Missing header A" 400

theorem headerEcho_present (ctx : Context) (value : String)
    (h : ctx.request.headers.get? "A" = some value) :
    headerEcho (m := Id) ctx = Response.text value := by
  simp [headerEcho, h]
  rfl

theorem headerEcho_missing (ctx : Context)
    (h : ctx.request.headers.get? "A" = none) :
    (headerEcho (m := Id) ctx).status = 400 := by
  simp [headerEcho, h, Response.text]
  rfl
