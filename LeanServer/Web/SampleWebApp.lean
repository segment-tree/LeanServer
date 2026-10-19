import LeanServer.Web.WebApplicationSimple
import Lean.Data.Json

/-! A pure routing/SQL-preview example. It does not connect to a database. -/
namespace LeanServer

structure User where
  id : Option Nat := none
  name : String
  email : String
  age : Nat
  created_at : Option String := none

def userToJson (user : User) : String :=
  (Lean.Json.mkObj [("id", Lean.toJson user.id), ("name", Lean.toJson user.name),
    ("email", Lean.toJson user.email), ("age", Lean.toJson user.age),
    ("created_at", Lean.toJson user.created_at)]).compress

private def preview (sql : String) : HTTP.Response :=
  HTTP.Response.json (Lean.Json.mkObj [("sql", Lean.toJson sql)]).compress

def createUserTableHandler [Monad m] : HTTP.Handler m := fun _ =>
  pure (preview "CREATE TABLE users (id SERIAL PRIMARY KEY, name TEXT, email TEXT, age INT)")
def getUsersHandler [Monad m] : HTTP.Handler m := fun _ =>
  pure (preview "SELECT id, name, email, age FROM users ORDER BY id")

private def withUserId [Monad m] (sql : Nat → String) : HTTP.Handler m := fun ctx =>
  match (ctx.paramOr "id" "").toNat? with
  | some id => pure (preview (sql id))
  | none => pure (HTTP.Response.text "Invalid user id" 400)

def getUserByIdHandler [Monad m] : HTTP.Handler m :=
  withUserId (fun id => s!"SELECT * FROM users WHERE id = {id}")
def updateUserHandler [Monad m] : HTTP.Handler m :=
  withUserId (fun id => s!"UPDATE users SET ... WHERE id = {id}")
def deleteUserHandler [Monad m] : HTTP.Handler m :=
  withUserId (fun id => s!"DELETE FROM users WHERE id = {id}")
def createUserHandler [Monad m] : HTTP.Handler m := fun ctx =>
  pure (HTTP.Response.json (Lean.Json.mkObj [
    ("sql", Lean.toJson "INSERT INTO users (name, email, age) VALUES (...)"),
    ("body", Lean.toJson (String.fromUTF8! ctx.request.body))]).compress)
def healthCheckHandler [Monad m] : HTTP.Handler m := fun _ =>
  pure (HTTP.Response.json "{\"status\":\"healthy\"}")
def rootHandler [Monad m] : HTTP.Handler m := fun _ =>
  pure (HTTP.Response.html "<h1>LeanServer SQL preview</h1><p>This demo returns SQL without executing it.</p><p>GET /users, GET /users/:id, POST /users, PUT /users/:id, DELETE /users/:id, POST /setup, GET /health</p>")

def createSampleWebApp [Monad m] : WebApplication m :=
  ({} : HTTP.Router m)
    |>.post "/setup" createUserTableHandler
    |>.get "/users" getUsersHandler
    |>.get "/users/:id" getUserByIdHandler
    |>.post "/users" createUserHandler
    |>.put "/users/:id" updateUserHandler
    |>.delete "/users/:id" deleteUserHandler
    |>.get "/health" healthCheckHandler
    |>.get "/" rootHandler

end LeanServer
