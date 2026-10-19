import FrontendCore
import BackendCore

namespace FrontendBackend

open LeanServer
open LeanServer.HTTP

/-! Pure policy contracts for the frontend/backend example. -/

def isResourceGet (ctx : Context) : Prop :=
  ctx.request.method = "GET" ∧ ctx.path = "/resource"

def backendReturnsResource
    (requestUpstream : Upstream → Request → Id UpstreamResult)
    (request : Request) : Prop :=
  requestUpstream backendAddr (backendRequest request) = .success (resource request.target)

def modelBackend : Upstream → Request → Id UpstreamResult :=
  fun _ request => .success (resource request.target)

/-! Connection metadata is kept outside `Context`; it is not read by the policy. -/
structure Endpoint where
  sourceIP : String
  sourcePort : UInt16

structure FrontendExchange where
  endpoint : Endpoint
  ctx : Context

def peerMatches (exchange : FrontendExchange) : Prop :=
  exchange.ctx.connection.peerAddress = some exchange.endpoint.sourceIP

theorem frontend_forwards_backend_request (ctx : Context) :
    singlePlan backendAddr backendRequest ctx =
      [{ upstream := backendAddr, request := backendRequest ctx.request }] := by
  rfl

theorem backend_core_serves_resource
    (ctx : Context)
    (hRequest : isResourceGet ctx) :
    backendCore (m := Id) ctx = pure (resource ctx.request.target) := by
  rcases hRequest with ⟨hMethod, hPath⟩
  simp [backendCore, hMethod, hPath]

theorem frontend_resource_iff_credentials
    (requestUpstream : Upstream → Request → Id UpstreamResult)
    (ctx : Context)
    (hRequest : isResourceGet ctx)
    (hBackend : backendReturnsResource requestUpstream ctx.request) :
    frontendWith requestUpstream ctx = pure (resource ctx.request.target)
      ↔ credentialsMatch ctx = true := by
  rcases hRequest with ⟨hMethod, hPath⟩
  by_cases hCredentials : credentialsMatch ctx
  · unfold backendReturnsResource at hBackend
    simp [frontendWith, hPath, hCredentials,
      singlePlan, proxyHandler, firstUpstreamResponse, hBackend] <;> rfl
  · have hNotResource :
        (pure unauthorizedResponse : Id Response) ≠
          pure (resource ctx.request.target) := by
      intro hEqual
      have hStatus := congrArg (fun response : Response => response.status) hEqual
      change unauthorizedResponse.status =
        (resource ctx.request.target).status at hStatus
      rw [unauthorized_status] at hStatus
      simp [resource, Response.json] at hStatus
    simpa [frontendWith, hPath, hCredentials] using hNotResource

theorem frontend_model_resource_iff_credentials (ctx : Context)
    (hRequest : isResourceGet ctx) :
    frontendWith modelBackend ctx = pure (resource ctx.request.target)
      ↔ credentialsMatch ctx = true := by
  apply frontend_resource_iff_credentials modelBackend ctx hRequest
  simp [backendReturnsResource, modelBackend, backendRequest]

theorem frontend_resource_iff_credentials_exchange
    (requestUpstream : Upstream → Request → Id UpstreamResult)
    (exchange : FrontendExchange)
    (_hExternal : exchange.endpoint.sourceIP ≠ "127.0.0.1")
    (_hPeer : peerMatches exchange)
    (hRequest : isResourceGet exchange.ctx)
    (hBackend : backendReturnsResource requestUpstream exchange.ctx.request) :
    frontendWith requestUpstream exchange.ctx =
        pure (resource exchange.ctx.request.target)
      ↔ credentialsMatch exchange.ctx = true := by
  exact frontend_resource_iff_credentials requestUpstream exchange.ctx hRequest hBackend

end FrontendBackend
