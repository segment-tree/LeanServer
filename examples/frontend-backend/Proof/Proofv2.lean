import Proof.ApplicationGraph

namespace FrontendBackend.Proofv2

open LeanServer.HTTP
open Network (AppM callUpstream)

/-- Parsing evidence is derived from the parser result, not a runtime premise. -/
theorem completeRequest_parsed (wire : ByteArray) (request : Request)
    (complete : completeRequest wire = some request) :
    ∃ rest, parseHTTP1 wire = .ok (some (request, rest)) := by
  unfold completeRequest at complete
  cases parsed : parseHTTP1 wire with
  | error error => simp [parsed] at complete
  | ok result =>
    cases result with
    | none => simp [parsed] at complete
    | some pair =>
      rcases pair with ⟨decoded, rest⟩
      simp only [parsed] at complete
      split at complete
      · have eq := Option.some.inj complete
        subst decoded
        exact ⟨rest, rfl⟩
      · contradiction

/-- The free-effect interpretation executes the existing frontend code. -/
theorem frontend_run (upstream : Upstream → Request → UpstreamResult) (ctx : Context) :
    AppM.run upstream (frontendWith callUpstream ctx) = frontendWith (m := Id) upstream ctx := by
  unfold frontendWith
  split
  · rfl
  · split
    · rfl
    · simp [proxyHandler, singlePlan, firstUpstreamResponse, callUpstream]
      cases result : upstream backendAddr (backendRequest ctx.request) <;>
        simp [bind, AppM.bind, AppM.run, result] <;> rfl

theorem backend_run (upstream : Upstream → Request → UpstreamResult) (ctx : Context) :
    AppM.run upstream (backendCore (m := AppM) ctx) = backendCore (m := Id) ctx := by
  unfold backendCore
  split
  · rfl
  · split <;> rfl

/-- Actual dispatch to the graph's backend, under the two environmental contracts.
Forwarded parsing and the backend response are proved from code and bytes. -/
theorem invoke_resource (graph : NetworkGraph)
    (contracts : Contracts graph) (frontend backend : graph.ServiceId)
    (application : ApplicationNetwork graph frontend backend)
    (wire : ByteArray) (request : Request)
    (complete : completeRequest wire = some request) (scope : ResourceRequest request) :
    ∃ backendClose, invoke graph contracts frontend backendAddr (backendRequest request) =
      .success (wireResponse (resource request.target) backendClose) := by
  obtain ⟨rest, parsed⟩ := completeRequest_parsed wire request complete
  obtain ⟨forwarded, forwardedParsed, method, target, _⟩ :=
    forwarded_request_roundtrip wire request rest parsed scope.forwardingConstraint scope.method
  have decoded : completeRequest (encodeUpstreamRequest backendAddr (backendRequest request)) =
      some forwarded := by simp [completeRequest, forwardedParsed, ByteArray.isEmpty]
  have resolve : graph.resolve backendAddr = some backend := by
    rw [← application.backendAddress]
    exact graph.resolves backend
  have backendMethod : forwarded.method = "GET" := method.trans scope.method
  have backendPath : (requestContext graph (some frontend) forwarded).path = "/resource" := by
    change (forwarded.target.splitOn "?").head! = "/resource"
    rw [target]
    exact scope.path
  have backendResponse : backendCore (m := Id) (requestContext graph (some frontend) forwarded) =
      resource request.target := by
    have methodCtx : (requestContext graph (some frontend) forwarded).request.method = "GET" := backendMethod
    have targetCtx : (requestContext graph (some frontend) forwarded).request.target = request.target := target
    simp [backendCore, backendPath, methodCtx, targetCtx]
    rfl
  have sent : serve graph contracts (some frontend) backend
      (encodeUpstreamRequest backendAddr (backendRequest request)) =
      some (encodeHTTP1 (resource request.target) "GET" (responseClose forwarded)) := by
    rw [serve_eq, decoded]
    simp only [bind, Option.bind, application.backendHandler, backend_run,
      backendResponse, backendMethod]
    rfl
  refine ⟨responseClose forwarded, ?_⟩
  unfold invoke
  rw [resolve]
  simp only [application.upstreamRoute, ↓reduceIte]
  rw [delivered_eq graph contracts _ _ application.upstreamRoute, sent]
  dsimp only
  rw [delivered_eq graph contracts _ _ application.upstreamRoute, resource_roundtrip]

/-- The client/server wire path is derived by composing socket and transport;
no independent runtime correspondence or supplied response is involved. -/
theorem observed_of_request (graph : NetworkGraph)
    (contracts : Contracts graph) (frontend backend : graph.ServiceId)
    (application : ApplicationNetwork graph frontend backend)
    (wire : ByteArray) (request : Request)
    (complete : completeRequest wire = some request) :
    observedAt graph contracts frontend wire =
      (decodeResponse (encodeHTTP1
        (frontendWith (m := Id) (invoke graph contracts frontend) (requestContext graph none request))
        request.method (responseClose request))).map view := by
  unfold observedAt clientExchange
  simp only [application.entryRoute, ↓reduceIte]
  rw [delivered_eq graph contracts _ _ application.entryRoute,
    serve_eq, complete]
  simp only [bind, Option.bind, application.frontendHandler, frontend_run, pure]
  rw [delivered_eq graph contracts _ _ application.entryRoute]
  cases decodeResponse (encodeHTTP1
    (frontendWith (m := Id) (invoke graph contracts frontend) (requestContext graph none request))
    request.method (responseClose request)) <;> rfl

private theorem resource_view_wire (target : String) (close : Bool) :
    view (wireResponse (resource target) close) = view (resource target) :=
  view_wire _ _ (resource_valid target)
    (by change (200 : UInt16) ≠ 204; decide) (by change (200 : UInt16) ≠ 304; decide)

/-- Main policy argument for a request obtained by parsing the input bytes. -/
private theorem resource_iff_parsed (graph : NetworkGraph)
    (contracts : Contracts graph) (frontend backend : graph.ServiceId)
    (application : ApplicationNetwork graph frontend backend)
    (wire : ByteArray) (request : Request)
    (complete : completeRequest wire = some request) (scope : ResourceRequest request) :
    observedAt graph contracts frontend wire = some (view (resource request.target)) ↔
      credentialsMatch (Context.ofRequest request) = true := by
  rw [observed_of_request graph contracts frontend backend application wire request complete,
    scope.method]
  have path : (requestContext graph none request).path = "/resource" := scope.path
  have credentials : credentialsMatch (requestContext graph none request) =
      credentialsMatch (Context.ofRequest request) := rfl
  cases auth : credentialsMatch (Context.ofRequest request) with
  | true =>
    obtain ⟨backendClose, result⟩ :=
      invoke_resource graph contracts frontend backend application wire request complete scope
    have handler : frontendWith (m := Id) (invoke graph contracts frontend) (requestContext graph none request) =
        wireResponse (resource request.target) backendClose := by
      have requestCtx : (requestContext graph none request).request = request := rfl
      simp [frontendWith, path, credentials, auth, proxyHandler, singlePlan,
        firstUpstreamResponse, requestCtx, result]
      rfl
    rw [handler, encodeHTTP1_wire _ _ _ (resource_valid _)
      (by change (200 : UInt16) ≠ 204; decide) (by change (200 : UInt16) ≠ 304; decide),
      resource_roundtrip]
    simp [resource_view_wire]
  | false =>
    have handler : frontendWith (m := Id) (invoke graph contracts frontend) (requestContext graph none request) =
        unauthorizedResponse := by
      simp [frontendWith, path, credentials, auth]
      rfl
    rw [handler, unauthorized_roundtrip]
    simp only [Option.map_some, Bool.false_eq_true, iff_false]
    intro equal
    have status := congrArg ResponseView.status (Option.some.inj equal)
    have rejectedStatus : (view (wireResponse unauthorizedResponse (responseClose request))).status = 401 := by
      simp only [view, wireResponse, unauthorized_valid, ↓reduceIte]
      rfl
    change (view (wireResponse unauthorizedResponse (responseClose request))).status = 200 at status
    rw [rejectedStatus] at status
    contradiction

/-- Fixed arbitrary network, arbitrary source endpoint, and arbitrary request
bytes within the resource scope. Only socket and transport are environmental
contracts. Handlers and reachable edges are properties of the supplied graph. -/
theorem resource_iff_on_network
    (graph : NetworkGraph)
    (contracts : Contracts graph)
    (frontend backend : graph.ServiceId)
    (application : ApplicationNetwork graph frontend backend)
    (wire : ByteArray) (hRequest : ResourceInput wire) :
    observedAt graph contracts frontend wire = expectedResource wire ↔
      credentialsMatch (context wire) = true := by
  cases complete : completeRequest wire with
  | none => simp [ResourceInput, complete] at hRequest
  | some request =>
    have scope : ResourceRequest request := by simpa [ResourceInput, complete] using hRequest
    simpa [expectedResource, context, complete] using
      resource_iff_parsed graph contracts frontend backend application wire request complete scope

/-- For the specified frontend/backend network, every complete GET /resource
request within the forwarding bounds returns the resource iff its credentials
match. Only the two environmental contracts and request scope are premises.
The source endpoint is arbitrary; the network does not depend on the request. -/
theorem remote_resource_iff_credentials
    (source : Upstream)
    (contracts : Contracts (frontendBackendGraph source))
    (wire : ByteArray) (hRequest : ResourceInput wire) :
    observed (frontendBackendGraph source) contracts wire = expectedResource wire ↔
      credentialsMatch (context wire) = true :=
  resource_iff_on_network (frontendBackendGraph source) contracts (0 : Fin 2) (1 : Fin 2)
    (frontendBackendGraph_application source) wire hRequest

end FrontendBackend.Proofv2
