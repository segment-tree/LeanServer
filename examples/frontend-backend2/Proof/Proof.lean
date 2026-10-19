import Proof.ApplicationGraph
import Proof.ResponseCodecProofs
import Proof.TwoHopProofs

namespace FrontendBackend2.Proof

open LeanServer.HTTP
open Network (AppM callUpstream)

theorem selectedRelay_odd (request : Request) (h : request.body.size % 2 = 1) :
    selectedRelay request = leftAddr := by simp [selectedRelay, h]

theorem selectedRelay_even (request : Request) (h : request.body.size % 2 = 0) :
    selectedRelay request = rightAddr := by simp [selectedRelay, h]

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

theorem frontend_run (upstream : Upstream → Request → UpstreamResult) (ctx : Context) :
    AppM.run upstream (frontendWith callUpstream ctx) =
      frontendWith (m := Id) upstream ctx := by
  unfold frontendWith
  split
  · rfl
  · split
    · rfl
    · simp [proxyHandler, singlePlan, firstUpstreamResponse, callUpstream]
      cases result : upstream (selectedRelay ctx.request) (backendRequest ctx.request) <;>
        simp [bind, AppM.bind, AppM.run, result] <;> rfl

theorem relay_run (upstream : Upstream → Request → UpstreamResult) (ctx : Context) :
    AppM.run upstream (relayWith callUpstream ctx) =
      relayWith (m := Id) upstream ctx := by
  simp [relayWith, proxyHandler, singlePlan, firstUpstreamResponse, callUpstream]
  cases result : upstream backendAddr ctx.request <;>
    simp [bind, AppM.bind, AppM.run, result] <;> rfl

theorem backend_run (upstream : Upstream → Request → UpstreamResult) (ctx : Context) :
    AppM.run upstream (backendCore (m := AppM) ctx) = backendCore (m := Id) ctx := by
  unfold backendCore
  split
  · rfl
  · split <;> rfl

private theorem resource_view_wire (target : String) (close : Bool) :
    view (wireResponse (resource target) close) = view (resource target) :=
  view_wire _ _ (resource_valid target)
    (by change (200 : UInt16) ≠ 204; decide) (by change (200 : UInt16) ≠ 304; decide)

/-- A proved local execution and decoder result compose across a reliable edge. -/
theorem invoke_of_serve (graph : NetworkGraph) (contracts : Contracts graph)
    (caller callee : graph.ServiceId) (address : Upstream) (outgoing : Request)
    (reply : ByteArray) (response : Response)
    (resolve : graph.resolve address = some callee)
    (route : graph.routes (some caller) (some callee) = true)
    (served : serve graph contracts (some caller) callee (encodeUpstreamRequest address outgoing) = some reply)
    (decoded : decodeResponse reply = some response) :
    invoke graph contracts caller address outgoing = .success response := by
  unfold invoke
  rw [resolve]
  simp only [route, ↓reduceIte]
  rw [delivered_eq graph contracts _ _ route, served]
  dsimp only
  rw [delivered_eq graph contracts _ _ route, decoded]

/-- Execute BOTH request hops, then return the backend's response through the
chosen relay. All parser and handler results below are derived from code. -/
theorem invoke_relay_resource (source : Upstream)
    (contracts : Contracts (frontendBackendGraph source))
    (odd : Bool) (wire : ByteArray) (request : Request)
    (complete : completeRequest wire = some request) (scope : ResourceRequest request) :
    ∃ relayClose,
      invoke (frontendBackendGraph source) contracts (0 : Fin 4)
        (relayDestination odd).address (backendRequest request) =
      .success (wireResponse (resource request.target) relayClose) := by
  let graph := frontendBackendGraph source
  let destination := relayDestination odd
  let middle := decodedRequest destination (backendRequest request)
  let finalRequest := decodedRequest .backend middle
  obtain ⟨rest, parsed⟩ := completeRequest_parsed wire request complete
  have first := first_hop_parsed destination wire request rest parsed scope.forwardingConstraint scope.method
  have second := second_hop_parsed destination wire request rest parsed scope.forwardingConstraint
  have middleParsed : completeRequest (encodeUpstreamRequest destination.address (backendRequest request)) =
      some middle := by simp [completeRequest, first, ByteArray.isEmpty, middle]
  have backendParsed : completeRequest (encodeUpstreamRequest backendAddr middle) = some finalRequest := by
    simp [completeRequest, second, ByteArray.isEmpty, middle, finalRequest]
  have backendPath : (requestContext graph (some (relayNode odd)) finalRequest).path = "/resource" := scope.path
  have backendResponse : backendCore (m := Id)
      (requestContext graph (some (relayNode odd)) finalRequest) = resource request.target := by
    have method : (requestContext graph (some (relayNode odd)) finalRequest).request.method = "GET" := rfl
    have target : (requestContext graph (some (relayNode odd)) finalRequest).request.target = request.target := rfl
    simp [backendCore, backendPath, method, target]
    rfl
  have backendHandler : graph.nodes[(show graph.ServiceId from (3 : Fin 4))] = backendCore (m := AppM) := rfl
  have backendServed : serve graph contracts (some (relayNode odd)) (3 : Fin 4)
      (encodeUpstreamRequest backendAddr middle) =
      some (encodeHTTP1 (resource request.target) "GET" (responseClose finalRequest)) := by
    rw [serve_eq, backendParsed]
    simp only [bind, Option.bind]
    rw [backendHandler, backend_run, backendResponse]
    rfl
  have backendResult : invoke graph contracts (relayNode odd) backendAddr middle =
      .success (wireResponse (resource request.target) (responseClose finalRequest)) :=
    invoke_of_serve graph contracts (relayNode odd) (3 : Fin 4) backendAddr middle _ _
      rfl (relay_backend_route source odd) backendServed (resource_roundtrip _ _)
  have relayResponse : relayWith (m := Id) (invoke graph contracts (relayNode odd))
      (requestContext graph (some (0 : Fin 4)) middle) =
      wireResponse (resource request.target) (responseClose finalRequest) := by
    have req : (requestContext graph (some (0 : Fin 4)) middle).request = middle := rfl
    simp [relayWith, proxyHandler, singlePlan, firstUpstreamResponse, req, backendResult]
    rfl
  have relayServed : serve graph contracts (some (0 : Fin 4)) (relayNode odd)
      (encodeUpstreamRequest destination.address (backendRequest request)) =
      some (encodeHTTP1 (resource request.target) "GET" (responseClose middle)) := by
    rw [serve_eq, middleParsed]
    have relayHandler : graph.nodes[(show graph.ServiceId from relayNode odd)] =
        relayWith callUpstream := by cases odd <;> rfl
    simp only [bind, Option.bind]
    rw [relayHandler, relay_run, relayResponse]
    change some (encodeHTTP1 (wireResponse (resource request.target) (responseClose finalRequest))
      "GET" (responseClose middle)) = _
    rw [encodeHTTP1_wire _ _ _ (resource_valid _)
      (by change (200 : UInt16) ≠ 204; decide) (by change (200 : UInt16) ≠ 304; decide)]
  exact ⟨responseClose middle,
    invoke_of_serve graph contracts (0 : Fin 4) (relayNode odd) destination.address
      (backendRequest request) _ _ (relay_resolve source odd) (frontend_relay_route source odd)
      relayServed (resource_roundtrip _ _)⟩

theorem observed_of_request (source : Upstream)
    (contracts : Contracts (frontendBackendGraph source))
    (wire : ByteArray) (request : Request) (complete : completeRequest wire = some request) :
    observed (frontendBackendGraph source) contracts wire =
      (decodeResponse (encodeHTTP1
        (frontendWith (m := Id) (invoke (frontendBackendGraph source) contracts (0 : Fin 4))
          (requestContext (frontendBackendGraph source) none request))
        request.method (responseClose request))).map view := by
  let graph := frontendBackendGraph source
  have route : graph.routes none (some (0 : Fin 4)) = true := rfl
  have handler : graph.nodes[(show graph.ServiceId from (0 : Fin 4))] = frontendWith callUpstream := rfl
  change observedAt graph contracts (0 : Fin 4) wire = _
  unfold observedAt clientExchange
  simp only [route, ↓reduceIte]
  rw [delivered_eq graph contracts _ _ route, serve_eq, complete]
  simp only [bind, Option.bind, pure]
  rw [handler, frontend_run]
  rw [delivered_eq graph contracts _ _ route]
  cases decodeResponse (encodeHTTP1
    (frontendWith (m := Id) (invoke graph contracts (0 : Fin 4)) (requestContext graph none request))
    request.method (responseClose request)) <;> rfl

private theorem resource_iff_parsed (source : Upstream)
    (contracts : Contracts (frontendBackendGraph source))
    (wire : ByteArray) (request : Request)
    (complete : completeRequest wire = some request) (scope : ResourceRequest request) :
    observed (frontendBackendGraph source) contracts wire = some (view (resource request.target)) ↔
      credentialsMatch (Context.ofRequest request) = true := by
  rw [observed_of_request source contracts wire request complete, scope.method]
  let graph := frontendBackendGraph source
  have path : (requestContext graph none request).path = "/resource" := scope.path
  have credentials : credentialsMatch (requestContext graph none request) =
      credentialsMatch (Context.ofRequest request) := rfl
  cases auth : credentialsMatch (Context.ofRequest request) with
  | true =>
    obtain ⟨relayClose, result⟩ := invoke_relay_resource source contracts
      (request.body.size % 2 == 1) wire request complete scope
    rw [← selected_address] at result
    change invoke graph contracts (0 : Fin 4) (selectedRelay request) (backendRequest request) =
      .success (wireResponse (resource request.target) relayClose) at result
    have handler : frontendWith (m := Id) (invoke graph contracts (0 : Fin 4))
        (requestContext graph none request) = wireResponse (resource request.target) relayClose := by
      have requestCtx : (requestContext graph none request).request = request := rfl
      simp [frontendWith, path, credentials, auth, proxyHandler, singlePlan,
        firstUpstreamResponse, requestCtx, result]
      rfl
    rw [handler, encodeHTTP1_wire _ _ _ (resource_valid _)
      (by change (200 : UInt16) ≠ 204; decide) (by change (200 : UInt16) ≠ 304; decide),
      resource_roundtrip]
    simp [resource_view_wire]
  | false =>
    have handler : frontendWith (m := Id) (invoke graph contracts (0 : Fin 4))
        (requestContext graph none request) = unauthorizedResponse := by
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

/-- Arbitrary source endpoint and original wire request, on the fixed diamond
network. Only socket/transport reliability and the original request scope are
premises; forwarding success and response preservation are proved above. -/
theorem remote_resource_iff_credentials
    (source : Upstream)
    (contracts : Contracts (frontendBackendGraph source))
    (wire : ByteArray) (hRequest : ResourceInput wire) :
    observed (frontendBackendGraph source) contracts wire = expectedResource wire ↔
      credentialsMatch (context wire) = true := by
  cases complete : completeRequest wire with
  | none => simp [ResourceInput, complete] at hRequest
  | some request =>
    have scope : ResourceRequest request := by simpa [ResourceInput, complete] using hRequest
    simpa [expectedResource, context, complete] using
      resource_iff_parsed source contracts wire request complete scope

end FrontendBackend2.Proof
