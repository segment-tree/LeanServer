import Proof.NetworkGraph
import Proof.ResponseCodecProofs

namespace FrontendBackend2.Proof

open LeanServer.HTTP
open Network (AppM callUpstream)

abbrev NetworkGraph := Network.Graph

inductive Direction where
  | request
  | response

/-- The socket operation and its reliability proof. For both directions of any
connection, the application's submitted bytes enter the network unchanged. -/
structure SocketContracts (graph : NetworkGraph) where
  send : graph.NodeId → graph.NodeId → Direction → ByteArray → ByteArray
  sent : ∀ caller callee direction payload, send caller callee direction payload = payload

/-- The network operation and its reliability proof on every available route.
Replies use the reverse direction of the same established connection. -/
structure TransportContracts (graph : NetworkGraph) where
  receive : graph.NodeId → graph.NodeId → Direction → ByteArray → ByteArray
  delivered : ∀ caller callee, graph.routes caller callee = true →
    ∀ direction payload, receive caller callee direction payload = payload

/-- Operations are packaged with their proofs; no separate Environment is needed.
This structure is in Type because it contains functions as well as proofs. -/
structure Contracts (graph : NetworkGraph) where
  socket : SocketContracts graph
  transport : TransportContracts graph

def delivered (graph : NetworkGraph) (contracts : Contracts graph)
    (caller callee : graph.NodeId) (direction : Direction) (payload : ByteArray) : ByteArray :=
  contracts.transport.receive caller callee direction
    (contracts.socket.send caller callee direction payload)

theorem delivered_eq (graph : NetworkGraph) (contracts : Contracts graph)
    (caller callee : graph.NodeId)
    (route : graph.routes caller callee = true) (direction : Direction) (payload : ByteArray) :
    delivered graph contracts caller callee direction payload = payload := by
  simp [delivered, contracts.socket.sent, contracts.transport.delivered caller callee route]

/-- Exactly one complete request, computed from bytes. No independently supplied
request and no clientParsed contract exist. -/
def completeRequest (wire : ByteArray) : Option Request :=
  match parseHTTP1 wire with
  | .ok (some (request, rest)) => if rest.isEmpty then some request else none
  | _ => none

/-- Exact close-mode expression used by handlePlainHTTP for a parsed request. -/
def responseClose (request : Request) : Bool :=
  ((request.headers.get? "connection").getD "").toLower == "close"

/-- Total notation for the theorem's credential check. On invalid input the
fallback has empty credentials; ResourceInput excludes that branch. Execution
itself uses completeRequest and never dispatches the fallback request. -/
def context (wire : ByteArray) : Context :=
  Context.ofRequest ((completeRequest wire).getD default)

def requestContext (graph : NetworkGraph) (peer : graph.NodeId) (request : Request) : Context :=
  let source := match peer with
    | none => graph.clientAddress
    | some node => graph.addresses node
  Context.ofRequest request { peerAddress := some source.host }

/-- Generic service execution. Look up the actual handler in nodes; interpret
its upstream effects by address resolution and a route check, then recursively
execute that target handler. Termination follows from the input DAG, with no
fuel, fixed depth, or frontend/backend-specific dispatch. -/
def serve (graph : NetworkGraph) (contracts : Contracts graph)
    (peer : graph.NodeId) (node : graph.ServiceId) (wire : ByteArray) : Option ByteArray := do
  let request ← completeRequest wire
  let invoke := fun (address : Upstream) (outgoing : Request) =>
    match graph.resolve address with
    | none => UpstreamResult.failure "unknown upstream"
    | some target =>
      if route : graph.routes (some node) (some target) = true then
        let received := delivered graph contracts (some node) (some target) .request
          (encodeUpstreamRequest address outgoing)
        match serve graph contracts (some node) target received with
        | none => .failure "invalid upstream request"
        | some reply =>
          let receivedReply := delivered graph contracts (some node) (some target) .response reply
          match decodeResponse receivedReply with
          | none => .failure "invalid upstream response"
          | some response => .success response
      else .failure "upstream unreachable"
  let ctx := requestContext graph peer request
  let response := AppM.run invoke (graph.nodes[node] ctx)
  pure (encodeHTTP1 response request.method (responseClose request))
termination_by graph.rank (some node)
decreasing_by exact graph.decreasing _ _ route

/-- Name the upstream effect used by serve, for modular proofs. -/
def invoke (graph : NetworkGraph) (contracts : Contracts graph) (caller : graph.ServiceId)
    (address : Upstream) (outgoing : Request) : UpstreamResult :=
  match graph.resolve address with
  | none => .failure "unknown upstream"
  | some target =>
    if graph.routes (some caller) (some target) then
      let received := delivered graph contracts (some caller) (some target) .request
        (encodeUpstreamRequest address outgoing)
      match serve graph contracts (some caller) target received with
      | none => .failure "invalid upstream request"
      | some reply =>
        let receivedReply := delivered graph contracts (some caller) (some target) .response reply
        match decodeResponse receivedReply with
        | none => .failure "invalid upstream response"
        | some response => .success response
    else .failure "upstream unreachable"

theorem serve_eq (graph : NetworkGraph) (contracts : Contracts graph)
    (peer : graph.NodeId) (node : graph.ServiceId) (wire : ByteArray) :
    serve graph contracts peer node wire = (do
      let request ← completeRequest wire
      pure (encodeHTTP1
        (AppM.run (invoke graph contracts node) (graph.nodes[node] (requestContext graph peer request)))
        request.method (responseClose request))) := by
  rw [serve]
  rfl

/-- The external client has no handler. It initiates this request; the graph is
unchanged. Responses travel back over the original reachable connection. -/
def clientExchange (graph : NetworkGraph) (contracts : Contracts graph)
    (entry : graph.ServiceId) (wire : ByteArray) : Option ByteArray := do
  if graph.routes none (some entry) then
    let received := delivered graph contracts none (some entry) .request wire
    let reply ← serve graph contracts none entry received
    pure (delivered graph contracts none (some entry) .response reply)
  else none

def observedAt (graph : NetworkGraph) (contracts : Contracts graph)
    (entry : graph.ServiceId) (wire : ByteArray) : Option ResponseView := do
  let received ← clientExchange graph contracts entry wire
  let response ← decodeResponse received
  pure (view response)

/-- The graph specifies which service receives the initiating client request. -/
def observed (graph : NetworkGraph) (contracts : Contracts graph)
    (wire : ByteArray) : Option ResponseView := observedAt graph contracts graph.entry wire

structure ResourceRequest (request : Request) : Prop where
  method : request.method = "GET"
  path : (Context.ofRequest request).path = "/resource"
  forwardingConstraint : ForwardingConstraint request

/-- These are the same request scope restrictions, now on a computed parser
result. Invalid/incomplete bytes are outside the resource-request theorem. -/
def ResourceInput (wire : ByteArray) : Prop :=
  match completeRequest wire with
  | none => False
  | some request => ResourceRequest request

def expectedResource (wire : ByteArray) : Option ResponseView :=
  (completeRequest wire).map (fun request => view (resource request.target))

end FrontendBackend2.Proof
