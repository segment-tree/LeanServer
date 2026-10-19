import Proxy

namespace FrontendBackend.ExchangeGraph

open LeanServer.HTTP

/-- Ordered, element-by-element correspondence, including equal lengths. -/
inductive Aligned (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Aligned relation [] []
  | cons {a b as bs} : relation a b → Aligned relation as bs →
      Aligned relation (a :: as) (b :: bs)

theorem Aligned.length_eq {relation : α → β → Prop} {as : List α} {bs : List β}
    (aligned : Aligned relation as bs) : as.length = bs.length := by
  induction aligned with
  | nil => rfl
  | cons _ _ ih => simp [ih]

structure SendCall where
  offered : ByteArray
  reported : Nat

def bytes (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) ByteArray.empty

def written (calls : List SendCall) : ByteArray :=
  bytes (calls.map fun c => c.offered.extract 0 c.reported)

/-- One logical request/response interaction, not an entire persistent socket. -/
structure ConnectionExchange where
  requestSends : List SendCall
  requestReads : List ByteArray
  responseSends : List SendCall
  responseReads : List ByteArray

structure Requests (connection : ConnectionExchange) (calls : List ForwardCall) : Prop where
  sent : written connection.requestSends =
    bytes (calls.map fun call => encodeUpstreamRequest call.upstream call.request)

/-- Sending the computed output is conditional on computation producing output.
Neither successful parsing nor network delivery is assumed here. -/
structure Replies (connection : ConnectionExchange)
    (respond : ByteArray → Option ByteArray) : Prop where
  sent : ∀ output, respond (bytes connection.requestReads) = some output →
    written connection.responseSends = output

structure StableTransport (connection : ConnectionExchange) : Prop where
  requestBounded : ∀ c ∈ connection.requestSends, c.reported ≤ c.offered.size
  received : bytes connection.requestReads = written connection.requestSends
  responseBounded : ∀ c ∈ connection.responseSends, c.reported ≤ c.offered.size
  delivered : bytes connection.responseReads = written connection.responseSends

structure Node (Program : Type) where
  program : Program
  address : Option Upstream
  rank : Nat

/-- Direction is caller to callee. Replies travel on this same edge.
The parent identifies the incoming request whose execution made this call. -/
structure UpstreamExchange (NodeId EdgeId : Type) where
  caller : NodeId
  callee : NodeId
  parent : Option EdgeId
  connection : ConnectionExchange
  sourceIP : String
  sourcePort : UInt16
  responseClose : Bool

/-- A finite, rooted interaction graph. Parallel calls and shared service nodes
are allowed. Structural proofs do not assert parsing, delivery, or handler results. -/
structure Exchange (Program : Type) where
  nodeCount : Nat
  edgeCount : Nat
  nodes : Fin nodeCount → Node Program
  upstream : Fin edgeCount → UpstreamExchange (Fin nodeCount) (Fin edgeCount)
  entry : Fin edgeCount
  children : Fin edgeCount → List (Fin edgeCount)
  entryRoot : (upstream entry).parent = none
  rootUnique : ∀ edge, (upstream edge).parent = none → edge = entry
  parentConnected : ∀ edge parent, (upstream edge).parent = some parent →
    (upstream edge).caller = (upstream parent).callee
  childrenParent : ∀ parent child,
    child ∈ children parent ↔ (upstream child).parent = some parent
  childrenUnique : ∀ parent, (children parent).Nodup
  increasing : ∀ edge,
    (nodes (upstream edge).caller).rank < (nodes (upstream edge).callee).rank

abbrev NodeId (e : Exchange Program) := Fin e.nodeCount
abbrev EdgeId (e : Exchange Program) := Fin e.edgeCount

/-- A nonempty directed path in the service graph. -/
inductive Path (e : Exchange Program) : NodeId e → NodeId e → Prop where
  | viaEdge (id : EdgeId e) : Path e (e.upstream id).caller (e.upstream id).callee
  | trans {a b c} : Path e a b → Path e b c → Path e a c

theorem path_increasing (e : Exchange Program) {a b : NodeId e}
    (path : Path e a b) : (e.nodes a).rank < (e.nodes b).rank := by
  induction path with
  | viaEdge id => exact e.increasing id
  | trans _ _ first second => exact Nat.lt_trans first second

theorem acyclic (e : Exchange Program) (node : NodeId e) : ¬ Path e node node := by
  intro path
  have := path_increasing e path
  omega

/-- A child call belongs to execution at its parent's receiving node. -/
theorem child_connected (e : Exchange Program) (parent child : EdgeId e)
    (member : child ∈ e.children parent) :
    (e.upstream child).caller = (e.upstream parent).callee :=
  e.parentConnected child parent ((e.childrenParent parent child).mp member)

theorem child_increasing (e : Exchange Program) (parent child : EdgeId e)
    (member : child ∈ e.children parent) :
    (e.nodes (e.upstream parent).callee).rank < (e.nodes (e.upstream child).callee).rank := by
  have connected := child_connected e parent child member
  have rank := e.increasing child
  rw [connected] at rank
  exact rank

end FrontendBackend.ExchangeGraph
