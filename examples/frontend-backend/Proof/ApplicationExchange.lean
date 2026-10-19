import Proof.ExchangeGraph
import FrontendCore

namespace FrontendBackend.Proofv2

open LeanServer.HTTP
open ExchangeGraph (ConnectionExchange)

inductive ServiceProgram where
  | client
  | frontend
  | backend
  deriving DecidableEq

/-- The graph stores all interactions. Only the original parsed request remains
as a theorem input, tied to entry bytes by clientParsed. -/
structure Exchange extends ExchangeGraph.Exchange ServiceProgram where
  request : Request

abbrev Exchange.EdgeId (e : Exchange) := Fin e.edgeCount
abbrev Exchange.NodeId (e : Exchange) := Fin e.nodeCount

def Exchange.client (e : Exchange) : ConnectionExchange := (e.upstream e.entry).connection
def Exchange.sourceIP (e : Exchange) : String := (e.upstream e.entry).sourceIP
def Exchange.sourcePort (e : Exchange) : UInt16 := (e.upstream e.entry).sourcePort
def Exchange.clientClose (e : Exchange) : Bool := (e.upstream e.entry).responseClose

/-- A convenience view for this one-call frontend, not a stored optional edge. -/
def Exchange.backendEdge (e : Exchange) : Option e.EdgeId := (e.children e.entry).head?

/-- The current application topology; the underlying graph supports arbitrary
finite rooted DAG interactions. Program labels identify the actual cores below. -/
structure FrontendBackendTopology (e : Exchange) : Prop where
  entryCaller : (e.nodes (e.upstream e.entry).caller).program = .client
  entryCallee : (e.nodes (e.upstream e.entry).callee).program = .frontend
  backend : ∀ edge, edge ≠ e.entry →
    (e.upstream edge).parent = some e.entry ∧
    (e.nodes (e.upstream edge).callee).program = .backend ∧
    (e.nodes (e.upstream edge).callee).address = some backendAddr ∧
    (e.upstream edge).responseClose = true

/-- The same three participants can be used in accepted and rejected exchanges.
The backend remains a participant even when no call to it occurs. -/
def exampleNodes (node : Fin 3) : ExchangeGraph.Node ServiceProgram :=
  if node = 0 then ⟨.client, none, 0⟩
  else if node = 1 then ⟨.frontend, some ⟨"127.0.0.1", 8080⟩, 1⟩
  else ⟨.backend, some backendAddr, 2⟩

private theorem two_edges (edge : Fin 2) : edge = 0 ∨ edge = 1 := by omega

/-- Construct the current successful-call topology for arbitrary byte records.
No transport, codec or credential property is built into the constructor. -/
def Exchange.withBackend (request : Request) (sourceIP : String) (sourcePort : UInt16)
    (client upstream : ConnectionExchange) (close : Bool) : Exchange where
  request
  nodeCount := 3
  edgeCount := 2
  nodes := exampleNodes
  upstream := fun edge => if edge = 0 then
    { caller := 0, callee := 1, parent := none, connection := client,
      sourceIP, sourcePort, responseClose := close }
    else
    { caller := 1, callee := 2, parent := some 0, connection := upstream,
      sourceIP := "127.0.0.1", sourcePort := 40000, responseClose := true }
  entry := 0
  children := fun edge => if edge = 0 then [1] else []
  entryRoot := by simp
  rootUnique := by
    intro edge root
    rcases two_edges edge with rfl | rfl <;> simp_all
  parentConnected := by
    intro edge parent h
    rcases two_edges edge with rfl | rfl <;>
      rcases two_edges parent with rfl | rfl <;> simp_all
  childrenParent := by
    intro parent child
    rcases two_edges parent with rfl | rfl <;>
      rcases two_edges child with rfl | rfl <;> simp
  childrenUnique := by
    intro parent
    rcases two_edges parent with rfl | rfl <;> simp
  increasing := by
    intro edge
    rcases two_edges edge with rfl | rfl <;> simp [exampleNodes]

theorem withBackend_topology (request : Request) (ip : String) (port : UInt16)
    (client upstream : ConnectionExchange) (close : Bool) :
    FrontendBackendTopology (Exchange.withBackend request ip port client upstream close) := by
  constructor
  · rfl
  · rfl
  · intro edge ne
    rcases two_edges edge with rfl | rfl
    · exact False.elim (ne rfl)
    · simp [Exchange.withBackend, exampleNodes]

/-- The no-call case still has the client-to-frontend entry edge. -/
def Exchange.withoutBackend (request : Request) (sourceIP : String) (sourcePort : UInt16)
    (client : ConnectionExchange) (close : Bool) : Exchange where
  request
  nodeCount := 3
  edgeCount := 1
  nodes := exampleNodes
  upstream := fun _ =>
    { caller := 0, callee := 1, parent := none, connection := client,
      sourceIP, sourcePort, responseClose := close }
  entry := 0
  children := fun _ => []
  entryRoot := rfl
  rootUnique := by intro edge _; omega
  parentConnected := by simp
  childrenParent := by simp
  childrenUnique := by simp
  increasing := by intro edge; simp [exampleNodes]

theorem withoutBackend_topology (request : Request) (ip : String) (port : UInt16)
    (client : ConnectionExchange) (close : Bool) :
    FrontendBackendTopology (Exchange.withoutBackend request ip port client close) := by
  constructor
  · rfl
  · rfl
  · intro edge ne
    apply False.elim
    apply ne
    change (edge : Fin 1) = (0 : Fin 1)
    apply Fin.ext
    change edge.val = 0
    have bound : edge.val < 1 := edge.isLt
    omega

/-- Data for the current application's graph construction. This stores no
assumptions or proofs. A backend trace may be present or absent independently
of credentials; runtime call correspondence constrains that choice. -/
structure ApplicationInput where
  request : Request
  sourceIP : String
  sourcePort : UInt16
  client : ConnectionExchange
  backend : Option ConnectionExchange
  clientClose : Bool

/-- Construct the full graph, including the program at each node and all edges. -/
def ApplicationInput.exchange (input : ApplicationInput) : Exchange :=
  match input.backend with
  | none => Exchange.withoutBackend input.request input.sourceIP input.sourcePort
      input.client input.clientClose
  | some backend => Exchange.withBackend input.request input.sourceIP input.sourcePort
      input.client backend input.clientClose

/-- Topology is a proved property of construction, with no contract premise. -/
theorem ApplicationInput.topology (input : ApplicationInput) :
    FrontendBackendTopology input.exchange := by
  unfold ApplicationInput.exchange
  split
  · exact withoutBackend_topology _ _ _ _ _
  · exact withBackend_topology _ _ _ _ _ _

end FrontendBackend.Proofv2
