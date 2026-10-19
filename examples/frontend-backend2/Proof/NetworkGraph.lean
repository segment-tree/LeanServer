import FrontendCore
import BackendCore

namespace FrontendBackend2.Network

open LeanServer.HTTP

/-- Application effects: return a value, or call an upstream and continue with
its result. Existing polymorphic Handler m implementations run in this monad. -/
inductive AppM (α : Type) where
  | pure : α → AppM α
  | call : Upstream → Request → (UpstreamResult → AppM α) → AppM α

def AppM.bind (program : AppM α) (next : α → AppM β) : AppM β :=
  match program with
  | .pure value => next value
  | .call address request resume => .call address request (fun result => (resume result).bind next)

instance : Monad AppM where
  pure := AppM.pure
  bind := AppM.bind

instance : LawfulMonad AppM := by
  refine LawfulMonad.mk' AppM ?_ ?_ ?_
  · intro α program
    induction program with
    | pure value => rfl
    | call address request resume ih =>
      change AppM.call address request (fun result => (resume result).bind AppM.pure) = _
      congr
      funext result
      exact ih result
  · intro α β value next
    rfl
  · intro α β γ program next last
    induction program with
    | pure value => rfl
    | call address request resume ih =>
      change AppM.call address request (fun result => ((resume result).bind next).bind last) = _
      congr
      funext result
      exact ih result

def callUpstream (address : Upstream) (request : Request) : AppM UpstreamResult :=
  .call address request .pure

/-- Interpret every upstream effect, preserving order and continuations. -/
def AppM.run (invoke : Upstream → Request → UpstreamResult) (program : AppM α) : α :=
  match program with
  | .pure value => value
  | .call address request resume => (resume (invoke address request)).run invoke

@[simp] theorem AppM.run_pure (invoke : Upstream → Request → UpstreamResult) (value : α) :
    AppM.run invoke (.pure value) = value := rfl

@[simp] theorem AppM.run_bind (invoke : Upstream → Request → UpstreamResult)
    (program : AppM α) (next : α → AppM β) :
    AppM.run invoke (program.bind next) = AppM.run invoke (next (program.run invoke)) := by
  induction program with
  | pure value => rfl
  | call address request resume ih => exact ih (invoke address request)

/-- Actual handler values, not service-name labels. The distinguished client
is represented by none; some i names a service in nodes. Edges express fixed
network reachability and contain no requests, responses, or authentication data. -/
structure Graph where
  nodes : List (Handler AppM)
  addresses : Fin nodes.length → Upstream
  resolve : Upstream → Option (Fin nodes.length)
  resolves : ∀ node, resolve (addresses node) = some node
  resolvesOnly : ∀ address node, resolve address = some node → addresses node = address
  clientAddress : Upstream
  /-- Initial service selected by the client; independent of later handler calls. -/
  entry : Fin nodes.length
  routes : Option (Fin nodes.length) → Option (Fin nodes.length) → Bool
  noIncomingClient : ∀ node, routes node none = false
  rank : Option (Fin nodes.length) → Nat
  decreasing : ∀ caller callee, routes caller callee = true → rank callee < rank caller

abbrev Graph.ServiceId (graph : Graph) := Fin graph.nodes.length
abbrev Graph.NodeId (graph : Graph) := Option graph.ServiceId

/-- Paths describe available call directions, independently of any execution.
Responses return over the same connection and do not create reverse call edges. -/
inductive Path (graph : Graph) : graph.NodeId → graph.NodeId → Prop where
  | route {caller callee} : graph.routes caller callee = true → Path graph caller callee
  | trans {a b c} : Path graph a b → Path graph b c → Path graph a c

theorem path_decreasing (graph : Graph) {a b : graph.NodeId}
    (path : Path graph a b) : graph.rank b < graph.rank a := by
  induction path with
  | route connected => exact graph.decreasing _ _ connected
  | trans _ _ first second => exact Nat.lt_trans second first

theorem acyclic (graph : Graph) (node : graph.NodeId) : ¬ Path graph node node := by
  intro path
  have := path_decreasing graph path
  omega

end FrontendBackend2.Network
