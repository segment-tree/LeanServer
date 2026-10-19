import Proof.NetworkExecution

namespace FrontendBackend2.Proof

open LeanServer.HTTP
open Network (AppM callUpstream)


def frontendBackendGraph (source : Upstream) : NetworkGraph where
  nodes := [frontendWith callUpstream, relayWith callUpstream,
    relayWith callUpstream, backendCore]
  addresses := fun node => match node.val with
    | 0 => ⟨"127.0.0.1", 8080⟩
    | 1 => leftAddr
    | 2 => rightAddr
    | _ => backendAddr
  resolve := fun address =>
    if address.host = "127.0.0.1" then
      if address.port = 8080 then some (0 : Fin 4) else
      if address.port = 8082 then some (1 : Fin 4) else
      if address.port = 8083 then some (2 : Fin 4) else
      if address.port = 8081 then some (3 : Fin 4) else none
    else none
  resolves := by
    intro node
    change Fin 4 at node
    have cases : node = (0 : Fin 4) ∨ node = 1 ∨ node = 2 ∨ node = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  resolvesOnly := by
    intro address node resolved
    change Fin 4 at node
    rcases address with ⟨host, port⟩
    repeat' split at resolved
    all_goals simp_all [leftAddr, rightAddr, backendAddr]
    all_goals subst node; rfl
  clientAddress := source
  entry := (0 : Fin 4)
  routes := fun caller callee => match caller, callee with
    | none, some node => node.val == 0
    | some caller, some callee =>
      (caller.val == 0 && (callee.val == 1 || callee.val == 2)) ||
      ((caller.val == 1 || caller.val == 2) && callee.val == 3)
    | _, none => false
  noIncomingClient := by intro node; cases node <;> rfl
  rank := fun node => match node with
    | none => 4
    | some node => if node.val = 0 then 3 else if node.val = 3 then 0 else 2
  decreasing := by
    intro caller callee connected
    cases callee with
    | none => cases caller <;> simp at connected
    | some target =>
      change Fin 4 at target
      cases caller with
      | none => dsimp; split <;> (try split) <;> omega
      | some caller =>
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connected
        dsimp
        split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem graph_routes (source : Upstream) :
    (frontendBackendGraph source).routes none (some (0 : Fin 4)) = true ∧
    (frontendBackendGraph source).routes (some (0 : Fin 4)) (some (1 : Fin 4)) = true ∧
    (frontendBackendGraph source).routes (some (0 : Fin 4)) (some (2 : Fin 4)) = true ∧
    (frontendBackendGraph source).routes (some (1 : Fin 4)) (some (3 : Fin 4)) = true ∧
    (frontendBackendGraph source).routes (some (2 : Fin 4)) (some (3 : Fin 4)) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem graph_no_direct_backend (source : Upstream) :
    (frontendBackendGraph source).routes (some (0 : Fin 4)) (some (3 : Fin 4)) = false := by
  rfl

/-- Branch indices select existing vertices; they do not construct new edges. -/
def relayNode (odd : Bool) : Fin 4 := if odd then 1 else 2

def relayDestination (odd : Bool) : ForwardDestination := if odd then .left else .right

theorem selected_address (request : Request) :
    selectedRelay request = (relayDestination (request.body.size % 2 == 1)).address := by
  unfold selectedRelay relayDestination
  split <;> rfl

theorem relay_resolve (source : Upstream) (odd : Bool) :
    (frontendBackendGraph source).resolve (relayDestination odd).address = some (relayNode odd) := by
  cases odd <;> rfl

theorem relay_handler (source : Upstream) (odd : Bool) :
    (frontendBackendGraph source).nodes[relayNode odd]'(by exact (relayNode odd).isLt) =
      relayWith callUpstream := by
  cases odd <;> rfl

theorem frontend_relay_route (source : Upstream) (odd : Bool) :
    (frontendBackendGraph source).routes (some (0 : Fin 4)) (some (relayNode odd)) = true := by
  cases odd <;> rfl

theorem relay_backend_route (source : Upstream) (odd : Bool) :
    (frontendBackendGraph source).routes (some (relayNode odd)) (some (3 : Fin 4)) = true := by
  cases odd <;> rfl

end FrontendBackend2.Proof
