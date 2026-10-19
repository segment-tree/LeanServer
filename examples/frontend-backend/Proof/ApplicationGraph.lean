import Proof.NetworkExecution

namespace FrontendBackend.Proofv2

open LeanServer.HTTP
open Network (AppM callUpstream)

/-- The specific application's fixed network. The special client is none;
service 0 stores the real frontend handler and service 1 the real backend.
Both reachable edges exist for every request, regardless of credentials. -/
def frontendBackendGraph (source : Upstream) : NetworkGraph where
  nodes := [frontendWith callUpstream, backendCore]
  addresses := fun node => if node = (0 : Fin 2) then ⟨"127.0.0.1", 8080⟩ else backendAddr
  resolve := fun address =>
    if address.host = "127.0.0.1" then
      if address.port = 8080 then some (0 : Fin 2) else if address.port = 8081 then some (1 : Fin 2) else none
    else none
  resolves := by
    intro node
    change Fin 2 at node
    have cases : node = (0 : Fin 2) ∨ node = (1 : Fin 2) := by omega
    rcases cases with rfl | rfl <;> rfl
  resolvesOnly := by
    intro address node resolved
    change Fin 2 at node
    rcases address with ⟨host, port⟩
    split at resolved
    · split at resolved
      · simp_all
      · split at resolved
        · simp_all [backendAddr]
          omega
        · contradiction
    · contradiction
  clientAddress := source
  entry := (0 : Fin 2)
  routes := fun caller callee => match caller, callee with
    | none, some node => node.val == 0
    | some caller, some callee => caller.val == 0 && callee.val == 1
    | _, none => false
  noIncomingClient := by intro node; cases node <;> rfl
  rank := fun node => match node with
    | none => 2
    | some node => 1 - node.val
  decreasing := by
    intro caller callee connected
    cases callee with
    | none => cases caller <;> simp at connected
    | some target =>
      change Fin 2 at target
      cases caller with
      | none => simp only [beq_iff_eq] at connected; dsimp; omega
      | some caller =>
        simp only [Bool.and_eq_true, beq_iff_eq] at connected
        dsimp
        omega

/-- Application placement follows from the graph definition, not a caller premise. -/
theorem frontendBackendGraph_application (source : Upstream) :
    ApplicationNetwork (frontendBackendGraph source) (0 : Fin 2) (1 : Fin 2) := by
  constructor <;> rfl

theorem frontendBackendGraph_routes (source : Upstream) :
    (frontendBackendGraph source).routes none (some (0 : Fin 2)) = true ∧
    (frontendBackendGraph source).routes (some (0 : Fin 2)) (some (1 : Fin 2)) = true := by
  exact ⟨rfl, rfl⟩

end FrontendBackend.Proofv2
