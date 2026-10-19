import Proof.Proofv2

namespace FrontendBackend.Network

open LeanServer.HTTP
open FrontendBackend.Proofv2

private def addresses (node : Fin 4) : Upstream :=
  ⟨"127.0.0.1", if node = (0 : Fin 4) then 8080 else if node = (1 : Fin 4) then 8082 else if node = (2 : Fin 4) then 8083 else 8081⟩

private def resolve (address : Upstream) : Option (Fin 4) :=
  if address.host = "127.0.0.1" then
    if address.port = 8080 then some (0 : Fin 4) else if address.port = 8082 then some (1 : Fin 4)
    else if address.port = 8083 then some (2 : Fin 4) else if address.port = 8081 then some (3 : Fin 4) else none
  else none

private theorem four_nodes (node : Fin 4) : node = (0 : Fin 4) ∨ node = (1 : Fin 4) ∨ node = (2 : Fin 4) ∨ node = (3 : Fin 4) := by omega

/-- A fixed network with four services plus the special client. The two extra
handlers are arbitrary. The network permits branches and a shared backend:
client→frontend, frontend→left→backend, frontend→right→backend,
and frontend→backend. The frontend's policy uses its direct backend route;
unused routes remain part of the graph regardless of credentials. -/
def diamond (source : Upstream) (left right : Handler AppM) : Graph where
  nodes := [frontendWith callUpstream, left, right, backendCore]
  addresses := addresses
  resolve := resolve
  resolves := by
    intro node
    change Fin 4 at node
    rcases four_nodes node with rfl | rfl | rfl | rfl <;> rfl
  resolvesOnly := by
    intro address node resolved
    change Fin 4 at node
    rcases address with ⟨host, port⟩
    simp only [resolve] at resolved
    split at resolved
    · split at resolved
      · simp_all [addresses]
      · split at resolved
        · simp_all [addresses]
          omega
        · split at resolved
          · have eq := Option.some.inj resolved
            subst node
            simp_all [addresses]
          · split at resolved
            · have eq := Option.some.inj resolved
              subst node
              simp_all [addresses]
            · contradiction
    · contradiction
  clientAddress := source
  entry := (0 : Fin 4)
  routes := fun caller callee => match caller, callee with
    | none, some node => node.val == 0
    | some caller, some callee => caller.val < callee.val
    | _, none => false
  noIncomingClient := by intro node; cases node <;> rfl
  rank := fun node => match node with
    | none => 5
    | some node => 4 - node.val
  decreasing := by
    intro caller callee connected
    cases callee with
    | none => cases caller <;> simp at connected
    | some target =>
      change Fin 4 at target
      cases caller with
      | none => simp only [beq_iff_eq] at connected; dsimp; omega
      | some caller =>
        simp only [decide_eq_true_eq] at connected
        have := target.isLt
        dsimp
        omega

theorem diamond_application (source : Upstream) (left right : Handler AppM) :
    ApplicationNetwork (diamond source left right) (0 : Fin 4) (3 : Fin 4) := by
  constructor <;> rfl

/-- This instantiates the final theorem on a five-node network, with two
unconstrained additional handlers. No three-node restriction is used. -/
theorem diamond_resource_iff (source : Upstream) (left right : Handler AppM)
    (contracts : Contracts (diamond source left right))
    (wire : ByteArray) (request : ResourceInput wire) :
    observed (diamond source left right) contracts wire = expectedResource wire ↔
      credentialsMatch (context wire) = true :=
  resource_iff_on_network _ contracts (0 : Fin 4) (3 : Fin 4)
    (diamond_application source left right) wire request

theorem diamond_unused_routes (source : Upstream) (left right : Handler AppM) :
    (diamond source left right).routes (some (0 : Fin 4)) (some (1 : Fin 4)) = true ∧
    (diamond source left right).routes (some (0 : Fin 4)) (some (2 : Fin 4)) = true ∧
    (diamond source left right).routes (some (1 : Fin 4)) (some (3 : Fin 4)) = true ∧
    (diamond source left right).routes (some (2 : Fin 4)) (some (3 : Fin 4)) = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end FrontendBackend.Network
