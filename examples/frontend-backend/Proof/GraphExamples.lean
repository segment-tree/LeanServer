import Proof.ApplicationExchange

namespace FrontendBackend.ExchangeGraph

private theorem five_edges (edge : Fin 5) :
    edge = 0 ∨ edge = 1 ∨ edge = 2 ∨ edge = 3 ∨ edge = 4 := by omega

/-- A branching DAG with a shared receiving service:
0 → 1 → 2 → 4 and 1 → 3 → 4. The two requests to node 4 have distinct parents.
Program labels and byte records are arbitrary; no application policy is asserted. -/
def diamond (programs : Fin 5 → Program) (traces : Fin 5 → ConnectionExchange) :
    Exchange Program where
  nodeCount := 5
  edgeCount := 5
  nodes := fun node => ⟨programs node, none, node.val⟩
  upstream := fun edge =>
    let endpoints : Fin 5 × Fin 5 :=
      if edge = 0 then (0, 1) else if edge = 1 then (1, 2)
      else if edge = 2 then (1, 3) else if edge = 3 then (2, 4) else (3, 4)
    { caller := endpoints.1, callee := endpoints.2,
      parent := if edge = 0 then none else if edge = 3 then some 1
        else if edge = 4 then some 2 else some 0,
      connection := traces edge, sourceIP := "", sourcePort := 0, responseClose := true }
  entry := 0
  children := fun edge => if edge = 0 then [1, 2]
    else if edge = 1 then [3] else if edge = 2 then [4] else []
  entryRoot := by simp
  rootUnique := by
    intro edge root
    rcases five_edges edge with rfl | rfl | rfl | rfl | rfl <;> simp_all
  parentConnected := by
    intro edge parent h
    rcases five_edges edge with rfl | rfl | rfl | rfl | rfl <;>
      rcases five_edges parent with rfl | rfl | rfl | rfl | rfl <;> simp_all
  childrenParent := by
    intro parent child
    rcases five_edges parent with rfl | rfl | rfl | rfl | rfl <;>
      rcases five_edges child with rfl | rfl | rfl | rfl | rfl <;> simp
  childrenUnique := by
    intro parent
    rcases five_edges parent with rfl | rfl | rfl | rfl | rfl <;> simp
  increasing := by
    intro edge
    rcases five_edges edge with rfl | rfl | rfl | rfl | rfl <;> simp <;> decide

/-- Sharing a service does not merge the two request executions. -/
theorem diamond_shared_service (programs : Fin 5 → Program)
    (traces : Fin 5 → ConnectionExchange) :
    ((diamond programs traces).upstream (3 : Fin 5)).callee =
      ((diamond programs traces).upstream (4 : Fin 5)).callee ∧
    ((diamond programs traces).upstream (3 : Fin 5)).parent ≠
      ((diamond programs traces).upstream (4 : Fin 5)).parent := by
  simp [diamond]

end FrontendBackend.ExchangeGraph
