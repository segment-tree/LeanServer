import Lean
import LeanServer.HTTP.Codec
import Proof.DecimalProofs
import Init.Data.Nat.ToString
namespace FrontendBackend
-- Codec is a legacy module. Resolve its private helper for proof access only.
-- This expands to the existing constant; it introduces no definition or axiom.
local macro "httpDecimal" : term => pure (Lean.mkIdent
  (Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.LeanServer.HTTP.Codec 0) "LeanServer") "HTTP") "decimal"))
/-- The HTTP parser's stricter decimal routine accepts the encoder's length. -/
theorem http_decimal_roundtrip (n : Nat) : httpDecimal (toString n) = .ok n := by
  have digits : (toString n).toList.all (fun c => '0' ≤ c && c ≤ '9') = true := by
    apply List.all_eq_true.mpr
    intro c hc
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  have nonempty : (toString n).isEmpty = false := by
    have len := Nat.length_toDigits_pos (b := 10) (n := n)
    apply Bool.eq_false_iff.mpr
    intro eq
    have empty := String.toList_eq_nil_iff.mpr (String.isEmpty_iff.mp eq)
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at empty
    simp [empty] at len
  change (if (toString n).isEmpty || !(toString n).toList.all (fun c => '0' ≤ c && c ≤ '9') then _
    else match (toString n).toNat? with | some value => Except.ok (ε := LeanServer.HTTP.RequestError) value | none => _) = _
  rw [nonempty, digits]
  simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [decimal_roundtrip]
end FrontendBackend
