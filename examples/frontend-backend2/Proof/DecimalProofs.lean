import Std
import Init.Data.Nat.ToString
import Init.Data.String.Lemmas
import Init.Data.Iterators.Lemmas.Consumers.Loop

/-! Decimal roundtrip through the actual String.toNat? implementation. -/

namespace FrontendBackend2
private theorem fold_chars (s : String) (f : α → Char → α) (a : α) :
    s.toSlice.foldl f a = s.toList.foldl f a := by
  unfold String.Slice.foldl
  rw [← Std.Iter.foldl_toList]
  simp

private def natCheck (state : Bool × Bool × Bool × Bool) (c : Char) : Bool × Bool × Bool × Bool :=
  let (first, underscore, _, valid) := state
  (false, c = '_', c.isDigit,
    valid && (c.isDigit || decide (c = '_')) &&
      !(first && decide (c = '_')) && !(underscore && decide (c = '_')))

private theorem digit_not_underscore (c : Char) (digit : c.isDigit = true) : c ≠ '_' := by
  intro eq
  subst c
  contradiction

private theorem check_digits (cs : List Char) (digits : ∀ c ∈ cs, c.isDigit = true)
    (nonempty : cs ≠ []) (first last : Bool) :
    cs.foldl natCheck (first, false, last, true) = (false, false, true, true) := by
  cases cs with
  | nil => contradiction
  | cons c cs =>
    have digit := digits c (by simp)
    have ne := digit_not_underscore c digit
    simp only [List.foldl_cons]
    have step : natCheck (first, false, last, true) c = (false, false, true, true) := by
      simp [natCheck, digit, ne]
    rw [step]
    cases cs with
    | nil => rfl
    | cons d ds => exact check_digits (d :: ds) (by intro x hx; exact digits x (by simp [hx])) (by simp) false true
termination_by cs.length

private theorem isNat_digits (s : String) (digits : ∀ c ∈ s.toList, c.isDigit = true)
    (nonempty : s.toList ≠ []) : s.toSlice.isNat = true := by
  have notEmpty : s.toSlice.isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro empty
    exact nonempty (String.toList_eq_nil_iff.mpr (String.isEmpty_toSlice_iff.mp empty))
  unfold String.Slice.isNat
  rw [notEmpty]
  simp only [Bool.false_eq_true, ↓reduceIte, fold_chars]
  change ((s.toList.foldl natCheck (true, false, false, true)).2.2.2 &&
    (s.toList.foldl natCheck (true, false, false, true)).2.2.1) = true
  rw [check_digits _ digits nonempty]
  rfl

private theorem digit_value (n : Nat) (h : n < 10) : n.digitChar.toNat - 48 = n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> first | decide | omega

private theorem digits_value (n : Nat) :
    (Nat.toDigits 10 n).foldl (fun a c => a * 10 + (c.toNat - 48)) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_if (by decide : 1 < 10)]
    split
    · rename_i bound
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      exact digit_value n bound
    · rename_i bound
      rw [List.foldl_append, ih (n / 10) (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, digit_value _ (Nat.mod_lt _ (by decide : 0 < 10))]
      omega

/-- Every natural number survives decimal rendering and parsing, without a size bound. -/
theorem decimal_roundtrip (n : Nat) : (toString n).toNat? = some n := by
  have digits : ∀ c ∈ (toString n).toList, c.isDigit = true := by
    intro c hc
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  have nonempty : (toString n).toList ≠ [] := by
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    have := Nat.length_toDigits_pos (b := 10) (n := n)
    intro eq
    simp [eq] at this
  unfold String.toNat? String.Slice.toNat?
  rw [isNat_digits _ digits nonempty]
  simp only [↓reduceIte, fold_chars]
  congr 1
  have foldEq : ((toString n).toList.foldl (fun a c => if c = '_' then a else a * 10 + (c.toNat - '0'.toNat)) 0) =
      (toString n).toList.foldl (fun a c => a * 10 + (c.toNat - 48)) 0 := by
    generalize eq : (toString n).toList = cs at *
    clear eq nonempty
    have aux (a : Nat) : cs.foldl (fun a c => if c = '_' then a else a * 10 + (c.toNat - '0'.toNat)) a =
        cs.foldl (fun a c => a * 10 + (c.toNat - 48)) a := by
      induction cs generalizing a with
      | nil => rfl
      | cons c cs ih =>
        simp only [List.foldl_cons, if_neg (digit_not_underscore c (digits c (by simp)))]
        exact ih (by intro d hd; exact digits d (by simp [hd])) (a * 10 + (c.toNat - 48))
    exact aux 0
  rw [foldEq, Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  exact digits_value n
end FrontendBackend2
