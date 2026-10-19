import LeanServer.HTTP.Codec
import Init.Data.Range.Lemmas
namespace FrontendBackend
open LeanServer.HTTP

/-! Specifications of the actual HTTP byte scanner. No codec assumptions. -/

private def scanStep (p : Nat → Bool) (i : Nat) (_ : MProd (Option (Option Nat)) PUnit.{1}) :
    Id (ForInStep (MProd (Option (Option Nat)) PUnit.{1})) :=
  if p i then pure (.done ⟨some (some i), ⟨⟩⟩) else pure (.yield ⟨none, ⟨⟩⟩)
private theorem scan_list (xs : List Nat) (p : Nat → Bool) :
    (forIn xs ⟨none, PUnit.unit⟩ (scanStep p) : Id _).1 =
      (xs.find? p).map some := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    cases h : p x <;> simp [scanStep, h, List.find?, ih] <;> rfl
theorem findBytes_eq_find (b n : ByteArray) (start : Nat) :
    findBytes b n start = (List.range' start (b.size + 1 - start)).find?
      (fun i => i + n.size ≤ b.size && b.extract i (i + n.size) == n) := by
  unfold findBytes
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  change (match (forIn (List.range' start (b.size + 1 - start)) ⟨none, PUnit.unit⟩ (scanStep (fun i => i + n.size ≤ b.size && b.extract i (i + n.size) == n)) : Id _).1 with
    | none => none
    | some a => a) = _
  rw [scan_list]
  cases List.find? _ _ <;> rfl


theorem byteArray_beq_iff (a b : ByteArray) : (a == b) = true ↔ a = b := by
  cases a with | mk a =>
    cases b with | mk b =>
      change (a == b) = true ↔ _
      simp

/-- The actual scanner returns exactly the first complete match at or after start. -/
theorem findBytes_some_iff (b n : ByteArray) (start k : Nat) :
    findBytes b n start = some k ↔
      start ≤ k ∧ k + n.size ≤ b.size ∧ b.extract k (k + n.size) = n ∧
        ∀ j, start ≤ j → j < k →
          ¬(j + n.size ≤ b.size ∧ b.extract j (j + n.size) = n) := by
  rw [findBytes_eq_find, List.find?_eq_some_iff_getElem]
  simp only [List.length_range', List.getElem_range', Nat.one_mul, Bool.not_eq_true', Bool.eq_false_iff,
    Bool.and_eq_true, decide_eq_true_eq, byteArray_beq_iff]
  constructor
  · rintro ⟨⟨bound, eq⟩, i, hi, pos, prior⟩
    refine ⟨by omega, bound, eq, ?_⟩
    intro j lo lt matchAt
    have := prior (j - start) (by omega)
    have add : start + (j - start) = j := by omega
    rw [add] at this
    apply this
    simpa only [Bool.and_eq_true, decide_eq_true_eq, byteArray_beq_iff] using matchAt
  · rintro ⟨lo, bound, eq, prior⟩
    refine ⟨⟨bound, eq⟩, k - start, by omega, by omega, ?_⟩
    intro j hj
    have no := prior (start + j) (by omega) (by omega)
    intro yes
    apply no
    exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp yes).1,
      (byteArray_beq_iff _ _).mp (Bool.and_eq_true_iff.mp yes).2⟩

theorem extract_prefix (a tail : ByteArray) (i j : Nat) (bound : j ≤ a.size) :
    (a ++ tail).extract i j = a.extract i j := by
  rw [ByteArray.extract_append]
  have zero : j - a.size = 0 := by omega
  rw [zero]
  have empty : tail.extract (i - a.size) 0 = ByteArray.empty :=
    ByteArray.extract_eq_empty_iff.mpr (by simp)
  rw [empty, ByteArray.append_empty]

/-- Appending any payload cannot change a match already found within the prefix. -/
theorem findBytes_append_of_found (head tail needle : ByteArray) (start k : Nat)
    (found : findBytes head needle start = some k) :
    findBytes (head ++ tail) needle start = some k := by
  obtain ⟨lo, bound, eq, prior⟩ := (findBytes_some_iff _ _ _ _).mp found
  apply (findBytes_some_iff _ _ _ _).mpr
  refine ⟨lo, by simpa using Nat.le_trans bound (Nat.le_add_right head.size tail.size), ?_, ?_⟩
  · rw [extract_prefix _ _ _ _ bound]
    exact eq
  · intro j lower upper matchAt
    have before : j + needle.size ≤ head.size := by omega
    apply prior j lower upper
    refine ⟨before, ?_⟩
    rw [extract_prefix _ _ _ _ before] at matchAt
    exact matchAt.2

end FrontendBackend
