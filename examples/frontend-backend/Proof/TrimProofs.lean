module
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import Init.Data.String.Lemmas
import Std

/-! Proofs about the actual slice-based trimAscii implementation.
The private recursion is imported for proof access only; no implementation changes. -/

public section
namespace FrontendBackend
private theorem slice_from_start (s : String.Slice) : s.sliceFrom s.startPos = s := by
  ext <;> simp [String.Pos.ext_iff]
private theorem slice_to_end (s : String.Slice) : s.sliceTo s.endPos = s := by
  ext <;> simp

private theorem get_mem (s : String.Slice) (p : s.Pos) (h : p ≠ s.endPos) :
    p.get h ∈ s.copy.toList := by
  have split := (p.splits_next_right h).eq_append
  rw [split, String.toList_append, String.toList_append]
  simp

private theorem prefix_none (s : String.Slice)
    (clean : ∀ c ∈ s.copy.toList, c.isWhitespace = false) :
    String.Slice.Pattern.ForwardPattern.dropPrefix? Char.isWhitespace s = none := by
  change (if h : s.startPos = s.endPos then none else
    if (s.startPos.get h).isWhitespace then some (s.startPos.next h) else none) = none
  split
  · rfl
  · rename_i h
    rw [clean _ (get_mem s s.startPos h)]
    rfl

private theorem suffix_none (s : String.Slice)
    (clean : ∀ c ∈ s.copy.toList, c.isWhitespace = false) :
    String.Slice.Pattern.BackwardPattern.dropSuffix? Char.isWhitespace s = none := by
  change (if h : s.endPos = s.startPos then none else
    if ((s.endPos.prev h).get (by simp)).isWhitespace then some (s.endPos.prev h) else none) = none
  split
  · rfl
  · rename_i h
    rw [clean _ (get_mem s (s.endPos.prev h) (by simp))]
    rfl

theorem trim_end_clean (s : String.Slice)
    (clean : ∀ c ∈ s.copy.toList, c.isWhitespace = false) : s.trimAsciiEnd = s := by
  unfold String.Slice.trimAsciiEnd String.Slice.dropEndWhile
  rw [String.Slice.dropEndWhile.go]
  rw [suffix_none (s.sliceTo s.endPos) (by simpa only [slice_to_end] using clean)]
  exact slice_to_end s

theorem trim_start_clean (s : String.Slice)
    (clean : ∀ c ∈ s.copy.toList, c.isWhitespace = false) : s.trimAsciiStart = s := by
  unfold String.Slice.trimAsciiStart String.Slice.dropWhile
  rw [String.Slice.dropWhile.go]
  rw [prefix_none (s.sliceFrom s.startPos) (by simpa only [slice_from_start] using clean)]
  exact slice_from_start s

private theorem drop_go_clean (s : String.Slice) (p : s.Pos)
    (clean : ∀ c ∈ (s.sliceFrom p).copy.toList, c.isWhitespace = false) :
    String.Slice.dropWhile.go s Char.isWhitespace p = s.sliceFrom p := by
  rw [String.Slice.dropWhile.go, prefix_none _ clean]

/-- Trimming removes the encoder's leading space without changing a whitespace-free value. -/
theorem trim_space_clean (s : String)
    (clean : ∀ c ∈ s.toList, c.isWhitespace = false) :
    (" " ++ s).trimAscii.toString = s := by
  let t := (" " ++ s).toSlice
  have split : t.startPos.Splits "" (String.singleton ' ' ++ s) := by
    simpa only [t, String.copy_toSlice, show String.singleton ' ' = " " from rfl] using t.splits_startPos
  have ne := split.ne_endPos_of_singleton
  have first : t.startPos.get ne = ' ' := split.next.get_eq_of_singleton
  have tail : (t.sliceFrom (t.startPos.next ne)).copy = s := split.next.copy_sliceFrom_eq
  let q := t.sliceFrom t.startPos
  have qs : q.startPos.Splits "" (String.singleton ' ' ++ s) := by
    simpa only [q, slice_from_start, t, String.copy_toSlice,
      show String.singleton ' ' = " " from rfl] using q.splits_startPos
  have qne := qs.ne_endPos_of_singleton
  have qfirst : q.startPos.get qne = ' ' := qs.next.get_eq_of_singleton
  have pref : String.Slice.Pattern.ForwardPattern.dropPrefix? Char.isWhitespace q = some (q.startPos.next qne) := by
    change (if h : q.startPos = q.endPos then none else
      if (q.startPos.get h).isWhitespace then some (q.startPos.next h) else none) = _
    rw [dif_neg qne, qfirst]
    rfl
  have mapped : String.Slice.Pos.ofSliceFrom (q.startPos.next qne) = t.startPos.next ne := by
    apply String.Slice.Pos.ext
    simp [String.Slice.Pos.offset_next, qfirst, first, q]
  unfold String.trimAscii String.Slice.trimAscii String.Slice.toString
  change t.trimAsciiStart.trimAsciiEnd.copy = s
  unfold String.Slice.trimAsciiStart String.Slice.dropWhile
  rw [String.Slice.dropWhile.go, pref]
  simp only [mapped, if_pos String.Slice.Pos.lt_next]
  rw [drop_go_clean t _ (by simpa only [tail] using clean)]
  rw [trim_end_clean _ (by simpa only [tail] using clean), tail]
private theorem sliceFrom_mem (s : String.Slice) (p : s.Pos) (c : Char)
    (mem : c ∈ (s.sliceFrom p).copy.toList) : c ∈ s.copy.toList := by
  rw [p.splits.eq_append, String.toList_append]
  exact List.mem_append_right _ mem
private theorem sliceTo_mem (s : String.Slice) (p : s.Pos) (c : Char)
    (mem : c ∈ (s.sliceTo p).copy.toList) : c ∈ s.copy.toList := by
  rw [p.splits.eq_append, String.toList_append]
  exact List.mem_append_left _ mem
private theorem drop_go_mem (s : String.Slice) (p : s.Pos) (c : Char) :
    c ∈ (String.Slice.dropWhile.go s Char.isWhitespace p).copy.toList → c ∈ s.copy.toList := by
  fun_induction String.Slice.dropWhile.go s Char.isWhitespace p with
  | case1 => assumption
  | case2 => exact sliceFrom_mem s _ c
  | case3 => exact sliceFrom_mem s _ c
private theorem drop_end_go_mem (s : String.Slice) (p : s.Pos) (c : Char) :
    c ∈ (String.Slice.dropEndWhile.go s Char.isWhitespace p).copy.toList → c ∈ s.copy.toList := by
  fun_induction String.Slice.dropEndWhile.go s Char.isWhitespace p with
  | case1 => assumption
  | case2 => exact sliceTo_mem s _ c
  | case3 => exact sliceTo_mem s _ c

theorem trim_mem (s : String) (c : Char) (mem : c ∈ s.trimAscii.toString.toList) : c ∈ s.toList := by
  unfold String.trimAscii String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd
    String.Slice.toString String.Slice.dropWhile String.Slice.dropEndWhile at mem
  have h := drop_end_go_mem _ _ c mem
  have h := drop_go_mem _ _ c h
  simpa using h
end FrontendBackend
