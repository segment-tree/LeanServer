import Proof.ByteFramingProofs
import Init.Data.String.Lemmas
import Proof.StringJoinProofs

/-! The first CRLFCRLF boundary for nonempty, CR-free UTF-8 header rows.
The byte arguments also exclude false matches across concatenation boundaries. -/

namespace FrontendBackend.RequestFraming
open LeanServer.HTTP
private theorem char_no_cr_byte (c : Char) (no : c ≠ '\r') :
    ∀ b ∈ String.utf8EncodeChar c, b ≠ (13 : UInt8) := by
  intro b hb
  unfold String.utf8EncodeChar at hb
  dsimp only at hb
  split at hb
  · rename_i small
    simp only [List.mem_singleton] at hb
    subst b
    intro eq
    have eqNat := congrArg UInt8.toNat eq
    change c.val.toNat % 256 = 13 at eqNat
    have val : c.toNat = 13 := by change c.val.toNat = 13; omega
    apply no
    apply Char.ext
    apply UInt32.toNat_inj.mp
    exact val
  · split at hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> intro eq <;>
        have h := congrArg UInt8.toNat eq <;> simp at h <;> omega
    · split at hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> intro eq <;>
          have h := congrArg UInt8.toNat eq <;> simp at h <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> intro eq <;>
          have h := congrArg UInt8.toNat eq <;> simp at h <;> omega

def NoCR (b : ByteArray) : Prop := ∀ j (h : j < b.size), b[j]'h ≠ 13

theorem utf8_no_cr (s : String) (no : ∀ c ∈ s.toList, c ≠ '\r') : NoCR s.toUTF8 := by
  intro j hj
  have all : ∀ b ∈ s.toList.utf8Encode.data.toList, b ≠ (13 : UInt8) := by
    simp only [List.utf8Encode, List.data_toByteArray, List.toList_toArray, List.mem_flatMap]
    intro b hb
    obtain ⟨c,hc,hb⟩ := hb
    exact char_no_cr_byte c (no c hc) b hb
  simp only [String.utf8Encode_toList] at all
  exact all _ (List.mem_iff_getElem.mpr ⟨j, by simpa using hj, rfl⟩)

private theorem match_cr (wire : ByteArray) (j : Nat)
    (eq : wire.extract j (j+4) = "\r\n\r\n".toUTF8) :
    ∃ h0 : j < wire.size, ∃ h2 : j+2 < wire.size,
      wire[j]'h0 = 13 ∧ wire[j+2]'h2 = 13 := by
  have h0 : 0 < (wire.extract j (j+4)).size := by rw [eq]; decide
  have h2 : 2 < (wire.extract j (j+4)).size := by rw [eq]; decide
  have v0 : (wire.extract j (j+4))[0]'h0 = 13 := by simp only [eq]; rfl
  have v2 : (wire.extract j (j+4))[2]'h2 = 13 := by simp only [eq]; rfl
  rw [ByteArray.getElem_extract] at v0 v2
  exact ⟨by simpa using ByteArray.getElem_extract_aux h0,
    ByteArray.getElem_extract_aux h2, by simpa using v0, v2⟩

def SafePrefix (b : ByteArray) : Prop :=
  ∀ j (h : j < b.size), b[j]'h ≠ 13 ∨ ∃ h2 : j+2 < b.size, b[j+2]'h2 ≠ 13

theorem safe_append (a b : ByteArray) (ha : SafePrefix a) (hb : SafePrefix b) : SafePrefix (a ++ b) := by
  intro j hj
  by_cases before : j < a.size
  · rcases ha j before with no | ⟨third,no⟩
    · exact Or.inl (by simpa only [ByteArray.getElem_append_left before] using no)
    · exact Or.inr ⟨by simp only [ByteArray.size_append]; omega,
        by simpa only [ByteArray.getElem_append_left third] using no⟩
  · have index : j-a.size < b.size := by simp only [ByteArray.size_append] at hj; omega
    rcases hb (j-a.size) index with no | ⟨third,no⟩
    · left
      rw [ByteArray.getElem_append_right (by omega)]
      exact no
    · refine Or.inr ⟨by simp only [ByteArray.size_append]; omega, ?_⟩
      rw [ByteArray.getElem_append_right (by omega)]
      have eq : j+2-a.size = j-a.size+2 := by omega
      simpa only [eq] using no

theorem safe_line (row : ByteArray) (nonempty : 0 < row.size) (no : NoCR row) :
    SafePrefix ("\r\n".toUTF8 ++ row) := by
  intro j hj
  by_cases before : j < 2
  · have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl | rfl
    · refine Or.inr ⟨by rw [ByteArray.size_append]; change 2 < 2 + row.size; omega, ?_⟩
      rw [ByteArray.getElem_append_right (by decide)]
      exact no 0 nonempty
    · left
      rw [ByteArray.getElem_append_left (by decide)]
      decide
  · left
    rw [ByteArray.getElem_append_right (by simpa using Nat.le_of_not_gt before)]
    exact no _ _

theorem find_prepend (pre tail : ByteArray) (k : Nat)
    (safe : SafePrefix pre) (found : findBytes tail "\r\n\r\n".toUTF8 = some k) :
    findBytes (pre ++ tail) "\r\n\r\n".toUTF8 = some (pre.size+k) := by
  obtain ⟨lo, bound, eq, prior⟩ := (findBytes_some_iff _ _ _ _).mp found
  apply (findBytes_some_iff _ _ _ _).mpr
  refine ⟨by omega, by simp only [ByteArray.size_append]; omega, ?_, ?_⟩
  · simpa only [Nat.add_assoc, ByteArray.extract_append_size_add] using eq
  · intro j _ lt yes
    by_cases before : j < pre.size
    · obtain ⟨h0,h2,v0,v2⟩ := match_cr _ j yes.2
      rcases safe j before with no | ⟨third,no⟩
      · exact no (by simpa only [ByteArray.getElem_append_left before] using v0)
      · exact no (by simpa only [ByteArray.getElem_append_left third] using v2)
    · have shifted : j = pre.size + (j-pre.size) := by omega
      apply prior (j-pre.size) (by omega) (by omega)
      refine ⟨by simp only [ByteArray.size_append] at yes; omega, ?_⟩
      have eq := yes.2
      rw [shifted] at eq
      simpa only [Nat.add_assoc, ByteArray.extract_append_size_add] using eq
def rowsSuffix : List String → String
  | [] => ""
  | row :: rows => "\r\n" ++ row ++ rowsSuffix rows

private theorem safe_rows (rows : List String)
    (no : ∀ row ∈ rows, ∀ c ∈ row.toList, c ≠ '\r')
    (nonempty : ∀ row ∈ rows, row ≠ "") :
    SafePrefix (rowsSuffix rows).toUTF8 := by
  induction rows with
  | nil => intro j hj; contradiction
  | cons row rows ih =>
    rw [rowsSuffix, String.toUTF8_eq_toByteArray, String.toByteArray_append]
    apply safe_append
    · change SafePrefix ("\r\n".toUTF8 ++ row.toUTF8)
      apply safe_line
      · have n := nonempty row (by simp)
        have nz : row.utf8ByteSize ≠ 0 := by
          intro zero
          exact n (String.isEmpty_iff.mp (String.isEmpty_iff_utf8ByteSize_eq_zero.mpr zero))
        simpa using Nat.pos_of_ne_zero nz
      · exact utf8_no_cr row (no row (by simp))
    · exact ih (by intro row hr; exact no row (by simp [hr]))
        (by intro row hr; exact nonempty row (by simp [hr]))

private theorem intercalate_rows (first : String) (rows : List String) :
    String.intercalate "\r\n" (first :: rows) = first ++ rowsSuffix rows := by
  induction rows generalizing first with
  | nil => simp [HTTPStrings.intercalate_one, rowsSuffix]
  | cons row rows ih =>
    rw [HTTPStrings.intercalate_cons, ih, rowsSuffix]
    simp only [String.append_assoc]

theorem head_boundary (first : String) (rows : List String)
    (firstNo : ∀ c ∈ first.toList, c ≠ '\r')
    (no : ∀ row ∈ rows, ∀ c ∈ row.toList, c ≠ '\r')
    (nonempty : ∀ row ∈ rows, row ≠ "") :
    let head := String.intercalate "\r\n" (first :: rows)
    findBytes (head ++ "\r\n\r\n").toUTF8 "\r\n\r\n".toUTF8 = some head.toUTF8.size := by
  have safe : SafePrefix (String.intercalate "\r\n" (first :: rows)).toUTF8 := by
    rw [intercalate_rows, String.toUTF8_eq_toByteArray, String.toByteArray_append]
    exact safe_append _ _ (fun j hj => Or.inl (utf8_no_cr first firstNo j hj)) (safe_rows rows no nonempty)
  have found : findBytes "\r\n\r\n".toUTF8 "\r\n\r\n".toUTF8 = some 0 := by native_decide
  simpa only [String.toUTF8_eq_toByteArray, String.toByteArray_append, Nat.add_zero] using find_prepend _ _ 0 safe found
end FrontendBackend.RequestFraming
