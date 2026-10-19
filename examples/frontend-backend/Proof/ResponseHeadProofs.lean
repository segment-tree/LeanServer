import Proof.AsciiHTTPProofs
import Proof.DecimalProofs
import Proof.TrimProofs
import Proof.ServiceProofs

/-! Pure parsing and byte-framing proofs for the JSON response head. -/

namespace FrontendBackend.Proofv2
open LeanServer.HTTP

/-- Header text before the terminating CRLFCRLF, matching encodeHTTP1. -/
def jsonResponseHead (length : Nat) (close : Bool) : String :=
  "HTTP/1.1 200 \r\ncontent-type: application/json\r\ncontent-length: " ++ toString length ++
    "\r\nConnection: " ++ (if close then "close" else "keep-alive")

theorem decimal_chars (n : Nat) :
    ∀ c ∈ (toString n).toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro c hc
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  simpa only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using digit

theorem json_head_lines (n : Nat) (close : Bool) :
    (jsonResponseHead n close).splitOn "\r\n" =
      ["HTTP/1.1 200 ", "content-type: application/json", "content-length: " ++ toString n,
        "Connection: " ++ (if close then "close" else "keep-alive")] := by
  let rows := ["HTTP/1.1 200 ", "content-type: application/json", "content-length: " ++ toString n,
        "Connection: " ++ (if close then "close" else "keep-alive")]
  have decAscii : AsciiHTTP.Ascii (toString n).toList := by
    intro c hc; have := decimal_chars n c hc; omega
  have decCR : ∀ c ∈ (toString n).toList, c ≠ '\r' := by
    intro c hc eq; have := decimal_chars n c hc; subst c; contradiction
  have asc : ∀ row ∈ rows.map String.toList, AsciiHTTP.Ascii row := by
    intro row mem
    simp only [rows, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · unfold AsciiHTTP.Ascii; decide
    · unfold AsciiHTTP.Ascii; decide
    · intro c hc
      simp only [String.toList_append, List.mem_append] at hc
      rcases hc with hc | hc
      · have bound : AsciiHTTP.Ascii "content-length: ".toList := by unfold AsciiHTTP.Ascii; decide
        exact bound c hc
      · exact decAscii c hc
    · cases close <;> (unfold AsciiHTTP.Ascii; decide)
  have cr : ∀ row ∈ rows.map String.toList, ∀ c ∈ row, c ≠ '\r' := by
    intro row mem
    simp only [rows, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · decide
    · decide
    · intro c hc
      simp only [String.toList_append, List.mem_append] at hc
      rcases hc with hc | hc
      · have h : ∀ c ∈ "content-length: ".toList, c ≠ '\r' := by decide
        exact h c hc
      · exact decCR c hc
    · cases close <;> decide
  have split := AsciiHTTP.split_crlf_join (rows.map String.toList) asc cr (by simp [rows])
  simpa only [rows, List.map_cons, List.map_nil, AsciiHTTP.crlfJoin,
    String.ofList_append, String.ofList_toList, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, jsonResponseHead, String.append_assoc] using split

/-- The actual header parser removes the encoder's space and preserves all digits. -/
theorem parse_content_length (n : Nat) :
    parseHeader ("content-length: " ++ toString n) = .ok ⟨"content-length", toString n⟩ := by
  have ascii : AsciiHTTP.Ascii (" " ++ toString n).toList := by
    intro c hc
    simp only [String.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · have h : AsciiHTTP.Ascii " ".toList := by unfold AsciiHTTP.Ascii; decide
      exact h c hc
    · have := decimal_chars n c hc; omega
  have colon : ∀ c ∈ (" " ++ toString n).toList, c ≠ ':' := by
    intro c hc eq
    simp only [String.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · subst c; contradiction
    · have := decimal_chars n c hc; subst c; contradiction
  have split := AsciiHTTP.split_colon "content-length".toList (" " ++ toString n).toList
    (by unfold AsciiHTTP.Ascii; decide) ascii (by decide) colon
  have spl : ("content-length: " ++ toString n).splitOn ":" = ["content-length", " " ++ toString n] := by
    simpa only [String.ofList_append, show ∀ c cs, String.ofList (c :: cs) = String.singleton c ++ String.ofList cs from by intros; simp [String.singleton_eq_ofList, ← String.ofList_append], String.ofList_toList,
      show String.singleton ':' = ":" from rfl, String.append_assoc] using split
  have clean : ∀ c ∈ (toString n).toList, c.isWhitespace = false := by
    intro c hc
    have bounds := decimal_chars n c hc
    simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · constructor
      · constructor <;> (intro eq; subst c; contradiction)
      · intro eq; subst c; contradiction
    · intro eq; subst c; contradiction
  have trim := trim_space_clean (toString n) clean
  have valid : (Header.mk "content-length" (toString n)).valid = true := by
    exact Bool.and_eq_true_iff.mpr ⟨by change isToken "content-length" = true; native_decide, ServiceProofs.decimal_value_valid n⟩
  simp only [parseHeader, spl]
  change (if !(Header.mk "content-length" ((" " ++ toString n).trimAscii.toString)).valid then _ else _) = _
  rw [trim, valid]
  change Except.ok (Header.mk "content-length" ((" " ++ toString n).trimAscii.toString)) = _
  rw [trim]

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

/-- No CR can begin a CRLFCRLF here: either it is absent, or the third byte
is present and differs. This also rules out matches crossing into the suffix. -/
private def SafePrefix (b : ByteArray) : Prop :=
  ∀ j (h : j < b.size), b[j]'h ≠ 13 ∨ ∃ h2 : j+2 < b.size, b[j+2]'h2 ≠ 13

private theorem find_prepend (pre tail : ByteArray) (k : Nat)
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

private theorem decimal_no_cr (n : Nat) :
    ∀ j (h : j < (toString n).toUTF8.size), (toString n).toUTF8[j]'h ≠ 13 := by
  intro j hj
  have digits : ∀ c ∈ (toString n).toList, c.isDigit = true := by
    intro c hc
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  have all : ∀ b ∈ (toString n).toList.utf8Encode.data.toList, b ≠ (13 : UInt8) := by
    simp only [List.utf8Encode, List.data_toByteArray, List.toList_toArray, List.mem_flatMap]
    intro b hb
    obtain ⟨c,hc,hb⟩ := hb
    have digit := digits c hc
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at digit
    have bounds := decimal_chars n c hc
    have small : c.val.toNat ≤ 127 := by change c.toNat ≤ 127; omega
    simp [String.utf8EncodeChar, small] at hb
    subst b
    intro eq
    have eqNat := congrArg UInt8.toNat eq
    change c.val.toNat % 256 = 13 at eqNat
    change 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 at bounds
    omega
  simp only [String.utf8Encode_toList] at all
  apply all
  exact List.mem_iff_getElem.mpr ⟨j, by simpa using hj, rfl⟩

/-- The first complete terminator is precisely the one following the last field. -/
theorem json_head_boundary (n : Nat) (close : Bool) :
    findBytes ((jsonResponseHead n close ++ "\r\n\r\n").toUTF8) "\r\n\r\n".toUTF8 =
      some (jsonResponseHead n close).toUTF8.size := by
  let pre := "HTTP/1.1 200 \r\ncontent-type: application/json\r\ncontent-length: ".toUTF8
  let tail := ("\r\nConnection: " ++ (if close then "close" else "keep-alive") ++ "\r\n\r\n").toUTF8
  have safe : SafePrefix pre := by
    have checked : ∀ j : Fin pre.size, pre[j.val] ≠ 13 ∨
        ∃ h : j.val+2 < pre.size, pre[j.val+2]'h ≠ 13 := by native_decide
    intro j hj
    exact checked ⟨j,hj⟩
  have digits : SafePrefix (toString n).toUTF8 := by
    intro j hj; exact Or.inl (decimal_no_cr n j hj)
  have tailFound : findBytes tail "\r\n\r\n".toUTF8 = some (tail.size-4) := by
    cases close <;> native_decide
  have found := find_prepend pre ((toString n).toUTF8 ++ tail)
    ((toString n).toUTF8.size + (tail.size-4)) safe
    (find_prepend (toString n).toUTF8 tail (tail.size-4) digits tailFound)
  have size : pre.size + ((toString n).toUTF8.size + (tail.size-4)) =
      (jsonResponseHead n close).toUTF8.size := by
    cases close <;> simp [pre, tail, jsonResponseHead, String.toUTF8, String.toByteArray_append,
      ByteArray.size_append, Nat.add_assoc] <;> decide
  rw [size] at found
  simpa only [pre, tail, jsonResponseHead, String.append_assoc, String.toUTF8,
    String.toByteArray_append, ByteArray.append_assoc] using found
end FrontendBackend.Proofv2
