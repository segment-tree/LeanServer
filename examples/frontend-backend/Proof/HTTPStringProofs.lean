import Proof.AsciiHTTPProofs
import Proof.StringJoinProofs

/-! Splitting the actual legacy String.splitOn at UTF-8 byte boundaries.
Unlike the ASCII response helpers, these proofs allow arbitrary Unicode fields. -/

namespace FrontendBackend.HTTPStrings
private def width (cs : List Char) := (String.ofList cs).utf8ByteSize
@[simp] private theorem width_nil : width [] = 0 := rfl
@[simp] private theorem width_append (a b : List Char) : width (a ++ b) = width a + width b := by
  simp [width]
@[simp] private theorem width_cons (c : Char) (cs : List Char) : width (c :: cs) = c.utf8Size + width cs := by
  rw [show c :: cs = [c] ++ cs from rfl, width_append]
  simp only [width, ← String.singleton_eq_ofList, String.utf8ByteSize_singleton]
private theorem width_pos (c : Char) (cs : List Char) : 0 < width (c :: cs) := by
  rw [width_cons]; have := c.utf8Size_pos; omega
private theorem get_aux (pre : List Char) (c : Char) (tail : List Char) (base : Nat) :
    String.Pos.Raw.utf8GetAux (pre ++ c :: tail) ⟨base⟩ ⟨base + width pre⟩ = c := by
  induction pre generalizing base with
  | nil => simp [String.Pos.Raw.utf8GetAux]
  | cons d ds ih =>
    rw [List.cons_append, String.Pos.Raw.utf8GetAux]
    have pos := width_pos d ds
    rw [if_neg (by intro eq; have he := congrArg String.Pos.Raw.byteIdx eq; change base = base + _ at he; omega)]
    change String.Pos.Raw.utf8GetAux (ds ++ c :: tail) ⟨base+d.utf8Size⟩ _ = _
    simpa only [width_cons, Nat.add_assoc] using ih (base+d.utf8Size)
private theorem raw_get (pre : List Char) (c : Char) (tail : List Char) :
    (⟨width pre⟩ : String.Pos.Raw).get (String.ofList (pre ++ c :: tail)) = c := by
  simpa [String.Pos.Raw.get] using get_aux pre c tail 0
private theorem raw_next (pre : List Char) (c : Char) (tail : List Char) :
    (⟨width pre⟩ : String.Pos.Raw).next (String.ofList (pre ++ c :: tail)) = ⟨width pre+c.utf8Size⟩ := by
  unfold String.Pos.Raw.next
  rw [raw_get]
  rfl
private theorem take_aux (row tail : List Char) (base : Nat) :
    String.Pos.Raw.extract.go₂ (row ++ tail) ⟨base⟩ ⟨base+width row⟩ = row := by
  induction row generalizing base with
  | nil => cases tail <;> simp [String.Pos.Raw.extract.go₂]
  | cons c cs ih =>
    rw [List.cons_append, String.Pos.Raw.extract.go₂]
    have pos := width_pos c cs
    rw [if_neg (by intro eq; have he := congrArg String.Pos.Raw.byteIdx eq; change base = base + _ at he; omega)]
    congr 1
    change String.Pos.Raw.extract.go₂ (cs ++ tail) ⟨base+c.utf8Size⟩ _ = _
    simpa only [width_cons, Nat.add_assoc] using ih (base+c.utf8Size)
private theorem extract_aux (pre row tail : List Char) (base : Nat) :
    String.Pos.Raw.extract.go₁ (pre ++ row ++ tail) ⟨base⟩ ⟨base+width pre⟩ ⟨base+width pre+width row⟩ = row := by
  induction pre generalizing base with
  | nil =>
    simp only [List.nil_append, width_nil, Nat.add_zero]
    cases row with
    | nil => cases tail <;> simp [String.Pos.Raw.extract.go₁, String.Pos.Raw.extract.go₂]
    | cons c cs => simpa only [List.cons_append, String.Pos.Raw.extract.go₁, ↓reduceIte] using take_aux (c :: cs) tail base
  | cons c cs ih =>
    rw [List.cons_append, List.cons_append, String.Pos.Raw.extract.go₁]
    have pos := width_pos c cs
    rw [if_neg (by intro eq; have he := congrArg String.Pos.Raw.byteIdx eq; change base = base + _ at he; omega)]
    change String.Pos.Raw.extract.go₁ (cs ++ row ++ tail) ⟨base+c.utf8Size⟩ _ _ = _
    simpa only [width_cons, Nat.add_assoc] using ih (base+c.utf8Size)
private theorem raw_extract (pre row tail : List Char) :
    (⟨width pre⟩ : String.Pos.Raw).extract (String.ofList (pre ++ row ++ tail)) ⟨width pre+width row⟩ = String.ofList row := by
  cases row with
  | nil => simp [String.Pos.Raw.extract]
  | cons c cs =>
    have pos := width_pos c cs
    simp only [String.Pos.Raw.extract, show ¬ width pre + width (c :: cs) ≤ width pre by omega, ↓reduceIte,
      String.toList_ofList]
    simpa using congrArg String.ofList (extract_aux pre (c :: cs) tail 0)

private theorem split_skip (pre segment tail : List Char) (sep : String)
    (b : String.Pos.Raw) (r : List String)
    (avoid : ∀ c ∈ segment, c ≠ (0 : String.Pos.Raw).get sep) :
    String.splitOnAux (String.ofList (pre ++ segment ++ tail)) sep b ⟨width pre⟩ 0 r =
      String.splitOnAux (String.ofList (pre ++ segment ++ tail)) sep b ⟨width pre+width segment⟩ 0 r := by
  induction segment generalizing pre with
  | nil => simp
  | cons c cs ih =>
    rw [String.splitOnAux]
    have notEnd : (⟨width pre⟩ : String.Pos.Raw).atEnd (String.ofList (pre ++ (c :: cs) ++ tail)) = false := by
      change decide (width pre ≥ width (pre ++ (c :: cs) ++ tail)) = false
      simp only [width_append, width_cons, decide_eq_false_iff_not]
      have := c.utf8Size_pos; omega
    rw [notEnd, if_neg (by decide)]
    have get : (⟨width pre⟩ : String.Pos.Raw).get (String.ofList (pre ++ (c :: cs) ++ tail)) = c := by
      simpa only [List.append_assoc, List.cons_append] using raw_get pre c (cs ++ tail)
    rw [get, if_neg (by simpa using avoid c (by simp))]
    have next : ((⟨width pre⟩ : String.Pos.Raw).unoffsetBy 0).next
        (String.ofList (pre ++ (c :: cs) ++ tail)) = ⟨width pre+c.utf8Size⟩ := by
      change (⟨width pre-0⟩ : String.Pos.Raw).next _ = _
      simpa only [Nat.sub_zero, List.append_assoc, List.cons_append] using raw_next pre c (cs ++ tail)
    rw [next]
    have ih := ih (pre ++ [c]) (by intro d hd; exact avoid d (by simp [hd]))
    simpa only [List.append_assoc, List.cons_append, List.nil_append, width_append, width_cons,
      width_nil, Nat.add_zero, Nat.add_assoc] using ih
private theorem split_last (pre row : List Char) (sep : String) (r : List String)
    (avoid : ∀ c ∈ row, c ≠ (0 : String.Pos.Raw).get sep) :
    String.splitOnAux (String.ofList (pre ++ row)) sep ⟨width pre⟩ ⟨width pre⟩ 0 r =
      (String.ofList row :: r).reverse := by
  have skip := split_skip pre row [] sep ⟨width pre⟩ r avoid
  simp only [List.append_nil] at skip
  rw [skip, String.splitOnAux]
  have ended : (⟨width pre+width row⟩ : String.Pos.Raw).atEnd (String.ofList (pre ++ row)) = true := by
    change decide (width pre+width row ≥ width (pre++row)) = true
    simp
  rw [ended, if_pos rfl]
  have ext := raw_extract pre row []
  simp only [List.append_nil] at ext
  rw [ext]

private theorem split_char_step (pre row tail : List Char) (sep : Char) (r : List String)
    (avoid : ∀ c ∈ row, c ≠ sep) :
    let s := String.ofList (pre ++ row ++ sep :: tail)
    String.splitOnAux s (String.singleton sep) ⟨width pre⟩ ⟨width pre⟩ 0 r =
      String.splitOnAux s (String.singleton sep) ⟨width pre+width row+sep.utf8Size⟩
        ⟨width pre+width row+sep.utf8Size⟩ 0 (String.ofList row :: r) := by
  dsimp only
  have sepGet : (0 : String.Pos.Raw).get (String.singleton sep) = sep := by
    simp [String.Pos.Raw.get, String.singleton_eq_ofList, String.Pos.Raw.utf8GetAux]
  have skip := split_skip pre row (sep :: tail) (String.singleton sep) ⟨width pre⟩ r
    (by simpa only [sepGet] using avoid)
  rw [skip, String.splitOnAux]
  have notEnd : (⟨width pre+width row⟩ : String.Pos.Raw).atEnd (String.ofList (pre ++ row ++ sep :: tail)) = false := by
    change decide (width pre+width row ≥ width (pre++row++sep::tail)) = false
    simp only [width_append, width_cons, decide_eq_false_iff_not]
    have := sep.utf8Size_pos; omega
  have get : (⟨width pre+width row⟩ : String.Pos.Raw).get (String.ofList (pre ++ row ++ sep :: tail)) = sep := by
    simpa only [width_append] using raw_get (pre++row) sep tail
  have next : (⟨width pre+width row⟩ : String.Pos.Raw).next (String.ofList (pre ++ row ++ sep :: tail)) =
      ⟨width pre+width row+sep.utf8Size⟩ := by
    simpa only [width_append] using raw_next (pre++row) sep tail
  rw [notEnd, if_neg (by decide), get, sepGet]
  simp only [beq_self_eq_true, ↓reduceIte, next]
  have sepNext : (0 : String.Pos.Raw).next (String.singleton sep) = ⟨sep.utf8Size⟩ := by
    unfold String.Pos.Raw.next; rw [sepGet]; apply String.Pos.Raw.ext; simp
  rw [sepNext]
  have sepEnd : (⟨sep.utf8Size⟩ : String.Pos.Raw).atEnd (String.singleton sep) = true := by
    simp [String.Pos.Raw.atEnd]
  rw [sepEnd, if_pos rfl]
  change String.splitOnAux _ _ _ _ _
    ((⟨width pre⟩ : String.Pos.Raw).extract _ ⟨width pre+width row+sep.utf8Size-sep.utf8Size⟩ :: r) = _
  rw [Nat.add_sub_cancel, raw_extract]

def join (sep : List Char) : List (List Char) → List Char
  | [] => []
  | [row] => row
  | row :: next :: rows => row ++ sep ++ join sep (next :: rows)

private theorem split_char_join_aux (sep : Char) (rows : List (List Char)) (pre : List Char) (r : List String)
    (avoid : ∀ row ∈ rows, ∀ c ∈ row, c ≠ sep) (nonempty : rows ≠ []) :
    String.splitOnAux (String.ofList (pre ++ join [sep] rows)) (String.singleton sep) ⟨width pre⟩ ⟨width pre⟩ 0 r =
      r.reverse ++ rows.map String.ofList := by
  match rows with
  | [] => contradiction
  | [row] =>
    have sepGet : (0 : String.Pos.Raw).get (String.singleton sep) = sep := by
      simp [String.Pos.Raw.get, String.singleton_eq_ofList, String.Pos.Raw.utf8GetAux]
    rw [join, split_last pre row (String.singleton sep) r (by simpa only [sepGet] using avoid row (by simp))]
    simp
  | row :: next :: rows =>
    simp only [join]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [← List.append_assoc]
    rw [split_char_step pre row (join [sep] (next :: rows)) sep r (avoid row (by simp))]
    have ih := split_char_join_aux sep (next::rows) (pre++row++[sep]) (String.ofList row :: r)
      (by intro row hr; exact avoid row (by simp [hr])) (by simp)
    simpa only [List.append_assoc, List.cons_append, List.nil_append, width_append, width_cons,
      width_nil, Nat.add_zero, Nat.add_assoc, List.reverse_cons, List.map_cons, List.singleton_append] using ih

theorem split_char_join (sep : Char) (rows : List (List Char))
    (avoid : ∀ row ∈ rows, ∀ c ∈ row, c ≠ sep) (nonempty : rows ≠ []) :
    (String.ofList (join [sep] rows)).splitOn (String.singleton sep) = rows.map String.ofList := by
  have h := split_char_join_aux sep rows [] [] avoid nonempty
  simpa [String.splitOn, String.singleton_ne_empty] using h

private theorem partition (sep : Char) (cs : List Char) :
    ∃ rows : List (List Char), rows ≠ [] ∧ join [sep] rows = cs ∧
      ∀ row ∈ rows, ∀ c ∈ row, c ≠ sep := by
  induction cs with
  | nil => exact ⟨[[]], by simp, rfl, by simp⟩
  | cons c cs ih =>
    obtain ⟨rows, ne, eq, avoid⟩ := ih
    cases rows with
    | nil => contradiction
    | cons row rows =>
      by_cases h : c = sep
      · subst c
        refine ⟨[] :: row :: rows, by simp, ?_, ?_⟩
        · simpa only [join, List.nil_append, List.singleton_append] using congrArg (sep :: ·) eq
        · intro r hr d hd
          rcases List.mem_cons.mp hr with rfl | hr
          · contradiction
          · exact avoid r hr d hd
      · refine ⟨(c :: row) :: rows, by simp, ?_, ?_⟩
        · cases rows <;> simpa only [join, List.cons_append] using congrArg (c :: ·) eq
        · intro r hr d hd
          rcases List.mem_cons.mp hr with rfl | hr
          · rcases List.mem_cons.mp hd with rfl | hd
            · exact h
            · exact avoid row (by simp) d hd
          · exact avoid r (by simp [hr]) d hd

private theorem ofList_join (sep : List Char) (rows : List (List Char)) :
    String.ofList (join sep rows) = String.intercalate (String.ofList sep) (rows.map String.ofList) := by
  match rows with
  | [] => rfl
  | [row] => simp [join, intercalate_one]
  | row :: next :: rows =>
    rw [join, String.ofList_append, String.ofList_append, ofList_join sep (next :: rows)]
    simp [intercalate_cons, String.append_assoc]

theorem split_char_reassemble (s : String) (sep : Char) :
    String.intercalate (String.singleton sep) (s.splitOn (String.singleton sep)) = s := by
  obtain ⟨rows, ne, eq, avoid⟩ := partition sep s.toList
  have asString : String.ofList (join [sep] rows) = s := by rw [eq, String.ofList_toList]
  rw [← asString, split_char_join sep rows avoid ne, String.singleton_eq_ofList, ← ofList_join]

theorem split_char_prefix (name value : String) (sep : Char)
    (avoid : ∀ c ∈ name.toList, c ≠ sep) :
    (name ++ String.singleton sep ++ value).splitOn (String.singleton sep) =
      name :: value.splitOn (String.singleton sep) := by
  obtain ⟨rows, ne, eq, no⟩ := partition sep value.toList
  have asString : String.ofList (join [sep] rows) = value := by rw [eq, String.ofList_toList]
  have split := split_char_join sep (name.toList :: rows) (by
    intro row hr c hc
    rcases List.mem_cons.mp hr with rfl | hr
    · exact avoid c hc
    · exact no row hr c hc) (by simp)
  cases rows with
  | nil => contradiction
  | cons row rows =>
    simpa only [join, String.ofList_append, ← String.singleton_eq_ofList, asString,
      List.map_cons, String.ofList_toList, ← split_char_join sep (row::rows) no ne] using split

theorem split_char_nonempty (s : String) (sep : Char) : s.splitOn (String.singleton sep) ≠ [] := by
  obtain ⟨rows, ne, eq, no⟩ := partition sep s.toList
  have asString : String.ofList (join [sep] rows) = s := by rw [eq, String.ofList_toList]
  rw [← asString, split_char_join sep rows no ne]
  simpa using ne
private theorem split_crlf_step (pre row tail : List Char) (r : List String)
    (avoid : ∀ c ∈ row, c ≠ '\r') :
    let s := String.ofList (pre ++ row ++ ['\r', '\n'] ++ tail)
    String.splitOnAux s "\r\n" ⟨width pre⟩ ⟨width pre⟩ 0 r =
      String.splitOnAux s "\r\n" ⟨width pre+width row+2⟩ ⟨width pre+width row+2⟩ 0
        (String.ofList row :: r) := by
  dsimp only
  have skip := split_skip pre row (['\r', '\n'] ++ tail) "\r\n" ⟨width pre⟩ r avoid
  simp only [← List.append_assoc] at skip
  rw [skip]
  let s := String.ofList (pre ++ row ++ ['\r', '\n'] ++ tail)
  let k := width pre + width row
  have get0 : (⟨k⟩ : String.Pos.Raw).get s = '\r' := by
    simpa only [s, k, width_append, List.append_assoc, List.cons_append, List.nil_append] using raw_get (pre++row) '\r' ('\n'::tail)
  have get1 : (⟨k+1⟩ : String.Pos.Raw).get s = '\n' := by
    simpa only [s, k, width_append, width_cons, width_nil, Nat.add_assoc, Nat.add_zero,
      show '\r'.utf8Size = 1 from rfl, List.append_assoc, List.cons_append, List.nil_append]
      using raw_get (pre++row++['\r']) '\n' tail
  have next0 : (⟨k⟩ : String.Pos.Raw).next s = ⟨k+1⟩ := by
    unfold String.Pos.Raw.next; rw [get0]; rfl
  have next1 : (⟨k+1⟩ : String.Pos.Raw).next s = ⟨k+2⟩ := by
    unfold String.Pos.Raw.next; rw [get1]; rfl
  have end0 : (⟨k⟩ : String.Pos.Raw).atEnd s = false := by
    change decide (k ≥ width (pre ++ row ++ ['\r','\n'] ++ tail)) = false
    simp only [width_append, width_cons, width_nil, decide_eq_false_iff_not]
    change ¬ k ≥ k + (1+(1+0)) + width tail
    omega
  have end1 : (⟨k+1⟩ : String.Pos.Raw).atEnd s = false := by
    change decide (k+1 ≥ width (pre ++ row ++ ['\r','\n'] ++ tail)) = false
    simp only [width_append, width_cons, width_nil, decide_eq_false_iff_not]
    change ¬ k+1 ≥ k + (1+(1+0)) + width tail
    omega
  change String.splitOnAux s "\r\n" ⟨width pre⟩ ⟨k⟩ 0 r = _
  rw [String.splitOnAux, end0]
  simp only [Bool.false_eq_true, ↓reduceIte, get0,
    show (0 : String.Pos.Raw).get "\r\n" = '\r' from rfl,
    show ('\r' == '\r') = true from rfl, next0]
  change String.splitOnAux s "\r\n" ⟨width pre⟩ ⟨k+1⟩ ⟨1⟩ r = _
  rw [String.splitOnAux, end1]
  simp only [Bool.false_eq_true, ↓reduceIte, get1,
    show (⟨1⟩ : String.Pos.Raw).get "\r\n" = '\n' from rfl,
    show ('\n' == '\n') = true from rfl, next1]
  change String.splitOnAux s "\r\n" ⟨k+2⟩ ⟨k+2⟩ 0
    ((⟨width pre⟩ : String.Pos.Raw).extract s ⟨k+2-2⟩ :: r) = _
  have extract : (⟨width pre⟩ : String.Pos.Raw).extract s ⟨k+2-2⟩ = String.ofList row := by
    simp only [Nat.add_sub_cancel]
    simpa only [s, k, List.append_assoc] using raw_extract pre row (['\r','\n']++tail)
  rw [extract]
private theorem split_crlf_join_aux (rows : List (List Char)) (pre : List Char) (r : List String)
    (avoid : ∀ row ∈ rows, ∀ c ∈ row, c ≠ '\r') (nonempty : rows ≠ []) :
    String.splitOnAux (String.ofList (pre ++ join ['\r','\n'] rows)) "\r\n" ⟨width pre⟩ ⟨width pre⟩ 0 r =
      r.reverse ++ rows.map String.ofList := by
  match rows with
  | [] => contradiction
  | [row] =>
    rw [join, split_last pre row "\r\n" r (avoid row (by simp))]
    simp
  | row :: next :: rows =>
    simp only [join, ← List.append_assoc]
    rw [split_crlf_step pre row (join ['\r','\n'] (next :: rows)) r (avoid row (by simp))]
    have ih := split_crlf_join_aux (next :: rows) (pre ++ row ++ ['\r', '\n'])
      (String.ofList row :: r) (by intro x hx; exact avoid x (by simp [hx])) (by simp)
    simpa only [width_append, width_cons, width_nil, Nat.add_assoc, show '\r'.utf8Size = 1 from rfl,
      show '\n'.utf8Size = 1 from rfl, Nat.add_zero,
      List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append] using ih

theorem split_crlf_join (rows : List String)
    (avoid : ∀ row ∈ rows, ∀ c ∈ row.toList, c ≠ '\r') (nonempty : rows ≠ []) :
    (String.intercalate "\r\n" rows).splitOn "\r\n" = rows := by
  have h := split_crlf_join_aux (rows.map String.toList) [] []
    (by intro row hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact avoid s hs)
    (by simpa using nonempty)
  simpa [String.splitOn, ofList_join, List.map_map, Function.comp_def] using h

theorem split_singleton_join (sep : Char) (rows : List String)
    (avoid : ∀ row ∈ rows, ∀ c ∈ row.toList, c ≠ sep) (nonempty : rows ≠ []) :
    (String.intercalate (String.singleton sep) rows).splitOn (String.singleton sep) = rows := by
  have h := split_char_join sep (rows.map String.toList)
    (by intro row hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact avoid s hs)
    (by simpa using nonempty)
  simpa [ofList_join, List.map_map, Function.comp_def, ← String.singleton_eq_ofList] using h
end FrontendBackend.HTTPStrings
