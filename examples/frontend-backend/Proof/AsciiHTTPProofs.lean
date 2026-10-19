import Proof.ByteFramingProofs
import Init.Data.String.Lemmas
namespace FrontendBackend.AsciiHTTP
def Ascii (cs : List Char) : Prop := ∀ c ∈ cs, c.toNat ≤ 127
private theorem ascii_size (c : Char) (h : c.toNat ≤ 127) : c.utf8Size = 1 := by
  unfold Char.utf8Size
  have bound : c.val ≤ 127 := h
  simp [bound]
private theorem ascii_bytes (cs : List Char) (ascii : Ascii cs) :
    (String.ofList cs).utf8ByteSize = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [show String.ofList (c :: cs) = String.singleton c ++ String.ofList cs by simp [String.singleton_eq_ofList, ← String.ofList_append]]
    rw [String.utf8ByteSize_append, String.utf8ByteSize_singleton,
      ascii_size c (ascii c (by simp)), ih (by intro d hd; exact ascii d (by simp [hd]))]
    simp [Nat.add_comm]
private theorem raw_get_aux (cs : List Char) (ascii : Ascii cs) (base i : Nat) :
    String.Pos.Raw.utf8GetAux cs ⟨base⟩ ⟨base+i⟩ = cs[i]?.getD default := by
  induction cs generalizing base i with
  | nil => rfl
  | cons c cs ih =>
    rw [String.Pos.Raw.utf8GetAux]
    have size := ascii_size c (ascii c (by simp))
    cases i with
    | zero => simp
    | succ i =>
      have ne : (⟨base⟩ : String.Pos.Raw) ≠ ⟨base + (i+1)⟩ := by
        intro eq; have := congrArg String.Pos.Raw.byteIdx eq; simp at this
      rw [if_neg ne]
      have pos : (⟨base⟩ : String.Pos.Raw) + c = ⟨base+1⟩ := by
        apply String.Pos.Raw.ext; simp [size]
      rw [pos]
      have arith : base + (i+1) = (base+1)+i := by omega
      rw [arith, ih (by intro d hd; exact ascii d (by simp [hd]))]
      rfl
private theorem raw_get (cs : List Char) (ascii : Ascii cs) (i : Nat) :
    (⟨i⟩ : String.Pos.Raw).get (String.ofList cs) = cs[i]?.getD default := by
  simpa [String.Pos.Raw.get] using raw_get_aux cs ascii 0 i
private theorem raw_take (cs : List Char) (ascii : Ascii cs) (base n : Nat) :
    String.Pos.Raw.extract.go₂ cs ⟨base⟩ ⟨base+n⟩ = cs.take n := by
  induction cs generalizing base n with
  | nil => simp [String.Pos.Raw.extract.go₂]
  | cons c cs ih =>
    rw [String.Pos.Raw.extract.go₂]
    have size := ascii_size c (ascii c (by simp))
    cases n with
    | zero => simp
    | succ n =>
      have ne : (⟨base⟩ : String.Pos.Raw) ≠ ⟨base+(n+1)⟩ := by
        intro eq; have := congrArg String.Pos.Raw.byteIdx eq; simp at this
      rw [if_neg ne]
      have pos : (⟨base⟩ : String.Pos.Raw) + c = ⟨base+1⟩ := by
        apply String.Pos.Raw.ext; simp [size]
      rw [pos]
      have arith : base+(n+1) = (base+1)+n := by omega
      rw [arith, ih (by intro d hd; exact ascii d (by simp [hd]))]
      rfl
private theorem raw_drop_take (cs : List Char) (ascii : Ascii cs) (base i n : Nat) :
    String.Pos.Raw.extract.go₁ cs ⟨base⟩ ⟨base+i⟩ ⟨base+i+n⟩ = (cs.drop i).take n := by
  induction cs generalizing base i n with
  | nil => simp [String.Pos.Raw.extract.go₁]
  | cons c cs ih =>
    rw [String.Pos.Raw.extract.go₁]
    have size := ascii_size c (ascii c (by simp))
    cases i with
    | zero => simpa using raw_take (c :: cs) ascii base n
    | succ i =>
      have ne : (⟨base⟩ : String.Pos.Raw) ≠ ⟨base+(i+1)⟩ := by
        intro eq; have := congrArg String.Pos.Raw.byteIdx eq; simp at this
      rw [if_neg ne]
      have pos : (⟨base⟩ : String.Pos.Raw) + c = ⟨base+1⟩ := by
        apply String.Pos.Raw.ext; simp [size]
      rw [pos]
      have arith : base+(i+1) = (base+1)+i := by omega
      rw [arith, ih (by intro d hd; exact ascii d (by simp [hd]))]
      rfl
private theorem raw_extract (cs : List Char) (ascii : Ascii cs) (i n : Nat) :
    (⟨i⟩ : String.Pos.Raw).extract (String.ofList cs) ⟨i+n⟩ = String.ofList ((cs.drop i).take n) := by
  unfold String.Pos.Raw.extract
  cases n with
  | zero => simp
  | succ n =>
    simp only [show ¬ i + (n+1) ≤ i by omega, ↓reduceIte,
      String.toList_ofList]
    simpa using congrArg String.ofList (raw_drop_take cs ascii 0 i (n+1))

private theorem ascii_append (a b : List Char) : Ascii (a ++ b) ↔ Ascii a ∧ Ascii b := by
  simp only [Ascii, List.mem_append, or_imp, forall_and]

private theorem raw_get_prefix (pre : List Char) (c : Char) (tail : List Char)
    (ascii : Ascii (pre ++ c :: tail)) :
    (⟨pre.length⟩ : String.Pos.Raw).get (String.ofList (pre ++ c :: tail)) = c := by
  rw [raw_get _ ascii]
  simp

private theorem raw_next_prefix (pre : List Char) (c : Char) (tail : List Char)
    (ascii : Ascii (pre ++ c :: tail)) :
    (⟨pre.length⟩ : String.Pos.Raw).next (String.ofList (pre ++ c :: tail)) = ⟨pre.length+1⟩ := by
  unfold String.Pos.Raw.next
  rw [raw_get_prefix _ _ _ ascii]
  apply String.Pos.Raw.ext
  simp [ascii_size c (ascii c (by simp))]

private theorem split_skip (pre segment tail : List Char) (sep : String)
    (b : String.Pos.Raw) (r : List String)
    (ascii : Ascii (pre ++ segment ++ tail))
    (avoid : ∀ c ∈ segment, c ≠ (0 : String.Pos.Raw).get sep) :
    String.splitOnAux (String.ofList (pre ++ segment ++ tail)) sep b ⟨pre.length⟩ 0 r =
      String.splitOnAux (String.ofList (pre ++ segment ++ tail)) sep b ⟨pre.length + segment.length⟩ 0 r := by
  induction segment generalizing pre with
  | nil => simp
  | cons c cs ih =>
    have eqList : pre ++ (c :: cs) ++ tail = pre ++ c :: (cs ++ tail) := by simp
    have asc : Ascii (pre ++ c :: (cs ++ tail)) := eqList ▸ ascii
    rw [String.splitOnAux]
    have notEnd : (⟨pre.length⟩ : String.Pos.Raw).atEnd (String.ofList (pre ++ (c :: cs) ++ tail)) = false := by
      simp only [String.Pos.Raw.atEnd, ascii_bytes _ ascii, List.length_append, List.length_cons]
      simp; omega
    rw [notEnd, if_neg (by decide)]
    have get : (⟨pre.length⟩ : String.Pos.Raw).get (String.ofList (pre ++ (c :: cs) ++ tail)) = c := by
      rw [eqList]; exact raw_get_prefix pre c (cs ++ tail) asc
    rw [get, if_neg (by simpa using avoid c (by simp))]
    have next : ((⟨pre.length⟩ : String.Pos.Raw).unoffsetBy 0).next
        (String.ofList (pre ++ (c :: cs) ++ tail)) = ⟨pre.length+1⟩ := by
      change (⟨pre.length - 0⟩ : String.Pos.Raw).next _ = _
      simp only [Nat.sub_zero, eqList]
      exact raw_next_prefix pre c (cs ++ tail) asc
    rw [next]
    have eq : pre ++ (c :: cs) ++ tail = (pre ++ [c]) ++ cs ++ tail := by simp
    have h := ih (pre ++ [c]) (eq ▸ ascii) (by intro d hd; exact avoid d (by simp [hd]))
    simpa [← eq, List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


private theorem split_crlf_step (pre row tail : List Char) (r : List String)
    (ascii : Ascii (pre ++ row ++ ['\r', '\n'] ++ tail))
    (avoid : ∀ c ∈ row, c ≠ '\r') :
    let s := String.ofList (pre ++ row ++ ['\r', '\n'] ++ tail)
    String.splitOnAux s "\r\n" ⟨pre.length⟩ ⟨pre.length⟩ 0 r =
      String.splitOnAux s "\r\n" ⟨pre.length+row.length+2⟩ ⟨pre.length+row.length+2⟩ 0
        (String.ofList row :: r) := by
  dsimp only
  have skip := split_skip pre row (['\r', '\n'] ++ tail) "\r\n" ⟨pre.length⟩ r
    (by simpa only [List.append_assoc] using ascii) avoid
  simp only [← List.append_assoc] at skip
  rw [skip]
  let s := String.ofList (pre ++ row ++ ['\r', '\n'] ++ tail)
  let k := pre.length + row.length
  have get0 : (⟨k⟩ : String.Pos.Raw).get s = '\r' := by
    dsimp [s, k]; rw [raw_get _ ascii]; simp
  have get1 : (⟨k+1⟩ : String.Pos.Raw).get s = '\n' := by
    dsimp [s, k]; rw [raw_get _ ascii]; simp [List.getElem?_append, show ¬ pre.length + row.length + 1 < pre.length by omega, show pre.length + row.length + 1 - pre.length = row.length + 1 by omega]
  have next0 : (⟨k⟩ : String.Pos.Raw).next s = ⟨k+1⟩ := by
    unfold String.Pos.Raw.next; rw [get0]; rfl
  have next1 : (⟨k+1⟩ : String.Pos.Raw).next s = ⟨k+2⟩ := by
    unfold String.Pos.Raw.next; rw [get1]; rfl
  have end0 : (⟨k⟩ : String.Pos.Raw).atEnd s = false := by
    dsimp [s, k]; simp only [String.Pos.Raw.atEnd, ascii_bytes _ ascii, List.length_append, List.length_cons, List.length_nil]; simp; omega
  have end1 : (⟨k+1⟩ : String.Pos.Raw).atEnd s = false := by
    dsimp [s, k]; simp only [String.Pos.Raw.atEnd, ascii_bytes _ ascii, List.length_append, List.length_cons, List.length_nil]; simp; omega
  change String.splitOnAux s "\r\n" ⟨pre.length⟩ ⟨k⟩ 0 r = _
  rw [String.splitOnAux, end0]
  simp only [Bool.false_eq_true, ↓reduceIte, get0,
    show (0 : String.Pos.Raw).get "\r\n" = '\r' from rfl,
    show ('\r' == '\r') = true from rfl, next0]
  change String.splitOnAux s "\r\n" ⟨pre.length⟩ ⟨k+1⟩ ⟨1⟩ r = _
  rw [String.splitOnAux, end1]
  simp only [Bool.false_eq_true, ↓reduceIte, get1,
    show (⟨1⟩ : String.Pos.Raw).get "\r\n" = '\n' from rfl,
    show ('\n' == '\n') = true from rfl, next1]
  change String.splitOnAux s "\r\n" ⟨k+2⟩ ⟨k+2⟩ 0
    ((⟨pre.length⟩ : String.Pos.Raw).extract s ⟨k+2-2⟩ :: r) = _
  have extract : (⟨pre.length⟩ : String.Pos.Raw).extract s ⟨k+2-2⟩ = String.ofList row := by
    simp only [Nat.add_sub_cancel]
    dsimp [s, k]
    rw [raw_extract _ ascii]
    simp
  rw [extract]


private theorem split_last (pre row : List Char) (sep : String) (r : List String)
    (ascii : Ascii (pre ++ row)) (avoid : ∀ c ∈ row, c ≠ (0 : String.Pos.Raw).get sep) :
    String.splitOnAux (String.ofList (pre ++ row)) sep ⟨pre.length⟩ ⟨pre.length⟩ 0 r =
      (String.ofList row :: r).reverse := by
  have skip := split_skip pre row [] sep ⟨pre.length⟩ r (by simpa using ascii) avoid
  simp only [List.append_nil] at skip
  rw [skip, String.splitOnAux]
  have ended : (⟨pre.length+row.length⟩ : String.Pos.Raw).atEnd (String.ofList (pre ++ row)) = true := by
    simp only [String.Pos.Raw.atEnd, ascii_bytes _ ascii, List.length_append]; simp
  rw [ended, if_pos rfl, raw_extract _ ascii]
  simp

def crlfJoin : List (List Char) → List Char
  | [] => []
  | [row] => row
  | row :: next :: rows => row ++ ['\r', '\n'] ++ crlfJoin (next :: rows)

private theorem crlfJoin_ascii (rows : List (List Char))
    (ascii : ∀ row ∈ rows, Ascii row) : Ascii (crlfJoin rows) := by
  match rows with
  | [] => simp [crlfJoin, Ascii]
  | [row] => exact ascii row (by simp)
  | row :: next :: rows =>
    rw [crlfJoin, ascii_append, ascii_append]
    exact ⟨⟨ascii row (by simp), by simp [Ascii]⟩,
      crlfJoin_ascii (next :: rows) (by intro r hr; exact ascii r (by simp [hr]))⟩

private theorem split_crlf_join_aux (rows : List (List Char)) (pre : List Char) (r : List String)
    (asciiPre : Ascii pre) (ascii : ∀ row ∈ rows, Ascii row)
    (avoid : ∀ row ∈ rows, ∀ c ∈ row, c ≠ '\r') (nonempty : rows ≠ []) :
    String.splitOnAux (String.ofList (pre ++ crlfJoin rows)) "\r\n" ⟨pre.length⟩ ⟨pre.length⟩ 0 r =
      r.reverse ++ rows.map String.ofList := by
  match rows with
  | [] => contradiction
  | [row] =>
    rw [crlfJoin, split_last pre row "\r\n" r
      ((ascii_append _ _).mpr ⟨asciiPre, ascii row (by simp)⟩) (avoid row (by simp))]
    simp
  | row :: next :: rows =>
    have tailAscii := crlfJoin_ascii (next :: rows) (by intro x hx; exact ascii x (by simp [hx]))
    have whole : Ascii (pre ++ row ++ ['\r', '\n'] ++ crlfJoin (next :: rows)) := by
      simp only [ascii_append]
      exact ⟨⟨⟨asciiPre, ascii row (by simp)⟩, by simp [Ascii]⟩, tailAscii⟩
    simp only [crlfJoin, ← List.append_assoc]
    rw [split_crlf_step pre row (crlfJoin (next :: rows)) r whole (avoid row (by simp))]
    have ih := split_crlf_join_aux (next :: rows) (pre ++ row ++ ['\r', '\n'])
      (String.ofList row :: r)
      ((ascii_append _ _).mp whole).1
      (by intro x hx; exact ascii x (by simp [hx]))
      (by intro x hx; exact avoid x (by simp [hx])) (by simp)
    simpa only [List.length_append, List.length_cons, List.length_nil,
      List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append] using ih

theorem split_crlf_join (rows : List (List Char))
    (ascii : ∀ row ∈ rows, Ascii row)
    (avoid : ∀ row ∈ rows, ∀ c ∈ row, c ≠ '\r') (nonempty : rows ≠ []) :
    (String.ofList (crlfJoin rows)).splitOn "\r\n" = rows.map String.ofList := by
  have h := split_crlf_join_aux rows [] [] (by simp [Ascii]) ascii avoid nonempty
  simpa [String.splitOn] using h


theorem split_colon (left right : List Char)
    (asciiLeft : Ascii left) (asciiRight : Ascii right)
    (avoidLeft : ∀ c ∈ left, c ≠ ':') (avoidRight : ∀ c ∈ right, c ≠ ':') :
    (String.ofList (left ++ ':' :: right)).splitOn ":" =
      [String.ofList left, String.ofList right] := by
  have ascii : Ascii (left ++ ':' :: right) := by
    intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact asciiLeft c hc
    · decide
    · exact asciiRight c hc
  unfold String.splitOn
  change String.splitOnAux (String.ofList (left ++ ':' :: right)) ":" 0 0 0 [] = _
  have skip := split_skip [] left (':' :: right) ":" 0 [] (by simpa using ascii) avoidLeft
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at skip
  change String.splitOnAux (String.ofList (left ++ ':' :: right)) ":" 0 ⟨0⟩ 0 [] = _
  rw [skip, String.splitOnAux]
  have ended : (⟨left.length⟩ : String.Pos.Raw).atEnd (String.ofList (left ++ ':' :: right)) = false := by
    simp only [String.Pos.Raw.atEnd, ascii_bytes _ ascii, List.length_append, List.length_cons]
    simp
  rw [ended]
  simp only [Bool.false_eq_true, ↓reduceIte, raw_get_prefix left ':' right ascii,
    show (0 : String.Pos.Raw).get ":" = ':' from rfl,
    show (':' == ':') = true from rfl, raw_next_prefix left ':' right ascii]
  change String.splitOnAux (String.ofList (left ++ ':' :: right)) ":" ⟨left.length+1⟩ ⟨left.length+1⟩ 0
    ((0 : String.Pos.Raw).extract (String.ofList (left ++ ':' :: right)) ⟨left.length+1-1⟩ :: []) = _
  have extracted : (0 : String.Pos.Raw).extract (String.ofList (left ++ ':' :: right)) ⟨left.length+1-1⟩ = String.ofList left := by
    simpa using raw_extract (left ++ ':' :: right) ascii 0 left.length
  rw [extracted]
  have last := split_last (left ++ [':']) right ":" [String.ofList left]
    (by simpa using ascii) avoidRight
  simpa using last
end FrontendBackend.AsciiHTTP
