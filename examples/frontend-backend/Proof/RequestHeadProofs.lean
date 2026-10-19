import Proof.HTTPStringProofs
import Proof.TrimProofs
import Proof.ForwardingProofs
import Proof.DecimalProofs
import Proof.RequestFramingProofs
import Proof.ResponseHeadProofs

/-! The actual proxy encoder's request head: successful parsing of retained
headers, line recovery, framing, and generated protocol-header lookups. -/

namespace FrontendBackend
open LeanServer.HTTP

/-- A second parse may normalize a header value. The forwarding theorem only
needs its name and validity; it does not assert whole-header equality. -/
def reparsedHeader (h : Header) : Header :=
  ⟨h.name, (" " ++ h.value).trimAscii.toString⟩

theorem token_no_colon (s : String) (valid : isToken s = true) :
    ∀ c ∈ s.toList, c ≠ ':' := by
  intro c hc eq
  have all := (Bool.and_eq_true_iff.mp valid).2
  have digit := List.all_eq_true.mp all c hc
  subst c
  have no : ((':').toNat < 128 && ((':').isAlphanum || "!#$%&'*+-.^_`|~".contains ':')) = false := by native_decide
  rw [no] at digit
  contradiction

theorem reparsed_header_valid (h : Header) (valid : h.valid = true) :
    (reparsedHeader h).valid = true := by
  obtain ⟨name, value⟩ := Bool.and_eq_true_iff.mp valid
  apply Bool.and_eq_true_iff.mpr
  refine ⟨name, List.all_eq_true.mpr ?_⟩
  intro c hc
  have mem := trim_mem (" " ++ h.value) c hc
  simp only [String.toList_append, List.mem_append] at mem
  rcases mem with mem | mem
  · have eq : c = ' ' := by simpa using mem
    subst c; decide
  · exact List.all_eq_true.mp value c mem

set_option maxHeartbeats 800000 in
theorem parse_serialized_header (h : Header) (valid : h.valid = true) :
    parseHeader (h.name ++ ": " ++ h.value) = .ok (reparsedHeader h) := by
  have split := HTTPStrings.split_char_prefix h.name (" " ++ h.value) ':'
    (token_no_colon h.name (Bool.and_eq_true_iff.mp valid).1)
  have rejoin := HTTPStrings.split_char_reassemble (" " ++ h.value) ':'
  have ne := HTTPStrings.split_char_nonempty (" " ++ h.value) ':'
  simp only [show String.singleton ':' = ":" from rfl] at split rejoin ne
  have eq : h.name ++ ": " ++ h.value = h.name ++ ":" ++ (" " ++ h.value) := by
    simp only [String.append_assoc]; rfl
  unfold parseHeader
  rw [eq, split]
  have len : ¬ (h.name :: (" " ++ h.value).splitOn ":").length < 2 := by
    have := List.length_pos_iff.mpr ne
    simp only [List.length_cons]; omega
  simp only [if_neg len, bind, Except.bind, pure, Except.pure]
  simp only [List.head!, List.tail!]
  rw [rejoin]
  change (if !(reparsedHeader h).valid then _ else _) = _
  rw [reparsed_header_valid h valid]
  rfl

theorem token_no_cr (s : String) (valid : isToken s = true) :
    ∀ c ∈ s.toList, c ≠ '\r' := by
  intro c hc eq
  have all := (Bool.and_eq_true_iff.mp valid).2
  have bad := List.all_eq_true.mp all c hc
  subst c
  have no : (('\r').toNat < 128 && (('\r').isAlphanum || "!#$%&'*+-.^_`|~".contains '\r')) = false := by native_decide
  rw [no] at bad
  contradiction

theorem serialized_header_no_cr (h : Header) (valid : h.valid = true) :
    ∀ c ∈ (h.name ++ ": " ++ h.value).toList, c ≠ '\r' := by
  intro c hc eq
  simp only [String.toList_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact token_no_cr _ (Bool.and_eq_true_iff.mp valid).1 c hc eq
  · subst c; contradiction
  · have all := (Bool.and_eq_true_iff.mp valid).2
    have bad := List.all_eq_true.mp all c hc
    subst c
    contradiction

theorem parse_serialized_headers (hs : List Header)
    (valid : ∀ h ∈ hs, h.valid = true) :
    (hs.map fun h => h.name ++ ": " ++ h.value).mapM parseHeader = .ok (hs.map reparsedHeader) := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    simp only [List.map_cons, List.mapM_cons, parse_serialized_header h (valid h (by simp)),
      ih (by intro v hv; exact valid v (by simp [hv])), bind, Except.bind, pure, Except.pure]

theorem reparsed_getAll (hs : Headers) (name : String)
    (absent : hs.getAll name = #[]) :
    Headers.getAll (hs.map reparsedHeader) name = #[] := by
  unfold Headers.getAll at *
  apply Array.eq_empty_iff_forall_not_mem.mpr
  intro value mem
  obtain ⟨h,hm,_⟩ := Array.mem_map.mp mem
  obtain ⟨hm,matchName⟩ := Array.mem_filter.mp hm
  obtain ⟨original, originalMem, originalEq⟩ := Array.mem_map.mp hm
  subst h
  have old : original.value ∈ (hs.filter fun h => headerName h.name == headerName name).map (·.value) :=
    Array.mem_map.mpr ⟨original, Array.mem_filter.mpr ⟨originalMem,matchName⟩, rfl⟩
  rw [absent] at old
  exact Array.not_mem_empty _ old

theorem retained_protocol_absent (request : Request) (name : String)
    (protocol : name = "host" ∨ name = "content-length" ∨ name = "transfer-encoding") :
    (retainedHeaders request).getAll name = #[] := by
  have folded : headerName name = name := by rcases protocol with rfl | rfl | rfl <;> native_decide
  unfold Headers.getAll
  apply Array.eq_empty_iff_forall_not_mem.mpr
  intro value mem
  obtain ⟨h, hm, _⟩ := Array.mem_map.mp mem
  obtain ⟨hm, matched⟩ := Array.mem_filter.mp hm
  obtain ⟨_, kept⟩ := Array.mem_filter.mp hm
  have nameEq : headerName h.name = name := by simpa only [folded, beq_iff_eq] using matched
  change (!omitForwardHeader h) = true at kept
  unfold omitForwardHeader at kept
  rcases protocol with rfl | rfl | rfl <;> simp [nameEq, connectionHeaders] at kept


def requestHeaderRows (request : Request) : List String :=
  (retainedHeaders request).toList.map (fun h => h.name ++ ": " ++ h.value) ++
    ["Host: 127.0.0.1:8081", "Content-Length: " ++ toString request.body.size, "Connection: close"]

def requestHeadText (request : Request) : String :=
  String.intercalate "\r\n" ((request.method ++ " " ++ request.target ++ " HTTP/1.1") :: requestHeaderRows request)

private theorem fold_serialized (hs : List Header) (acc : String) (tail : List String) (ne : tail ≠ []) :
    hs.foldl (fun out h => out ++ h.name ++ ": " ++ h.value ++ "\r\n") acc ++
      String.intercalate "\r\n" tail =
    acc ++ String.intercalate "\r\n" ((hs.map fun h => h.name ++ ": " ++ h.value) ++ tail) := by
  induction hs generalizing acc with
  | nil => simp
  | cons h hs ih =>
    rw [List.foldl_cons, ih]
    cases tail with
    | nil => contradiction
    | cons t ts =>
      simp only [List.map_cons, List.cons_append]
      cases hs <;> simp [HTTPStrings.intercalate_cons, String.append_assoc]

theorem encoded_request_head (request : Request) :
    encodeUpstreamHead backendAddr request = (requestHeadText request ++ "\r\n\r\n").toUTF8 := by
  have fold := fold_serialized (retainedHeaders request).toList ""
    ["Host: 127.0.0.1:8081", "Content-Length: " ++ toString request.body.size, "Connection: close"] (by simp)
  simp only [String.empty_append] at fold
  have rows : requestHeaderRows request ≠ [] := by simp [requestHeaderRows]
  unfold encodeUpstreamHead requestHeadText
  rw [ServiceProofs.forwardHeaders_eq_retained]
  have joined : String.intercalate "\r\n" ((request.method ++ " " ++ request.target ++ " HTTP/1.1") :: requestHeaderRows request) =
      request.method ++ " " ++ request.target ++ " HTTP/1.1" ++ "\r\n" ++ String.intercalate "\r\n" (requestHeaderRows request) := by
    cases eq : requestHeaderRows request with
    | nil => contradiction
    | cons r rs => exact HTTPStrings.intercalate_cons _ _ _ _
  rw [joined]
  rw [show String.intercalate "\r\n" (requestHeaderRows request) = _ from fold.symm]
  simp only [HTTPStrings.intercalate_cons, HTTPStrings.intercalate_one, String.append_assoc]
  have port : toString (8081 : UInt16) = "8081" := by native_decide
  simp only [backendAddr, port]
  rfl

theorem request_line_split (request : Request) (method : request.method = "GET")
    (target : ∀ c ∈ request.target.toList, 32 < c.toNat ∧ c.toNat ≠ 127) :
    (request.method ++ " " ++ request.target ++ " HTTP/1.1").splitOn " " =
      ["GET", request.target, "HTTP/1.1"] := by
  have h := HTTPStrings.split_singleton_join ' ' ["GET",request.target,"HTTP/1.1"] (by
    intro row hr c hc eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · subst c; contradiction
    · have := target c hc; subst c; contradiction
    · subst c; contradiction) (by simp)
  simpa only [method, show String.singleton ' ' = " " from rfl,
    HTTPStrings.intercalate_cons, HTTPStrings.intercalate_one, String.append_assoc] using h

theorem request_rows_no_cr (request : Request) (method : request.method = "GET")
    (target : ∀ c ∈ request.target.toList, 32 < c.toNat ∧ c.toNat ≠ 127)
    (valid : (retainedHeaders request).all Header.valid = true) :
    ∀ row ∈ ((request.method ++ " " ++ request.target ++ " HTTP/1.1") :: requestHeaderRows request),
      ∀ c ∈ row.toList, c ≠ '\r' := by
  intro row hr c hc eq
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [method] at hc
    simp only [String.toList_append, List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · subst c; contradiction
    · subst c; contradiction
    · have := target c hc; subst c; contradiction
    · subst c; contradiction
  · simp only [requestHeaderRows, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ⟨h,hm,rfl⟩ | rfl | rfl | rfl
    · exact serialized_header_no_cr h (Array.all_eq_true_iff_forall_mem.mp valid h (by simpa using hm)) c hc eq
    · subst c; contradiction
    · simp only [String.toList_append, List.mem_append] at hc
      rcases hc with hc | hc
      · subst c; contradiction
      · have digit := ServiceProofs.decimal_value_valid request.body.size
        have bad := List.all_eq_true.mp digit c hc
        subst c; contradiction
    · subst c; contradiction
theorem request_rows_nonempty (request : Request) :
    ∀ row ∈ requestHeaderRows request, row ≠ "" := by
  intro row hr
  simp only [requestHeaderRows, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨h,_,rfl⟩ | rfl | rfl | rfl <;> simp

theorem request_head_boundary (request : Request) (method : request.method = "GET")
    (target : ∀ c ∈ request.target.toList, 32 < c.toNat ∧ c.toNat ≠ 127)
    (valid : (retainedHeaders request).all Header.valid = true) :
    findBytes (encodeUpstreamHead backendAddr request) "\r\n\r\n".toUTF8 =
      some (requestHeadText request).toUTF8.size := by
  rw [encoded_request_head]
  exact RequestFraming.head_boundary _ _
    (request_rows_no_cr request method target valid _ (by simp))
    (by intro row hr; exact request_rows_no_cr request method target valid row (by simp [hr]))
    (request_rows_nonempty request)

theorem request_head_lines (request : Request) (method : request.method = "GET")
    (target : ∀ c ∈ request.target.toList, 32 < c.toNat ∧ c.toNat ≠ 127)
    (valid : (retainedHeaders request).all Header.valid = true) :
    (requestHeadText request).splitOn "\r\n" =
      (request.method ++ " " ++ request.target ++ " HTTP/1.1") :: requestHeaderRows request :=
  HTTPStrings.split_crlf_join _ (request_rows_no_cr request method target valid) (by simp)

def decodedRequestHeaders (request : Request) : Headers :=
  (retainedHeaders request).map reparsedHeader ++
    #[⟨"Host", "127.0.0.1:8081"⟩, ⟨"Content-Length", toString request.body.size⟩, ⟨"Connection", "close"⟩]

private theorem parsed_content_length_upper (n : Nat) :
    parseHeader ("Content-Length: " ++ toString n) = .ok ⟨"Content-Length", toString n⟩ := by
  have valid : (Header.mk "Content-Length" (toString n)).valid = true := by
    exact Bool.and_eq_true_iff.mpr ⟨by change isToken "Content-Length" = true; native_decide,
      ServiceProofs.decimal_value_valid n⟩
  have parsed := parse_serialized_header ⟨"Content-Length", toString n⟩ valid
  have trimmed : (" " ++ toString n).trimAscii.toString = toString n := by
    apply trim_space_clean
    intro c hc
    have bounds := Proofv2.decimal_chars n c hc
    simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · constructor
      · constructor <;> (intro eq; subst c; contradiction)
      · intro eq; subst c; contradiction
    · intro eq; subst c; contradiction
  simpa only [reparsedHeader, trimmed] using parsed

section
local instance : DecidableEq Header := fun a b =>
  decidable_of_iff (a.name = b.name ∧ a.value = b.value) (by cases a; cases b; simp)
private theorem ok_of_toOption {ε α : Type} (r : Except ε α) (a : α) (h : r.toOption = some a) : r = .ok a := by
  cases r <;> simp_all [Except.toOption]

theorem request_header_parse (request : Request)
    (valid : (retainedHeaders request).all Header.valid = true) :
    (requestHeaderRows request).mapM parseHeader = .ok (decodedRequestHeaders request).toList := by
  have kept := parse_serialized_headers (retainedHeaders request).toList
    (by intro h hm; exact Array.all_eq_true_iff_forall_mem.mp valid h (by simpa using hm))
  have host : parseHeader "Host: 127.0.0.1:8081" = .ok ⟨"Host", "127.0.0.1:8081"⟩ :=
    ok_of_toOption _ _ (by native_decide)
  have conn : parseHeader "Connection: close" = .ok ⟨"Connection", "close"⟩ :=
    ok_of_toOption _ _ (by native_decide)
  simp only [requestHeaderRows, List.mapM_append, kept, List.mapM_cons, List.mapM_nil,
    host, conn, parsed_content_length_upper, bind, Except.bind, pure, Except.pure,
    decodedRequestHeaders, Array.toList_append, Array.toList_map]
end
private theorem getAll_append (a b : Headers) (name : String) :
    (a ++ b).getAll name = a.getAll name ++ b.getAll name := by
  simp [Headers.getAll, Array.filter_append, Array.map_append]

private theorem get_append_absent (a b : Headers) (name : String) (absent : a.getAll name = #[]) :
    (a ++ b).get? name = b.get? name := by
  have no : a.find? (fun h => headerName h.name == headerName name) = none := by
    apply Array.find?_eq_none.mpr
    intro h hm
    intro yes
    have mem : h.value ∈ a.getAll name :=
      Array.mem_map.mpr ⟨h, Array.mem_filter.mpr ⟨hm,yes⟩, rfl⟩
    rw [absent] at mem
    exact Array.not_mem_empty _ mem
  simp [Headers.get?, Array.find?_append, no]

theorem decoded_host (request : Request) :
    (decodedRequestHeaders request).getAll "host" = #["127.0.0.1:8081"] ∧
    (decodedRequestHeaders request).get? "host" = some "127.0.0.1:8081" := by
  have absent := reparsed_getAll (retainedHeaders request) "host"
    (retained_protocol_absent request "host" (Or.inl rfl))
  unfold decodedRequestHeaders
  rw [getAll_append, absent, get_append_absent _ _ _ absent]
  have host : headerName "Host" = "host" := by native_decide
  have lower : headerName "host" = "host" := by native_decide
  have length : headerName "Content-Length" = "content-length" := by native_decide
  have conn : headerName "Connection" = "connection" := by native_decide
  simp [Headers.getAll, Headers.get?, host, lower, length, conn]

theorem decoded_length (request : Request) :
    (decodedRequestHeaders request).getAll "content-length" = #[toString request.body.size] := by
  have absent := reparsed_getAll (retainedHeaders request) "content-length"
    (retained_protocol_absent request "content-length" (Or.inr (Or.inl rfl)))
  unfold decodedRequestHeaders
  rw [getAll_append, absent]
  have host : headerName "Host" = "host" := by native_decide
  have lower : headerName "content-length" = "content-length" := by native_decide
  have length : headerName "Content-Length" = "content-length" := by native_decide
  have conn : headerName "Connection" = "connection" := by native_decide
  simp [Headers.getAll, host, lower, length, conn]

theorem decoded_encoding (request : Request) :
    (decodedRequestHeaders request).getAll "transfer-encoding" = #[] := by
  have absent := reparsed_getAll (retainedHeaders request) "transfer-encoding"
    (retained_protocol_absent request "transfer-encoding" (Or.inr (Or.inr rfl)))
  unfold decodedRequestHeaders
  rw [getAll_append, absent]
  have host : headerName "Host" = "host" := by native_decide
  have lower : headerName "transfer-encoding" = "transfer-encoding" := by native_decide
  have length : headerName "Content-Length" = "content-length" := by native_decide
  have conn : headerName "Connection" = "connection" := by native_decide
  simp [Headers.getAll, host, lower, length, conn]
end FrontendBackend
