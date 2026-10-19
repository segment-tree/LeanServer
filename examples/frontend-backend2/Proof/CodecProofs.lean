import Proof.ForwardingProofs
import Proof.ByteFramingProofs
import Proof.RequestHeadProofs
import Proof.HTTPDecimalProofs

namespace FrontendBackend2

open LeanServer.HTTP

/-! Lemmas about the real HTTP codec. None assumes a codec contract. -/

theorem parsed_header_valid (line : String) (header : Header)
    (parsed : parseHeader line = .ok header) : header.valid = true := by
  unfold parseHeader at parsed
  simp only [bind, Except.bind, pure, Except.pure] at parsed
  split at parsed
  · contradiction
  · split at parsed
    · contradiction
    · have eq := Except.ok.inj parsed
      subst header
      cases h : Header.valid _ <;> simp_all

theorem parsed_headers_valid (lines : List String) (headers : List Header)
    (parsed : lines.mapM parseHeader = .ok headers) :
    ∀ h ∈ headers, h.valid = true := by
  induction lines generalizing headers with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at parsed
    subst headers
    simp
  | cons line lines ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at parsed
    cases first : parseHeader line with
    | error err => simp [first] at parsed
    | ok h =>
      cases tail : lines.mapM parseHeader with
      | error err => simp [first, tail] at parsed
      | ok hs =>
        simp only [first, tail, Except.ok.injEq] at parsed
        subst headers
        intro v mem
        rcases List.mem_cons.mp mem with eq | mem
        · subst v; exact parsed_header_valid line h first
        · exact ih hs tail v mem

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- Successful parsing, including the chunked branch, supplies the real parsed
header lines and the checks performed on the method and target. -/
theorem parsed_request_head (wire : ByteArray) (request : Request) (rest : ByteArray)
    (parsed : parseHTTP1 wire = .ok (some (request, rest))) :
    ∃ head : String,
      List.mapM parseHeader (head.splitOn "\r\n").tail! = .ok request.headers.toList ∧
      isToken request.method = true ∧ request.target.isEmpty = false ∧
      request.target.toList.any (fun c => c.toNat ≤ 32 || c.toNat == 127) = false := by
  unfold parseHTTP1 at parsed
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe] at parsed
  split at parsed
  next headerEnd hEnd =>
    split at parsed
    · contradiction
    · split at parsed
      next head hHead =>
        split at parsed
        next method target version hLine =>
          split at parsed
          · contradiction
          · rename_i hShape
            simp only [Bool.or_eq_true, Bool.not_eq_true, not_or] at hShape
            repeat' first
              | (solve | cases parsed)
              | (solve | cases Except.ok.inj parsed)
              | split at parsed
            all_goals
              have pair := Option.some.inj (Except.ok.inj parsed)
              have reqEq := congrArg Prod.fst pair
              cases reqEq
              refine ⟨head, ?_, ?_, ?_, ?_⟩
              · exact ‹List.mapM parseHeader _ = .ok _›
              · simpa using hShape.1.1
              · exact hShape.1.2
              · exact hShape.2
        next => contradiction
      next => contradiction
  next => split at parsed <;> simp_all only [Except.ok.injEq, reduceCtorEq]

theorem parsed_request_headers_valid (wire : ByteArray) (request : Request) (rest : ByteArray)
    (parsed : parseHTTP1 wire = .ok (some (request, rest))) :
    request.headers.all Header.valid = true := by
  obtain ⟨head, headers, _⟩ := parsed_request_head wire request rest parsed
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro h mem
  exact parsed_headers_valid _ _ headers h (by simpa using mem)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- Connects the returned method and target to the actual byte boundary and
UTF-8 head selected by the parser, rather than an independent request record. -/
theorem parsed_request_line (wire : ByteArray) (request : Request) (rest : ByteArray)
    (parsed : parseHTTP1 wire = .ok (some (request, rest))) :
    ∃ endPos head,
      findBytes wire "\r\n\r\n".toUTF8 = some endPos ∧
      String.fromUTF8? (wire.extract 0 endPos) = some head ∧
      (head.splitOn "\r\n").head!.splitOn " " = [request.method, request.target, "HTTP/1.1"] := by
  unfold parseHTTP1 at parsed
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe] at parsed
  split at parsed
  next headerEnd hEnd =>
    split at parsed
    · contradiction
    · split at parsed
      next head hHead =>
        split at parsed
        next method target version hLine =>
          split at parsed
          · contradiction
          · split at parsed
            · contradiction
            · rename_i versionOk
              have versionEq : version = "HTTP/1.1" := by simpa using versionOk
              repeat' first
                | (solve | cases parsed)
                | (solve | cases Except.ok.inj parsed)
                | split at parsed
              all_goals
                have pair := Option.some.inj (Except.ok.inj parsed)
                have reqEq := congrArg Prod.fst pair
                cases reqEq
                exact ⟨headerEnd, head, hEnd, hHead, versionEq ▸ hLine⟩
        next => contradiction
      next => contradiction
  next => split at parsed <;> simp_all only [Except.ok.injEq, reduceCtorEq]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- Once a complete non-chunked request parses, arbitrary equal-length body
replacement preserves every other parsed field. The header-boundary and initial
parse premises must still be proved when applying this lemma to an encoder. -/
theorem parseHTTP1_replace_body (head body replacement : ByteArray) (endPos : Nat) (request : Request)
    (found : findBytes head "\r\n\r\n".toUTF8 = some endPos)
    (boundary : endPos + 4 = head.size)
    (sameSize : replacement.size = body.size)
    (noChunks : request.headers.getAll "transfer-encoding" = #[])
    (parsed : parseHTTP1 (head ++ body) = .ok (some (request, ByteArray.empty))) :
    parseHTTP1 (head ++ replacement) =
      .ok (some ({request with body := replacement}, ByteArray.empty)) := by
  have endBound : endPos ≤ head.size := by omega
  have oldFound := findBytes_append_of_found head body _ 0 endPos found
  have newFound := findBytes_append_of_found head replacement _ 0 endPos found
  unfold parseHTTP1 at parsed ⊢
  rw [oldFound] at parsed
  rw [newFound]
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    extract_prefix _ _ _ _ endBound, ByteArray.size_append, sameSize] at parsed ⊢
  repeat' first
    | (solve | cases parsed)
    | (solve | cases Except.ok.inj parsed)
    | split at parsed
  all_goals
    have pair := Option.some.inj (Except.ok.inj parsed)
    have reqEq := congrArg Prod.fst pair
    have restEq := congrArg Prod.snd pair
    cases reqEq
    simp_all only [Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals
    have exhausted := ByteArray.extract_eq_empty_iff.mp restEq
    simp only [ByteArray.size_append, Nat.min_self] at exhausted
    congr 3
    · congr 1
      apply ByteArray.extract_append_eq_right rfl
      omega
    · apply ByteArray.extract_eq_empty_iff.mpr
      simp only [ByteArray.size_append]
      omega

theorem parsed_target_characters (wire : ByteArray) (request : Request) (rest : ByteArray)
    (parsed : parseHTTP1 wire = .ok (some (request, rest))) :
    ∀ c ∈ request.target.toList, 32 < c.toNat ∧ c.toNat ≠ 127 := by
  obtain ⟨_, _, _, _, chars⟩ := parsed_request_head wire request rest parsed
  intro c hc
  have notBad := (List.any_eq_false.mp chars) c hc
  simp at notBad
  omega

theorem utf8_roundtrip (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  split
  · rfl
  · exact False.elim (‹¬_› s.isValidUTF8)

theorem forwarded_headers_valid (wire : ByteArray) (request : Request) (rest : ByteArray)
    (parsed : parseHTTP1 wire = .ok (some (request, rest))) :
    (retainedHeaders (backendRequest request)).all Header.valid = true := by
  have original := parsed_request_headers_valid wire request rest parsed
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro h mem
  have retained := (Array.mem_filter.mp mem).1
  have beforeRewrite := (Array.mem_filter.mp retained).1
  exact Array.all_eq_true_iff_forall_mem.mp original h beforeRewrite

/-- The encoder preserves arbitrary body bytes, including non-UTF-8 bytes and
CRLF sequences. This extracts at the known encoder boundary; it does not prove
that parseHTTP1 finds that boundary. -/
theorem forwarded_body_bytes (addr : Upstream) (request : Request) :
    (encodeUpstreamRequest addr (backendRequest request)).extract
        (encodeUpstreamHead addr (backendRequest request)).size
        (encodeUpstreamRequest addr (backendRequest request)).size = request.body := by
  unfold encodeUpstreamRequest
  exact ByteArray.extract_append_eq_right rfl (by simp)

/-- Explicit parser result. Header normalization is represented, not hidden by
an equality between whole requests. -/
def decodedRequest (destination : ForwardDestination) (r : Request) : Request :=
  { method := "GET", target := r.target, headers := decodedRequestHeaders destination r,
    authority := some destination.authority, scheme := some "http", body := r.body }

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
/-- Codec theorem with independently proved syntax and size premises. These
premises are discharged from ResourceInput for both hops in TwoHopProofs. -/
theorem request_roundtrip (destination : ForwardDestination) (r : Request)
    (method : r.method = "GET")
    (targetNonempty : r.target.isEmpty = false)
    (targetGood : r.target.toList.any (fun c => c.toNat ≤ 32 || c.toNat == 127) = false)
    (valid : (retainedHeaders r).all Header.valid = true)
    (headBound : (encodeUpstreamHead destination.address r).size ≤ ({} : Limits).maxHeaderBytes)
    (bodyBoundInput : r.body.size ≤ ({} : Limits).maxBodyBytes) :
    parseHTTP1 (encodeUpstreamRequest destination.address r) =
      .ok (some (decodedRequest destination r, ByteArray.empty)) := by
  let head := encodeUpstreamHead destination.address r
  let endPos := (requestHeadText destination r).toUTF8.size
  have target : ∀ c ∈ r.target.toList, 32 < c.toNat ∧ c.toNat ≠ 127 := by
    intro c hc
    have h := List.any_eq_false.mp targetGood c hc
    simp at h
    omega
  have found : findBytes head "\r\n\r\n".toUTF8 = some endPos :=
    request_head_boundary destination r method target valid
  have boundary : endPos + 4 = head.size := by
    dsimp [head, endPos]
    rw [encoded_request_head destination]
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.size_append]
    rfl
  have foundWire := findBytes_append_of_found head r.body _ 0 endPos found
  have headLimit : ¬ endPos + 4 > ({} : Limits).maxHeaderBytes := by rw [boundary]; exact Nat.not_lt.mpr headBound
  have headText : (head ++ r.body).extract 0 endPos = (requestHeadText destination r).toUTF8 := by
    rw [extract_prefix _ _ _ _ (by omega)]
    dsimp [head,endPos]
    rw [encoded_request_head destination]
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append]
    exact ByteArray.extract_append_eq_left rfl
  have headLines := request_head_lines destination r method target valid
  have line := request_line_split r method target
  have headerParse := request_header_parse destination r valid
  have payload : (head ++ r.body).extract (endPos+4) (endPos+4+r.body.size) = r.body := by
    rw [boundary]
    exact ByteArray.extract_append_eq_right rfl rfl
  have exhausted : (head ++ r.body).extract (endPos+4+r.body.size) (head ++ r.body).size = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr
    rw [boundary, ByteArray.size_append]
    simp
  change parseHTTP1 (head ++ r.body) = _
  unfold parseHTTP1
  rw [foundWire]
  simp only [bind, Except.bind, pure, Except.pure, headLimit, ↓reduceIte]
  rw [headText, utf8_roundtrip]
  dsimp only
  rw [headLines]
  simp only [List.head!, List.tail!]
  rw [line]
  have getToken : isToken "GET" = true := by native_decide
  simp only [getToken, Bool.not_true, Bool.false_or]
  have targetNonemptyR : r.target.isEmpty = false := targetNonempty
  have targetGoodR : r.target.toList.any (fun c => c.toNat ≤ 32 || c.toNat == 127) = false := targetGood
  rw [targetNonemptyR, targetGoodR]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [headerParse]
  dsimp only
  simp only [Array.toArray_toList]
  rw [(decoded_host destination r).1, (decoded_host destination r).2, decoded_length destination, decoded_encoding destination]
  have hostCheck : (#[destination.authority].size != 1 || some destination.authority == some "") = false := by cases destination <;> native_decide
  rw [hostCheck]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have lengthSize : #[toString r.body.size].size = 1 := rfl
  have encodingSize : (#[] : Array String).size = 0 := rfl
  have lengthEmpty : #[toString r.body.size].isEmpty = false := by simp
  have encodingEmpty : (#[] : Array String).isEmpty = true := rfl
  simp only [lengthSize, encodingSize, lengthEmpty, encodingEmpty, Bool.not_true,
    Bool.not_false, Bool.true_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    show ¬ (1 > 1) from by omega, show ¬ (0 > 1) from by omega, decide_false]
  have lengthValue : #[toString r.body.size][0]! = toString r.body.size := by simp
  rw [lengthValue]
  rw [http_decimal_roundtrip]
  dsimp only
  have bodyBound : ¬ r.body.size > 10485760 := Nat.not_lt.mpr bodyBoundInput
  have complete : ¬ endPos+4+r.body.size > (head++r.body).size := by
    rw [boundary, ByteArray.size_append]
    omega
  rw [if_neg bodyBound, if_neg complete, payload, exhausted]
  rfl

/-- For a normal response, GET encoding appends exactly the application body
after the same header section emitted for HEAD. No decoder is assumed. -/
theorem response_body_bytes (r : Response) (close : Bool) (valid : r.valid = true)
    (not204 : r.status ≠ 204) (not304 : r.status ≠ 304) :
    (encodeHTTP1 r "GET" close).extract (encodeHTTP1 r "HEAD" close).size
      (encodeHTTP1 r "GET" close).size = r.body := by
  have wire : encodeHTTP1 r "GET" close = encodeHTTP1 r "HEAD" close ++ r.body := by
    simp [encodeHTTP1, valid, responseBody, not204, not304]
  rw [wire]
  exact ByteArray.extract_append_eq_right rfl (by simp)

end FrontendBackend2
