import BackendCore
import FrontendCore
import Proof.ServiceProofs
import Proof.CodecProofs
import Proof.ResponseHeadProofs

namespace FrontendBackend.Proofv2

open LeanServer.HTTP

/-- A strict pure observer for one complete Content-Length HTTP/1.1 response.
It is a specification observer, not the private IO readBackendResponse function. -/
def decodeResponse (wire : ByteArray) : Option Response := do
  let headEnd ← findBytes wire "\r\n\r\n".toUTF8
  let head ← String.fromUTF8? (wire.extract 0 headEnd)
  let lines := head.splitOn "\r\n"
  let parts := lines.head!.splitOn " "
  if parts.head! != "HTTP/1.1" then none else do
    let status ← parts[1]?.bind String.toNat?
    if status > 999 then none else do
      let headers ← (lines.tail!.mapM fun line => (parseHeader line).toOption)
      let headers : Headers := headers.toArray
      let lengthText ← headers.get? "content-length"
      let length ← lengthText.toNat?
      if headEnd + 4 + length != wire.size then none else
        some { status := status.toUInt16, headers
               body := wire.extract (headEnd + 4) wire.size }

/-- The Response reconstructed from this encoder's wire representation, including
framing headers. This is not generally equal to the original application Response. -/
def wireResponse (r : Response) (close : Bool) : Response :=
  let r := if r.valid then r else Response.text "Internal Server Error" 500
  { status := r.status
    headers := (responseHeaders r).push
      ⟨"Connection", if close then "close" else "keep-alive"⟩
    body := responseBody "GET" r }

/-- Encoding normalizes invalid responses and adds only valid framing headers.
This is a property of the code, independent of every exchange contract. -/
theorem wire_response_valid (r : Response) (close : Bool) :
    (wireResponse r close).valid = true := by
  have connection : (Header.mk "Connection" (if close then "close" else "keep-alive")).valid = true := by
    cases close <;> decide
  have normalized : (if r.valid then r else Response.text "Internal Server Error" 500).valid = true := by
    split
    · assumption
    · native_decide
  have headers := ServiceProofs.response_headers_valid _ normalized
  have status := (Bool.and_eq_true_iff.mp normalized).1
  change ((_ >= 200 && _ <= 599) &&
    ((responseHeaders (if r.valid then r else Response.text "Internal Server Error" 500)).push
      ⟨"Connection", if close then "close" else "keep-alive"⟩).all Header.valid) = true
  rw [Array.all_push, connection, headers, Bool.true_and, Bool.and_true]
  exact status

/-- The real observer's status and headers depend only on the head and body
length. Arbitrary equal-length payload replacement changes only the body.
This is a framing lemma, not an assumed encoder/decoder roundtrip. -/
theorem decodeResponse_replace_body (head body replacement : ByteArray) (endPos : Nat)
    (found : findBytes head "\r\n\r\n".toUTF8 = some endPos)
    (boundary : endPos + 4 = head.size)
    (sameSize : replacement.size = body.size) :
    decodeResponse (head ++ replacement) =
      (decodeResponse (head ++ body)).map (fun r => {r with body := replacement}) := by
  have endBound : endPos ≤ head.size := by omega
  have oldFound := findBytes_append_of_found head body _ 0 endPos found
  have newFound := findBytes_append_of_found head replacement _ 0 endPos found
  unfold decodeResponse
  rw [oldFound, newFound]
  simp only [bind, Option.bind, extract_prefix _ _ _ _ endBound,
    ByteArray.size_append, sameSize]
  have payload : (head ++ replacement).extract (endPos + 4) (head.size + body.size) = replacement := by
    rw [boundary, ← sameSize]
    exact ByteArray.extract_append_eq_right rfl rfl
  rw [payload]
  repeat' first | rfl | (simp_all only [Option.map_none]) | split

section

local instance : DecidableEq Header := fun a b =>
  decidable_of_iff (a.name = b.name ∧ a.value = b.value) (by cases a; cases b; simp)
local instance : DecidableEq Response := fun a b =>
  decidable_of_iff (a.status = b.status ∧ a.headers = b.headers ∧ a.body = b.body)
    (by cases a; cases b; simp)

/-- Complete roundtrip for the fixed rejection response, for both connection
modes. No codec assumption supplies this equality. -/
theorem unauthorized_roundtrip (close : Bool) :
    decodeResponse (encodeHTTP1 unauthorizedResponse "GET" close) =
      some (wireResponse unauthorizedResponse close) := by
  cases close <;> native_decide

end

theorem resource_valid (target : String) : (resource target).valid = true := by
  simp [Response.valid, resource, Response.json, Header.valid, isToken]
  constructor <;> native_decide

section

local instance : DecidableEq Header := fun a b =>
  decidable_of_iff (a.name = b.name ∧ a.value = b.value) (by cases a; cases b; simp)

/-- Decode the explicit JSON response frame, preserving an arbitrary byte payload. -/
theorem decode_json_frame (body : ByteArray) (close : Bool) :
    decodeResponse ((jsonResponseHead body.size close ++ "\r\n\r\n").toUTF8 ++ body) =
      some { status := 200
             headers := #[⟨"content-type", "application/json"⟩, ⟨"content-length", toString body.size⟩,
               ⟨"Connection", if close then "close" else "keep-alive"⟩], body := body } := by
  let h := jsonResponseHead body.size close
  have boundary := json_head_boundary body.size close
  have found := findBytes_append_of_found (h ++ "\r\n\r\n").toUTF8 body "\r\n\r\n".toUTF8 0 h.toUTF8.size boundary
  have head : ((h ++ "\r\n\r\n").toUTF8 ++ body).extract 0 h.toUTF8.size = h.toUTF8 := by
    simp only [String.toUTF8, String.toByteArray_append]
    rw [extract_prefix _ _ _ _ (by simp), ByteArray.extract_append_eq_left rfl]
  have size : (h ++ "\r\n\r\n").toUTF8.size = h.toUTF8.size + 4 := by
    simp only [String.toUTF8, String.toByteArray_append, ByteArray.size_append]
    rfl
  have payload : ((h ++ "\r\n\r\n").toUTF8 ++ body).extract (h.toUTF8.size+4)
      ((h ++ "\r\n\r\n").toUTF8 ++ body).size = body :=
    ByteArray.extract_append_eq_right size.symm (by simp)
  unfold decodeResponse
  rw [found]
  simp only [bind, Option.bind]
  rw [head, utf8_roundtrip]
  dsimp only
  rw [json_head_lines]
  have ct : (parseHeader "content-type: application/json").toOption = some ⟨"content-type", "application/json"⟩ := by native_decide
  have connection : (parseHeader ("Connection: " ++ (if close then "close" else "keep-alive"))).toOption =
      some ⟨"Connection", if close then "close" else "keep-alive"⟩ := by cases close <;> native_decide
  have statusLine : "HTTP/1.1 200 ".splitOn " " = ["HTTP/1.1", "200", ""] := by native_decide
  simp only [List.head!, List.tail!, statusLine]
  simp only [List.mapM_cons, List.mapM_nil]
  rw [ct, connection, parse_content_length]
  simp only [Except.toOption, bind, Option.bind, pure]
  have status : "200".toNat? = some 200 := by native_decide
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_succ,
    List.getElem?_cons_zero, status]
  have lookup : Headers.get? #[⟨"content-type", "application/json"⟩,
      ⟨"content-length", toString body.size⟩, ⟨"Connection", if close then "close" else "keep-alive"⟩]
      "content-length" = some (toString body.size) := by
    have ctName : headerName "content-type" = "content-type" := by native_decide
    have clName : headerName "content-length" = "content-length" := by native_decide
    simp [Headers.get?, ctName, clName]
  rw [lookup]
  simp only [decimal_roundtrip]
  rw [payload]
  simp only [ByteArray.size_append]
  rw [size]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, show ¬ 200 > 999 from by decide]
  rfl
end

/-- Actual encoder/observer roundtrip for status 200, the JSON content type, and
arbitrary binary payload. The observer imposes no body-size limit; this does not
verify the IO reader's 1 MiB limit or require any property of Json.compress. -/
theorem json_response_roundtrip (body : ByteArray) (close : Bool) :
    let response : Response :=
      { status := 200, headers := #[⟨"content-type", "application/json"⟩], body }
    decodeResponse (encodeHTTP1 response "GET" close) =
      some (wireResponse response close) := by
  dsimp only
  let response : Response := { status := 200, headers := #[⟨"content-type", "application/json"⟩], body }
  have valid : response.valid = true := by
    change (Response.valid {status := 200, headers := #[⟨"content-type", "application/json"⟩], body := ByteArray.empty}) = true
    native_decide
  have headers : responseHeaders response =
      #[⟨"content-type", "application/json"⟩, ⟨"content-length", toString body.size⟩] := by
    have name : headerName "content-type" = "content-type" := by native_decide
    simp [responseHeaders, response, name]
  have encoded : encodeHTTP1 response "GET" close =
      (jsonResponseHead body.size close ++ "\r\n\r\n").toUTF8 ++ body := by
    unfold encodeHTTP1
    simp only [if_pos valid, headers]
    have statusText : toString (200 : UInt16) = "200" := by native_decide
    simp only [response, responseBody]
    simp only [show ("GET" == "HEAD") = false from rfl,
      show ((200 : UInt16) == 204) = false from rfl,
      show ((200 : UInt16) == 304) = false from rfl, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    congr 1
    congr 1
    change ("HTTP/1.1 " ++ toString (200 : UInt16) ++ " \r\n" ++
      ("" ++ "content-type" ++ ": " ++ "application/json" ++ "\r\n" ++
        "content-length" ++ ": " ++ toString body.size ++ "\r\n") ++
      "Connection: " ++ (if close then "close" else "keep-alive") ++ "\r\n\r\n") = _
    rw [statusText]
    simp only [jsonResponseHead, String.append_assoc]
    rfl
  change decodeResponse (encodeHTTP1 response "GET" close) = some (wireResponse response close)
  rw [encoded, decode_json_frame]
  congr 1
  unfold wireResponse
  simp only [if_pos valid, headers]
  rfl

theorem resource_roundtrip (target : String) (close : Bool) :
    decodeResponse (encodeHTTP1 (resource target) "GET" close) =
      some (wireResponse (resource target) close) :=
  json_response_roundtrip (resource target).body close

/-- Rebuilding framing headers twice is the same as rebuilding them once. -/
theorem responseHeaders_wire (r : Response) (upstreamClose : Bool)
    (valid : r.valid = true) (not204 : r.status ≠ 204) (not304 : r.status ≠ 304) :
    responseHeaders (wireResponse r upstreamClose) = responseHeaders r := by
  have connection : headerName "Connection" = "connection" := by native_decide
  have length : headerName "content-length" = "content-length" := by native_decide
  simp [wireResponse, valid, responseBody, not204, not304, responseHeaders,
    Array.filter_filter, connection, length]

theorem wireResponse_wire (r : Response) (upstreamClose close : Bool)
    (valid : r.valid = true) (not204 : r.status ≠ 204) (not304 : r.status ≠ 304) :
    wireResponse (wireResponse r upstreamClose) close = wireResponse r close := by
  have headers := responseHeaders_wire r upstreamClose valid not204 not304
  have wireValid := wire_response_valid r upstreamClose
  rw [wireResponse, if_pos wireValid, headers]
  simp [wireResponse, valid, responseBody, not204, not304]

/-- Forwarding an already framed response reuses exactly the same GET bytes
for the client's connection mode. This is proved without any roundtrip lemma. -/
theorem encodeHTTP1_wire (r : Response) (upstreamClose close : Bool)
    (valid : r.valid = true) (not204 : r.status ≠ 204) (not304 : r.status ≠ 304) :
    encodeHTTP1 (wireResponse r upstreamClose) "GET" close = encodeHTTP1 r "GET" close := by
  have headers := responseHeaders_wire r upstreamClose valid not204 not304
  have wireValid := wire_response_valid r upstreamClose
  unfold encodeHTTP1
  simp only [wireValid, valid, ↓reduceIte, headers]
  simp [wireResponse, valid, responseBody, not204, not304]

theorem forwarded_resource_roundtrip (target : String) (close : Bool) :
    decodeResponse (encodeHTTP1 (wireResponse (resource target) true) "GET" close) =
      some (wireResponse (wireResponse (resource target) true) close) := by
  have not204 : (resource target).status ≠ 204 := by change (200 : UInt16) ≠ 204; decide
  have not304 : (resource target).status ≠ 304 := by change (200 : UInt16) ≠ 304; decide
  rw [encodeHTTP1_wire _ _ _ (resource_valid target) not204 not304,
    wireResponse_wire _ _ _ (resource_valid target) not204 not304]
  exact resource_roundtrip target close

structure ResponseView where
  status : UInt16
  body : ByteArray

def view (r : Response) : ResponseView := ⟨r.status, r.body⟩

theorem unauthorized_valid : unauthorizedResponse.valid = true := by
  native_decide

theorem view_wire (r : Response) (close : Bool)
    (valid : r.valid = true) (not204 : r.status ≠ 204) (not304 : r.status ≠ 304) :
    view (wireResponse r close) = view r := by
  simp only [wireResponse, valid, ↓reduceIte, view]
  simp [responseBody, not204, not304]

theorem wire_resource_status (target : String) :
    (wireResponse (resource target) true).status = 200 := by
  simp only [wireResponse, resource_valid, ↓reduceIte]
  rfl

end FrontendBackend.Proofv2
