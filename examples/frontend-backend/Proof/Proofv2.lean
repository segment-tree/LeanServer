import Proof.ApplicationExchange
import FrontendCore
import BackendCore
import Proof.ServiceProofs
import Proof.ForwardingProofs
import Proof.CodecProofs
import Proof.DecimalProofs
import Proof.ResponseHeadProofs

namespace FrontendBackend.Proofv2

open LeanServer.HTTP

/-! Conditional HTTP/1.1 exchange proof. Data lives in Type; assumptions live in
Prop. None of the contracts below verifies opaque IO, C, or the OS. -/

open ExchangeGraph (SendCall bytes written ConnectionExchange Requests Replies StableTransport)

def context (e : Exchange) : Context :=
  Context.ofRequest e.request { peerAddress := some e.sourceIP }

/-- The backend input is computed from received bytes, never independently recorded. -/
def backendInput (e : Exchange) (u : e.EdgeId) : Except RequestError (Option (Request × ByteArray)) :=
  parseHTTP1 (bytes (e.upstream u).connection.requestReads)

/-- An incomplete or invalid request does not invoke the handler in this model. -/
def backendResponse (e : Exchange) (u : e.EdgeId) : Option Response :=
  match backendInput e u with
  | .ok (some (request, _)) => some (backendCore (m := Id) (Context.ofRequest request))
  | _ => none

/-- The bytes produced by parsing, running the backend handler, and encoding.
No output is specified for an incomplete or invalid input. -/
def backendReplyBytes (close : Bool) (input : ByteArray) : Option ByteArray :=
  match parseHTTP1 input with
  | .ok (some (request, _)) =>
    some (encodeHTTP1 (backendCore (m := Id) (Context.ofRequest request)) request.method close)
  | _ => none

def backendOutput (e : Exchange) (u : e.EdgeId) : Option ByteArray :=
  backendReplyBytes (e.upstream u).responseClose (bytes (e.upstream u).connection.requestReads)

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

def childResult (e : Exchange) (edge : e.EdgeId) : UpstreamResult :=
  match (e.children edge).head? with
  | none => .failure "no upstream exchange"
  | some u => match decodeResponse (bytes (e.upstream u).connection.responseReads) with
    | some response => .success response
    | none => .failure "invalid upstream response"

def upstreamResult (e : Exchange) : UpstreamResult := childResult e e.entry

/-- IO correspondence below binds this one-call replay to the configured address
and encoded request. It is not a general replacement for requestUpstreamIO. -/
def frontendResponse (e : Exchange) : Response :=
  (ServiceProofs.runFrontend (upstreamResult e) (context e)).1

/-- Calls are produced by frontend execution, not supplied independently in the trace. -/
def frontendCalls (e : Exchange) : List ForwardCall :=
  (ServiceProofs.runFrontend (upstreamResult e) (context e)).2

/-- Every execution either makes no call or calls the configured backend once.
This follows from the frontend code, without any exchange contract. -/
theorem frontend_calls_cases (e : Exchange) :
    frontendCalls e = [] ∨
      frontendCalls e = [{ upstream := backendAddr, request := backendRequest e.request }] := by
  by_cases login : (context e).path = "/login"
  · exact Or.inl (ServiceProofs.frontend_login_no_call _ _ login)
  · cases auth : credentialsMatch (context e) with
    | false =>
      left
      unfold frontendCalls
      rw [ServiceProofs.frontend_rejected_no_call _ _ login auth]
    | true => exact Or.inr (ServiceProofs.frontend_authorized_call _ _ login auth)

theorem frontend_calls_length_le_one (e : Exchange) : (frontendCalls e).length ≤ 1 := by
  rcases frontend_calls_cases e with empty | one <;> simp [*]

/-- This frontend issues at most one call; encode the calls produced by its execution. -/
def upstreamRequestBytes (e : Exchange) : ByteArray :=
  bytes ((frontendCalls e).map fun call => encodeUpstreamRequest call.upstream call.request)

/-- Parse received client bytes, replay the frontend with this exchange's
upstream result, and encode its response. No output is specified on parse failure. -/
def frontendReplyAt (e : Exchange) (edge : e.EdgeId) (input : ByteArray) : Option ByteArray :=
  match parseHTTP1 input with
  | .ok (some (request, _)) =>
    let ctx := Context.ofRequest request { peerAddress := some (e.upstream edge).sourceIP }
    let response := (ServiceProofs.runFrontend (childResult e edge) ctx).1
    some (encodeHTTP1 response request.method (e.upstream edge).responseClose)
  | _ => none

def frontendReplyBytes (e : Exchange) : ByteArray → Option ByteArray :=
  frontendReplyAt e e.entry

/-- Select the actual program at this edge's receiving node, with that edge's
own request and child result. This application's frontend issues at most one call. -/
def replyBytes (e : Exchange) (edge : e.EdgeId) : ByteArray → Option ByteArray :=
  match (e.nodes (e.upstream edge).callee).program with
  | .client => fun _ => none
  | .frontend => frontendReplyAt e edge
  | .backend => backendReplyBytes (e.upstream edge).responseClose

/-- Under the existing client parse condition, the common Replies contract
is equivalent to the former frontend send equality. No extra premise is needed. -/
theorem frontend_reply_iff (e : Exchange)
    (parsed : parseHTTP1 (bytes e.client.requestReads) =
      .ok (some (e.request, ByteArray.empty))) :
    Replies e.client (frontendReplyBytes e) ↔
      written e.client.responseSends =
        encodeHTTP1 (frontendResponse e) e.request.method e.clientClose := by
  have output : frontendReplyBytes e (bytes e.client.requestReads) =
      some (encodeHTTP1 (frontendResponse e) e.request.method e.clientClose) := by
    unfold frontendReplyBytes frontendReplyAt
    rw [parsed]
    rfl
  constructor
  · intro replies
    exact replies.sent _ output
  · intro sent
    refine ⟨?_⟩
    intro response computed
    rw [output] at computed
    exact sent.trans (Option.some.inj computed)

structure TransportContracts (e : Exchange) : Prop where
  edges : ∀ edge, StableTransport (e.upstream edge).connection

def TransportContracts.client {e : Exchange} (transport : TransportContracts e) :
    StableTransport e.client := transport.edges e.entry

def TransportContracts.upstream {e : Exchange} (transport : TransportContracts e)
    (u : e.EdgeId) (_present : e.backendEdge = some u) :
    StableTransport (e.upstream u).connection := transport.edges u

/-- Runtime assumptions bind recorded bytes to the actual pure encoders/handlers.
They do not assume a resource result, or credential/resource equivalence. -/
structure RuntimeCorrespondence (e : Exchange) : Prop where
  clientParsed : parseHTTP1 (bytes e.client.requestReads) =
    .ok (some (e.request, ByteArray.empty))
  /-- Per-call sending correspondence already fixes the number and order of
  child edges. Target agreement is proved for the constructed application graph. -/
  upstreamRequest : ExchangeGraph.Aligned (fun edge call =>
      Requests (e.upstream edge).connection [call])
    (e.children e.entry) (frontendCalls e)
  /-- Send correspondence only. Successful parsing and the output bytes are
  derived from backendInput and backendOutput, not assumed by this condition. -/
  replies : ∀ edge, Replies (e.upstream edge).connection (replyBytes e edge)

def RuntimeCorrespondence.frontendReply {e : Exchange} (runtime : RuntimeCorrespondence e)
    (topology : FrontendBackendTopology e) : Replies e.client (frontendReplyBytes e) := by
  have replies := runtime.replies e.entry
  simpa [replyBytes, topology.entryCallee, Exchange.client, frontendReplyBytes] using replies

def RuntimeCorrespondence.backendReply {e : Exchange} (runtime : RuntimeCorrespondence e)
    (topology : FrontendBackendTopology e) (u : e.EdgeId) (ne : u ≠ e.entry) :
    Replies (e.upstream u).connection (backendReplyBytes (e.upstream u).responseClose) := by
  have replies := runtime.replies u
  simpa [replyBytes, (topology.backend u ne).2.1] using replies

/-- The actual frontend makes at most one call, so its graph children equal
the optional convenience view. No one-child restriction is built into the graph. -/
theorem frontend_children (e : Exchange) (runtime : RuntimeCorrespondence e) :
    e.children e.entry = e.backendEdge.toList := by
  have count := runtime.upstreamRequest.length_eq
  have bound := frontend_calls_length_le_one e
  unfold Exchange.backendEdge
  cases children : e.children e.entry with
  | nil => rfl
  | cons u tail =>
    cases tail with
    | nil => rfl
    | cons v rest =>
      rw [children] at count
      simp only [List.length_cons] at count
      omega

theorem RuntimeCorrespondence.callCount {e : Exchange} (runtime : RuntimeCorrespondence e) :
    e.backendEdge.toList.length = (frontendCalls e).length := by
  rw [← frontend_children e runtime]
  exact runtime.upstreamRequest.length_eq

theorem backend_edge_ne_entry (e : Exchange) (u : e.EdgeId)
    (present : e.backendEdge = some u) : u ≠ e.entry := by
  have member : u ∈ e.children e.entry := by
    unfold Exchange.backendEdge at present
    cases children : e.children e.entry with
    | nil => simp [children] at present
    | cons head tail =>
      simp only [children, List.head?_cons, Option.some.injEq] at present
      subst head
      simp
  have parent := (e.childrenParent e.entry u).mp member
  intro same
  rw [same, e.entryRoot] at parent
  contradiction

/-- The former callsMatch field is derived: ordered request correspondence
supplies the edges, the frontend code fixes call targets, and construction fixes
callee addresses. No separate topology, parsing, or transport premise is needed. -/
theorem application_calls_match (input : ApplicationInput)
    (runtime : RuntimeCorrespondence input.exchange) :
    ExchangeGraph.Aligned (fun edge call =>
      (input.exchange.nodes (input.exchange.upstream edge).callee).address = some call.upstream)
      (input.exchange.children input.exchange.entry) (frontendCalls input.exchange) := by
  have requests := runtime.upstreamRequest
  rcases frontend_calls_cases input.exchange with empty | one
  · rw [empty] at requests ⊢
    cases children : input.exchange.children input.exchange.entry with
    | nil => exact .nil
    | cons u tail =>
      have count := requests.length_eq
      simp [children] at count
  · rw [one] at requests ⊢
    cases children : input.exchange.children input.exchange.entry with
    | nil =>
      rw [children] at requests
      cases requests
    | cons u tail =>
      rw [children] at requests
      cases requests with
      | cons _ rest =>
        cases rest
        apply ExchangeGraph.Aligned.cons ?_ .nil
        have present : input.exchange.backendEdge = some u := by
          simp [Exchange.backendEdge, children]
        exact (input.topology.backend u (backend_edge_ne_entry input.exchange u present)).2.2.1

/-- Specialize the ordered per-call Requests to this frontend's sole child. -/
theorem upstream_request_sent (e : Exchange) (runtime : RuntimeCorrespondence e)
    (u : e.EdgeId) (present : e.backendEdge = some u) :
    written (e.upstream u).connection.requestSends = upstreamRequestBytes e := by
  have requests := runtime.upstreamRequest
  rw [frontend_children e runtime, present] at requests
  cases calls : frontendCalls e with
  | nil =>
    rw [calls] at requests
    cases requests
  | cons call tail =>
    rw [calls] at requests
    cases requests with
    | cons head rest =>
      cases rest with
      | nil =>
        simpa [upstreamRequestBytes, calls, bytes] using head.sent

/-- Recover the frontend send equality using only existing runtime fields. -/
theorem frontend_reply_sent (e : Exchange) (runtime : RuntimeCorrespondence e)
    (topology : FrontendBackendTopology e) :
    written e.client.responseSends =
      encodeHTTP1 (frontendResponse e) e.request.method e.clientClose :=
  (frontend_reply_iff e runtime.clientParsed).mp (runtime.frontendReply topology)

/-- Bundling reduces theorem arguments, not the number of trusted obligations. -/
structure Contracts (e : Exchange) : Prop where
  transport : TransportContracts e
  runtime : RuntimeCorrespondence e

/-- Under this application's topology and execution, the graph has no hidden
interactions beyond the entry and the computed optional backend call. -/
theorem exchange_edges (e : Exchange) (contracts : Contracts e)
    (topology : FrontendBackendTopology e) (edge : e.EdgeId) :
    edge = e.entry ∨ e.backendEdge = some edge := by
  by_cases same : edge = e.entry
  · exact Or.inl same
  · right
    have parent := (topology.backend edge same).1
    have member := (e.childrenParent e.entry edge).mpr parent
    rw [frontend_children e contracts.runtime] at member
    cases present : e.backendEdge with
    | none => simp [present] at member
    | some u =>
      simp only [present, Option.toList_some, List.mem_singleton] at member
      subst edge
      rfl

/-- Query strings are allowed. Forwarding constraints apply to the original
parsed request. CodecProofs proves the resulting encoded size limits, complete
forwarded parsing, and method/target/body preservation. -/
structure ResourceRequest (e : Exchange) : Prop where
  method : e.request.method = "GET"
  path : (context e).path = "/resource"
  forwardingConstraint : ForwardingConstraint e.request

structure ResponseView where
  status : UInt16
  body : ByteArray

def view (r : Response) : ResponseView := ⟨r.status, r.body⟩

def observed (e : Exchange) : Option ResponseView :=
  (decodeResponse (bytes e.client.responseReads)).map view

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

/-- The actual frontend code determines the address and rewritten request. -/
theorem frontend_authorized_calls (e : Exchange)
    (hRequest : ResourceRequest e)
    (authorized : credentialsMatch (context e) = true) :
    frontendCalls e = [{ upstream := backendAddr, request := backendRequest e.request }] := by
  have notLogin : (context e).path ≠ "/login" := by rw [hRequest.path]; decide
  exact ServiceProofs.frontend_authorized_call _ _ notLogin authorized

theorem authorized_call (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (authorized : credentialsMatch (context e) = true) :
    ∃ u, e.backendEdge = some u := by
  have count := contracts.runtime.callCount
  rw [frontend_authorized_calls e hRequest authorized] at count
  cases present : e.backendEdge with
  | none => simp [present] at count
  | some u => exact ⟨u, rfl⟩

theorem rejected_no_call (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (rejected : credentialsMatch (context e) = false) : e.backendEdge = none := by
  have notLogin : (context e).path ≠ "/login" := by rw [hRequest.path]; decide
  have calls : frontendCalls e = [] := by
    unfold frontendCalls
    rw [ServiceProofs.frontend_rejected_no_call _ _ notLogin rejected]
  have count := contracts.runtime.callCount
  rw [calls] at count
  cases present : e.backendEdge with
  | none => rfl
  | some u => simp [present] at count

theorem present_call (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u) :
    frontendCalls e = [{ upstream := backendAddr, request := backendRequest e.request }] := by
  cases auth : credentialsMatch (context e) with
  | false =>
    have absent := rejected_no_call e contracts hRequest auth
    rw [present] at absent
    contradiction
  | true => exact frontend_authorized_calls e hRequest auth

/-- Request bytes are calculated from the call produced by the frontend code. -/
theorem upstream_request_bytes (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u) :
    upstreamRequestBytes e = encodeUpstreamRequest backendAddr (backendRequest e.request) := by
  unfold upstreamRequestBytes
  rw [present_call e contracts hRequest u present]
  simp [bytes]

theorem client_request_delivered (e : Exchange) (contracts : Contracts e) :
    parseHTTP1 (written e.client.requestSends) =
      .ok (some (e.request, ByteArray.empty)) := by
  rw [← contracts.transport.client.received]
  exact contracts.runtime.clientParsed

/-- Pure size guarantees, derived from the input constraints rather than assumed. -/
theorem backend_request_size_limits (e : Exchange)
    (hRequest : ResourceRequest e) :
    (encodeUpstreamHead backendAddr (backendRequest e.request)).size ≤ ({} : Limits).maxHeaderBytes ∧
    (backendRequest e.request).body.size ≤ ({} : Limits).maxBodyBytes :=
  forwarded_size_limits e.request hRequest.forwardingConstraint hRequest.method

/-- The same bound holds for the bytes actually delivered to the backend.
Only transport and runtime fields are used, not the codec assumptions. -/
theorem backend_received_size (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u) :
    (bytes (e.upstream u).connection.requestReads).size ≤ 57680 + e.request.body.size := by
  rw [(contracts.transport.upstream u present).received,
    upstream_request_sent e contracts.runtime u present, upstream_request_bytes e contracts hRequest u present]
  exact forwarded_request_size e.request hRequest.forwardingConstraint hRequest.method

/-- Delivered request bytes contain the original body at the encoder's boundary.
This does not claim that the backend parser discovers that boundary. -/
theorem backend_received_body (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u) :
    (bytes (e.upstream u).connection.requestReads).extract
      (encodeUpstreamHead backendAddr (backendRequest e.request)).size
      (bytes (e.upstream u).connection.requestReads).size = e.request.body := by
  rw [(contracts.transport.upstream u present).received,
    upstream_request_sent e contracts.runtime u present, upstream_request_bytes e contracts hRequest u present]
  exact forwarded_body_bytes backendAddr e.request

/-- Transport and the forwarding codec derive the complete backend parse and
field preservation together. No runtime assumption asserts parsing success. -/
theorem backend_request_delivered (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u) :
    ∃ request : Request,
      backendInput e u = .ok (some (request, ByteArray.empty)) ∧
      request.method = e.request.method ∧
      request.target = e.request.target ∧
      request.body = e.request.body := by
  obtain ⟨request, parsed, fields⟩ := forwarded_request_roundtrip
    (bytes e.client.requestReads) e.request ByteArray.empty
    contracts.runtime.clientParsed hRequest.forwardingConstraint hRequest.method
  refine ⟨request, ?_, fields⟩
  unfold backendInput
  rw [(contracts.transport.upstream u present).received,
    upstream_request_sent e contracts.runtime u present,
    upstream_request_bytes e contracts hRequest u present]
  exact parsed

/-- For every result of the backend's actual parse, the forwarded fields agree
with the original request. Parser determinism also proves complete consumption. -/
theorem backend_decoded_fields (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u)
    (request : Request) (rest : ByteArray)
    (parsed : backendInput e u = .ok (some (request, rest))) :
    request.method = e.request.method ∧
      request.target = e.request.target ∧
      request.body = e.request.body ∧ rest = ByteArray.empty := by
  obtain ⟨forwarded, decoded, fields⟩ := backend_request_delivered e contracts hRequest u present
  rw [parsed] at decoded
  have pair := Option.some.inj (Except.ok.inj decoded)
  have reqEq := congrArg Prod.fst pair
  have restEq := congrArg Prod.snd pair
  cases reqEq
  exact ⟨fields.1, fields.2.1, fields.2.2, restEq⟩

private theorem backend_handler_resource (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u)
    (request : Request) (rest : ByteArray)
    (parsed : backendInput e u = .ok (some (request, rest))) :
    backendCore (m := Id) (Context.ofRequest request) = resource e.request.target := by
  have fields := backend_decoded_fields e contracts hRequest u present request rest parsed
  have hm := fields.1.trans hRequest.method
  have ht := fields.2.1
  have hp : (Context.ofRequest request).path = "/resource" := by
    change (request.target.splitOn "?").head! = "/resource"
    rw [ht]
    exact hRequest.path
  have hm' : (Context.ofRequest request).request.method = "GET" := hm
  have ht' : (Context.ofRequest request).request.target = e.request.target := ht
  simp [backendCore, hp, hm', ht']
  rfl

theorem backend_serves_resource (e : Exchange) (contracts : Contracts e)
    (hRequest : ResourceRequest e)
    (u : e.EdgeId) (present : e.backendEdge = some u) :
    backendResponse e u = some (resource e.request.target) := by
  obtain ⟨request, parsed, _⟩ := backend_request_delivered e contracts hRequest u present
  unfold backendResponse
  rw [parsed]
  exact congrArg some (backend_handler_resource e contracts hRequest u present request _ parsed)

theorem upstream_returns_resource (e : Exchange) (contracts : Contracts e)
    (topology : FrontendBackendTopology e)
    (hRequest : ResourceRequest e)
    (authorized : credentialsMatch (context e) = true) :
    upstreamResult e = .success (wireResponse (resource e.request.target) true) := by
  obtain ⟨u, present⟩ := authorized_call e contracts hRequest authorized
  obtain ⟨request, parsed, fields⟩ := backend_request_delivered e contracts hRequest u present
  have methodEq := fields.1.trans hRequest.method
  have handler := backend_handler_resource e contracts hRequest u present request _ parsed
  have output : backendOutput e u = some (encodeHTTP1 (resource e.request.target) "GET" true) := by
    have close := (topology.backend u (backend_edge_ne_entry e u present)).2.2.2
    change parseHTTP1 (bytes (e.upstream u).connection.requestReads) = _ at parsed
    unfold backendOutput backendReplyBytes
    rw [parsed]
    dsimp only
    rw [methodEq, handler, close]
  have decoded : decodeResponse (bytes (e.upstream u).connection.responseReads) =
      some (wireResponse (resource e.request.target) true) := by
    rw [(contracts.transport.upstream u present).delivered,
      (contracts.runtime.backendReply topology u (backend_edge_ne_entry e u present)).sent _ output]
    exact resource_roundtrip _ _
  change (match e.backendEdge with
    | none => UpstreamResult.failure "no upstream exchange"
    | some u => match decodeResponse (bytes (e.upstream u).connection.responseReads) with
      | some response => .success response
      | none => .failure "invalid upstream response") = _
  simp only [present, decoded]

theorem frontend_authorized (e : Exchange) (contracts : Contracts e)
    (topology : FrontendBackendTopology e)
    (hRequest : ResourceRequest e)
    (authorized : credentialsMatch (context e) = true) :
    frontendResponse e = wireResponse (resource e.request.target) true := by
  have result := upstream_returns_resource e contracts topology hRequest authorized
  simp [frontendResponse, ServiceProofs.runFrontend_response, frontendWith, hRequest.path, authorized,
    proxyHandler, singlePlan, firstUpstreamResponse, result]
  rfl

theorem frontend_rejected (e : Exchange)
    (hRequest : ResourceRequest e)
    (rejected : credentialsMatch (context e) = false) :
    frontendResponse e = unauthorizedResponse := by
  simp [frontendResponse, ServiceProofs.runFrontend_response, frontendWith, hRequest.path, rejected]
  rfl

/-- The rejected branch needs only client transport and actual frontend output.
In particular, it needs no assumptions about upstream parsing or decoding. -/
theorem client_rejected_response (e : Exchange)
    (transport : TransportContracts e) (runtime : RuntimeCorrespondence e)
    (topology : FrontendBackendTopology e)
    (hRequest : ResourceRequest e)
    (rejected : credentialsMatch (context e) = false) :
    observed e = some (view (wireResponse unauthorizedResponse e.clientClose)) := by
  unfold observed
  rw [transport.client.delivered, frontend_reply_sent e runtime topology, hRequest.method,
    frontend_rejected e hRequest rejected, unauthorized_roundtrip]
  rfl

/-- The necessary-credentials direction does not need the forwarding roundtrip.
Status 401 cannot be confused with the resource response's status 200. -/
theorem remote_resource_requires_credentials (e : Exchange)
    (transport : TransportContracts e) (runtime : RuntimeCorrespondence e)
    (topology : FrontendBackendTopology e)
    (hRequest : ResourceRequest e)
    (received : observed e = some (view (resource e.request.target))) :
    credentialsMatch (context e) = true := by
  cases auth : credentialsMatch (context e) with
  | true => rfl
  | false =>
    rw [client_rejected_response e transport runtime topology hRequest auth] at received
    have status := congrArg (fun r : ResponseView => r.status) (Option.some.inj received)
    have rejectedStatus : (wireResponse unauthorizedResponse e.clientClose).status = 401 := by
      have valid : unauthorizedResponse.valid = true := by native_decide
      simp only [wireResponse, valid, ↓reduceIte]
      rfl
    change (wireResponse unauthorizedResponse e.clientClose).status = 200 at status
    rw [rejectedStatus] at status
    contradiction

theorem client_response_delivered (e : Exchange) (contracts : Contracts e)
    (topology : FrontendBackendTopology e)
    (hRequest : ResourceRequest e) :
    observed e = some (view (wireResponse (frontendResponse e) e.clientClose)) := by
  unfold observed
  rw [contracts.transport.client.delivered, frontend_reply_sent e contracts.runtime topology,
    hRequest.method]
  cases authorized : credentialsMatch (context e) with
  | false =>
    rw [frontend_rejected e hRequest authorized, unauthorized_roundtrip]
    rfl
  | true =>
    rw [frontend_authorized e contracts topology hRequest authorized, forwarded_resource_roundtrip]
    rfl

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

/-- Both directions follow from the explicit application topology, per-edge
transport/runtime correspondence, and proved request/response codecs. -/
private theorem resource_iff_of_topology
    (e : Exchange) (contracts : Contracts e)
    (topology : FrontendBackendTopology e)
    (hRequest : ResourceRequest e) :
    observed e = some (view (resource e.request.target)) ↔
      credentialsMatch (context e) = true := by
  constructor
  · exact remote_resource_requires_credentials e contracts.transport contracts.runtime topology hRequest
  · intro hAuth
    rw [client_response_delivered e contracts topology hRequest]
    rw [frontend_authorized e contracts topology hRequest hAuth]
    have valid := wire_response_valid (resource e.request.target) true
    rw [view_wire _ _ valid (by rw [wire_resource_status]; decide)
      (by rw [wire_resource_status]; decide)]
    rw [view_wire _ _ (resource_valid _)
      (by change (200 : UInt16) ≠ 204; native_decide)
      (by change (200 : UInt16) ≠ 304; native_decide)]

/-- The current application graph is constructed from data. Its topology is
proved by ApplicationInput.topology, never supplied as a runtime assumption. -/
theorem remote_resource_iff_credentials
    (input : ApplicationInput) (contracts : Contracts input.exchange)
    (hRequest : ResourceRequest input.exchange) :
    observed input.exchange = some (view (resource input.exchange.request.target)) ↔
      credentialsMatch (context input.exchange) = true :=
  resource_iff_of_topology input.exchange contracts input.topology hRequest

end FrontendBackend.Proofv2
