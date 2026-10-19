import App

open LeanServer.HTTP

namespace HeaderEchoExample

/-- The socket reports how many bytes from the offered buffer it accepted. -/
structure SendCall where
  offered : ByteArray
  reported : Nat

/-- A successful exchange on one accepted connection. Chunk boundaries are arbitrary. -/
structure Exchange where
  sourceIP : String
  sourcePort : UInt16
  clientSent : ByteArray
  serverRead : List ByteArray
  serverSendCalls : List SendCall
  clientRead : List ByteArray

def bytes (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) ByteArray.empty

def writtenBytes (exchange : Exchange) : ByteArray :=
  bytes (exchange.serverSendCalls.map fun call => call.offered.extract 0 call.reported)

/-- Assumptions about the socket, OS, and network for this one exchange. -/
structure StableTransport (exchange : Exchange) : Prop where
  received : bytes exchange.serverRead = exchange.clientSent
  sendBounded : ∀ call ∈ exchange.serverSendCalls, call.reported ≤ call.offered.size
  delivered : bytes exchange.clientRead = writtenBytes exchange

/-- HEAD has an empty payload, so its encoding is exactly the HTTP/1.1 header section. -/
def responseHead (response : Response) (close : Bool) : ByteArray :=
  encodeHTTP1 response "HEAD" close

/-- Body bytes after the known HTTP/1.1 header section. -/
def observedBody (head wire : ByteArray) : ByteArray :=
  wire.extract head.size wire.size

theorem text_content_length (value : String) :
    (responseHeaders (Response.text value)).get? "content-length" =
      some (toString value.toUTF8.size) := by
  have typeName : headerName "content-type" = "content-type" := by native_decide
  have lengthName : headerName "content-length" = "content-length" := by native_decide
  simp [responseHeaders, Response.text, Headers.get?, typeName, lengthName]

theorem transport_preserves_body (exchange : Exchange)
    (stable : StableTransport exchange) (head body : ByteArray)
    (written : writtenBytes exchange = head ++ body) :
    observedBody head (bytes exchange.clientRead) = body := by
  rw [stable.delivered, written]
  exact ByteArray.extract_append_eq_right rfl (by simp)

theorem application_body (request : Request) (peer : String) (value : String)
    (hasA : request.headers.get? "A" = some value) :
    (application (Context.ofRequest request { peerAddress := some peer })).body = value.toUTF8 := by
  rw [present _ _ hasA]
  rfl

theorem text_valid (value : String) : (Response.text value).valid = true := by
  simp [Response.valid, Response.text, Header.valid, isToken]
  constructor <;> native_decide

/-- Pure HTTP/1.1 result; the handler ignores source IP and has no source-port input. -/
theorem pure_http1_echo (request : Request) (sourceIP : String) (close : Bool)
    (value : String) (hasA : request.headers.get? "A" = some value)
    (notHead : request.method ≠ "HEAD")
    (validText : (Response.text value).valid = true) :
    encodeHTTP1 (application (Context.ofRequest request { peerAddress := some sourceIP }))
        request.method close =
      responseHead (Response.text value) close ++ value.toUTF8 := by
  rw [present _ _ hasA]
  simp only [responseHead, encodeHTTP1, validText, ↓reduceIte]
  simp [responseBody, notHead, Response.text]

/-- The runtime correspondence premise is separate from the transport assumptions. -/
theorem remote_echo (exchange : Exchange) (stable : StableTransport exchange)
    (request : Request) (rest : ByteArray) (close : Bool)
    (parsed : parseHTTP1 (bytes exchange.serverRead) = .ok (some (request, rest)))
    (oneRequest : rest = ByteArray.empty)
    (runtimeCorrespondence :
      writtenBytes exchange =
        encodeHTTP1 (application (Context.ofRequest request
          { peerAddress := some exchange.sourceIP })) request.method close)
    (value : String)
    (hasA : request.headers.get? "A" = some value)
    (notHead : request.method ≠ "HEAD")
    (validText : (Response.text value).valid = true) :
    parseHTTP1 exchange.clientSent = .ok (some (request, ByteArray.empty)) ∧
      observedBody (responseHead (Response.text value) close)
        (bytes exchange.clientRead) = value.toUTF8 := by
  constructor
  · rw [← stable.received, parsed, oneRequest]
  have written := runtimeCorrespondence.trans
    (pure_http1_echo request exchange.sourceIP close value hasA notHead validText)
  exact transport_preserves_body exchange stable _ _ written

/-- Convenience form that discharges the fixed response-validity check by native evaluation. -/
theorem remote_echo_checked (exchange : Exchange) (stable : StableTransport exchange)
    (request : Request) (rest : ByteArray) (close : Bool)
    (parsed : parseHTTP1 (bytes exchange.serverRead) = .ok (some (request, rest)))
    (oneRequest : rest = ByteArray.empty)
    (runtimeCorrespondence :
      writtenBytes exchange =
        encodeHTTP1 (application (Context.ofRequest request
          { peerAddress := some exchange.sourceIP })) request.method close)
    (value : String)
    (hasA : request.headers.get? "A" = some value)
    (notHead : request.method ≠ "HEAD")
    :
    parseHTTP1 exchange.clientSent = .ok (some (request, ByteArray.empty)) ∧
      observedBody (responseHead (Response.text value) close)
        (bytes exchange.clientRead) = value.toUTF8 :=
  remote_echo exchange stable request rest close parsed oneRequest runtimeCorrespondence value hasA notHead
    (text_valid value)


-- these examples are useless
example : (application (Context.ofRequest
    { headers := #[⟨"a", "first"⟩, ⟨"A", "second"⟩] })).body = "first".toUTF8 := by
  native_decide

example : (application (Context.ofRequest
    { headers := #[⟨"A", ""⟩] })).body = ByteArray.empty := by
  native_decide

example : (application (Context.ofRequest
    { headers := #[⟨"A", "汉字"⟩] })).body = "汉字".toUTF8 := by
  native_decide

example : responseBody "HEAD" (Response.text "hello") = ByteArray.empty := by
  rfl

end HeaderEchoExample
