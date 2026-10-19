import LeanServer.HTTP.Types

namespace LeanServer.HTTP

structure Limits where
  maxHeaderBytes : Nat := 65536
  maxBodyBytes : Nat := 10485760
  deriving Inhabited

structure RequestError where
  status : UInt16
  message : String
  deriving Repr, Inhabited

def RequestError.response (error : RequestError) : Response :=
  Response.text error.message error.status

private def badRequest : RequestError := ⟨400, "Bad Request"⟩

/-- Find CRLF (or CRLF CRLF) without decoding the body as UTF-8. -/
def findBytes (bytes needle : ByteArray) (start : Nat := 0) : Option Nat := Id.run do
  for i in [start:bytes.size + 1] do
    if i + needle.size ≤ bytes.size && bytes.extract i (i + needle.size) == needle then
      return some i
  return none

def parseHeader (line : String) : Except RequestError Header := do
  let parts := line.splitOn ":"
  if parts.length < 2 then throw badRequest
  let header := Header.mk parts.head! (String.intercalate ":" parts.tail!).trimAscii.toString
  if !header.valid then throw badRequest
  return header

private def decimal (value : String) : Except RequestError Nat := do
  if value.isEmpty || !value.toList.all (fun c => '0' ≤ c && c ≤ '9') then throw badRequest
  match value.toNat? with
  | some n => pure n
  | none => throw badRequest

private def hexNat (value : String) : Except RequestError Nat := do
  if value.isEmpty then throw badRequest
  value.toList.foldlM (fun n c => do
    let d ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
      else throw badRequest
    pure (n * 16 + d)) 0

private def parseChunks (bytes : ByteArray) (start : Nat) (limits : Limits) :
    Except RequestError (Option (ByteArray × Nat)) := do
  let mut pos := start
  let mut body := ByteArray.empty
  -- Each iteration consumes at least a chunk-size line.
  for _ in [:bytes.size + 1] do
    let some lineEnd := findBytes bytes "\r\n".toUTF8 pos | return none
    if lineEnd - pos > limits.maxHeaderBytes then throw ⟨431, "Request Header Fields Too Large"⟩
    let some line := String.fromUTF8? (bytes.extract pos lineEnd) | throw badRequest
    let size ← hexNat (line.splitOn ";").head!
    pos := lineEnd + 2
    if size == 0 then
      let trailerStart := pos
      for _ in [:bytes.size + 1] do
        let some trailerEnd := findBytes bytes "\r\n".toUTF8 pos | return none
        if trailerEnd - trailerStart > limits.maxHeaderBytes then
          throw ⟨431, "Request Header Fields Too Large"⟩
        if trailerEnd == pos then return some (body, pos + 2)
        let some trailer := String.fromUTF8? (bytes.extract pos trailerEnd) | throw badRequest
        let h ← parseHeader trailer
        if ["content-length", "transfer-encoding", "host"].contains (headerName h.name) then
          throw badRequest
        pos := trailerEnd + 2
      throw badRequest
    if body.size + size > limits.maxBodyBytes then throw ⟨413, "Content Too Large"⟩
    if pos + size + 2 > bytes.size then return none
    if bytes.extract (pos + size) (pos + size + 2) != "\r\n".toUTF8 then throw badRequest
    body := body ++ bytes.extract pos (pos + size)
    pos := pos + size + 2
  throw badRequest

/-- Incremental HTTP/1.1 parser: `none` means more bytes are needed.
    Successful parsing returns the untouched bytes for the next request. -/
def parseHTTP1 (bytes : ByteArray) (limits : Limits := {}) :
    Except RequestError (Option (Request × ByteArray)) := do
  let some headerEnd := findBytes bytes "\r\n\r\n".toUTF8 | do
    if bytes.size > limits.maxHeaderBytes then throw ⟨431, "Request Header Fields Too Large"⟩
    return none
  if headerEnd + 4 > limits.maxHeaderBytes then throw ⟨431, "Request Header Fields Too Large"⟩
  let some head := String.fromUTF8? (bytes.extract 0 headerEnd) | throw badRequest
  let lines := head.splitOn "\r\n"
  let [method, target, version] := lines.head!.splitOn " " | throw badRequest
  if !isToken method || target.isEmpty || target.toList.any (fun c => c.toNat ≤ 32 || c.toNat == 127) then
    throw badRequest
  if version != "HTTP/1.1" then throw ⟨505, "HTTP Version Not Supported"⟩
  let headers : Headers := (← lines.tail!.mapM parseHeader).toArray
  if (headers.getAll "host").size != 1 || (headers.get? "host") == some "" then throw badRequest
  let lengths := headers.getAll "content-length"
  let encodings := headers.getAll "transfer-encoding"
  if lengths.size > 1 || encodings.size > 1 || (!lengths.isEmpty && !encodings.isEmpty) then
    throw badRequest
  let bodyStart := headerEnd + 4
  let request : Request := { method, target, headers, authority := headers.get? "host", scheme := some "http" }
  if !encodings.isEmpty then
    if headerName encodings[0]! != "chunked" then throw ⟨501, "Unsupported Transfer-Encoding"⟩
    match ← parseChunks bytes bodyStart limits with
    | none => return none
    | some (body, consumed) => return some ({ request with body }, bytes.extract consumed bytes.size)
  let length ← if lengths.isEmpty then pure 0 else decimal lengths[0]!
  if length > limits.maxBodyBytes then throw ⟨413, "Content Too Large"⟩
  if bodyStart + length > bytes.size then return none
  return some ({ request with body := bytes.extract bodyStart (bodyStart + length) },
    bytes.extract (bodyStart + length) bytes.size)

/-- Convert decoded HPACK/QPACK fields into an application request. -/
def fromFields (version : Version) (fields : Headers) (body : ByteArray)
    (limits : Limits := {}) : Except RequestError Request := do
  if body.size > limits.maxBodyBytes then throw ⟨413, "Content Too Large"⟩
  if fields.foldl (fun n h => n + h.name.utf8ByteSize + h.value.utf8ByteSize + 32) 0 > limits.maxHeaderBytes then
    throw ⟨431, "Request Header Fields Too Large"⟩
  let mut ordinary := false
  let mut seen : List String := []
  for h in fields do
    if h.name != headerName h.name then throw badRequest
    if h.name.startsWith ":" then
      if ordinary || seen.contains h.name || ![":method", ":path", ":scheme", ":authority"].contains h.name then
        throw badRequest
      seen := h.name :: seen
    else
      ordinary := true
      if !h.valid || ["connection", "keep-alive", "upgrade", "transfer-encoding", "proxy-connection"].contains h.name then
        throw badRequest
      if h.name == "te" && headerName h.value != "trailers" then throw badRequest
  let some method := fields.get? ":method" | throw badRequest
  let some target := fields.get? ":path" | throw badRequest
  let some scheme := fields.get? ":scheme" | throw badRequest
  if !isToken method || target.isEmpty || target.toList.any (fun c => c.toNat ≤ 32 || c.toNat == 127) then
    throw badRequest
  let lengths := fields.getAll "content-length"
  if lengths.size > 1 then throw badRequest
  if !lengths.isEmpty then
    if (← decimal lengths[0]!) != body.size then throw badRequest
  return { method, target, scheme := some scheme, authority := fields.get? ":authority", version
           headers := fields.filter (fun h => !h.name.startsWith ":"), body }

def responseBody (method : String) (response : Response) : ByteArray :=
  if method == "HEAD" || response.status == 204 || response.status == 304 then ByteArray.empty
  else response.body

/-- Connection/framing headers are owned by the transport. Duplicate Set-Cookie survives. -/
def responseHeaders (response : Response) : Headers :=
  let headers := response.headers.filter fun h =>
    !["connection", "keep-alive", "upgrade", "transfer-encoding", "proxy-connection", "content-length"].contains (headerName h.name)
  if response.status == 204 || response.status == 304 then headers
  else headers.push ⟨"content-length", toString response.body.size⟩

def encodeHTTP1 (response : Response) (method : String := "GET") (close : Bool := false) : ByteArray :=
  let response := if response.valid then response else Response.text "Internal Server Error" 500
  let fields := (responseHeaders response).foldl (fun s h => s ++ h.name ++ ": " ++ h.value ++ "\r\n") ""
  (s!"HTTP/1.1 {response.status} \r\n{fields}Connection: {if close then "close" else "keep-alive"}\r\n\r\n").toUTF8 ++
    responseBody method response

end LeanServer.HTTP
