import LeanServer.Server.HTTPServer

namespace FrontendBackend2

open LeanServer
open LeanServer.HTTP

private def proxyMaxResponseBytes : Nat := 1024 * 1024

structure Upstream where
  host : String
  port : UInt16
  deriving Repr, BEq

structure ForwardCall where
  upstream : Upstream
  request : Request

inductive UpstreamResult where
  | success (response : Response)
  | failure (message : String)

def connectionHeaders : List String :=
  ["connection", "keep-alive", "proxy-connection", "transfer-encoding", "upgrade"]

/-- Protocol-owned fields are removed before the encoder rebuilds framing.
Application-specific rewrites belong to the caller's request plan. -/
def omitForwardHeader (header : Header) : Bool :=
  let name := headerName header.name
  name == "host" || name == "content-length" || connectionHeaders.contains name

def retainedHeaders (request : Request) : Headers :=
  request.headers.filter fun h => !omitForwardHeader h

def forwardHeaders (request : Request) : String :=
  request.headers.toList.foldl (fun output header =>
    if omitForwardHeader header then output
    else output ++ header.name ++ ": " ++ header.value ++ "\r\n") ""

/-- The request line, headers, and terminating empty line used by the encoder. -/
def encodeUpstreamHead (upstream : Upstream) (request : Request) : ByteArray :=
  let bodyLength := request.body.size
  let headers := forwardHeaders request ++
    "Host: " ++ upstream.host ++ ":" ++ toString upstream.port ++ "\r\n" ++
    s!"Content-Length: {bodyLength}\r\nConnection: close\r\n"
  (request.method ++ " " ++ request.target ++ " HTTP/1.1\r\n" ++
    headers ++ "\r\n").toUTF8

def encodeUpstreamRequest (upstream : Upstream) (request : Request) : ByteArray :=
  encodeUpstreamHead upstream request ++ request.body

private def findBytes (bytes needle : ByteArray) (start : Nat := 0) : Option Nat := Id.run do
  for i in [start:bytes.size + 1] do
    if i + needle.size ≤ bytes.size && bytes.extract i (i + needle.size) == needle then
      return some i
  return none

private def decimal (value : String) : Option Nat :=
  if value.isEmpty || !value.toList.all (fun c => '0' ≤ c && c ≤ '9') then none
  else value.toNat?

private def parseResponseHead (head : String) : Option (UInt16 × Headers × Nat) := do
  let lines := head.splitOn "\r\n"
  let statusLine := lines.head!
  let statusParts := statusLine.splitOn " "
  if statusParts.length < 2 || statusParts[0]! != "HTTP/1.1" then none
  let status := decimal statusParts[1]!
  let statusCode ← status
  if statusCode > 999 then none
  let headers := (← lines.tail!.mapM fun line => do
    let parts := line.splitOn ":"
    if parts.length < 2 then none
    let name := parts.head!
    let value := String.intercalate ":" parts.tail! |>.trimAscii.toString
    if !Header.valid { name, value } then none
    pure { name, value }).toArray
  let length := match Headers.get? headers "content-length" with
    | some value => decimal value
    | none => some 0
  some (statusCode.toUInt16, headers, length.getD 0)

private partial def readBackendResponse (sock : UInt64) : IO Response := do
  let rec read (buffer : ByteArray) : IO ByteArray := do
    if buffer.size > proxyMaxResponseBytes then
      throw (IO.userError "backend response too large")
    match findBytes buffer "\r\n\r\n".toUTF8 with
    | some _ => pure buffer
    | none =>
      let chunk ← socketRecvBytes sock 16384
      if chunk.isEmpty then throw (IO.userError "backend closed before response headers")
      read (buffer ++ chunk)
  let withHead ← read ByteArray.empty
  let headEnd ← match findBytes withHead "\r\n\r\n".toUTF8 with
    | some position => pure position
    | none => throw (IO.userError "missing backend response separator")
  let head ← match String.fromUTF8? (withHead.extract 0 headEnd) with
    | some value => pure value
    | none => throw (IO.userError "backend response headers are not UTF-8")
  let (status, headers, bodyLength) ← match parseResponseHead head with
    | some result => pure result
    | none => throw (IO.userError "malformed backend response")
  if bodyLength > proxyMaxResponseBytes then throw (IO.userError "backend body too large")
  let rec readBody (buffer : ByteArray) : IO ByteArray := do
    if buffer.size ≥ bodyLength then pure (buffer.extract 0 bodyLength)
    else
      let chunk ← socketRecvBytes sock (min 16384 (bodyLength - buffer.size)).toUInt32
      if chunk.isEmpty then throw (IO.userError "backend closed before response body")
      readBody (buffer ++ chunk)
  let initialBody := withHead.extract (headEnd + 4) withHead.size
  let body ← readBody initialBody
  return { status, headers, body }

/-! One real HTTP/1.1 request to one upstream. Fanout callers sequence this function. -/
def requestUpstreamIO (upstream : Upstream) (request : Request) : IO UpstreamResult := do
  try
    let sock ← socketConnect upstream.host upstream.port.toUInt32
    try
      sendAll sock (encodeUpstreamRequest upstream request)
      return .success (← readBackendResponse sock)
    catch error =>
      return .failure (toString error)
    finally
      socketClose sock
  catch error =>
    return .failure (toString error)

/-
  Generic sequential forwarding. `plan` may return one call or many calls;
  `combine` owns selection, aggregation, and partial-failure policy.
-/
def proxyHandler [Monad m]
    (plan : Context → List ForwardCall)
    (requestUpstream : Upstream → Request → m UpstreamResult)
    (combine : Context → List UpstreamResult → m Response) : Handler m :=
  fun ctx => do
    let results ← (plan ctx).mapM fun call =>
      requestUpstream call.upstream call.request
    combine ctx results

/-- A caller may rewrite application fields before the protocol encoder runs. -/
def singlePlan (upstream : Upstream) (rewrite : Request → Request := id) : Context → List ForwardCall :=
  fun ctx => [{ upstream, request := rewrite ctx.request }]

def firstUpstreamResponse [Monad m] : Context → List UpstreamResult → m Response
  | _, [.success response] => pure response
  | _, _ => pure (Response.text "Bad Gateway" 502)

end FrontendBackend2
