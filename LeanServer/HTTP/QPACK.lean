import LeanServer.HTTP.Codec
import LeanServer.Protocol.HPACK

/-! QPACK field sections with a zero-capacity dynamic table.
The runtime advertises capacity zero. Literal and static references remain fully usable.
Dynamic references are rejected instead of being silently misdecoded. -/
namespace LeanServer.HTTP.QPACK

def staticTable : Array (String × String) := #[
  (":authority", ""), (":path", "/"), ("age", "0"), ("content-disposition", ""),
  ("content-length", "0"), ("cookie", ""), ("date", ""), ("etag", ""),
  ("if-modified-since", ""), ("if-none-match", ""), ("last-modified", ""), ("link", ""),
  ("location", ""), ("referer", ""), ("set-cookie", ""),
  (":method", "CONNECT"), (":method", "DELETE"), (":method", "GET"), (":method", "HEAD"),
  (":method", "OPTIONS"), (":method", "POST"), (":method", "PUT"),
  (":scheme", "http"), (":scheme", "https"), (":status", "103"), (":status", "200"),
  (":status", "304"), (":status", "404"), (":status", "503"),
  ("accept", "*/*"), ("accept", "application/dns-message"), ("accept-encoding", "gzip, deflate, br"),
  ("accept-ranges", "bytes"), ("access-control-allow-headers", "cache-control"),
  ("access-control-allow-headers", "content-type"), ("access-control-allow-origin", "*"),
  ("cache-control", "max-age=0"), ("cache-control", "max-age=2592000"),
  ("cache-control", "max-age=604800"), ("cache-control", "no-cache"), ("cache-control", "no-store"),
  ("cache-control", "public, max-age=31536000"), ("content-encoding", "br"), ("content-encoding", "gzip"),
  ("content-type", "application/dns-message"), ("content-type", "application/javascript"),
  ("content-type", "application/json"), ("content-type", "application/x-www-form-urlencoded"),
  ("content-type", "image/gif"), ("content-type", "image/jpeg"), ("content-type", "image/png"),
  ("content-type", "text/css"), ("content-type", "text/html; charset=utf-8"),
  ("content-type", "text/plain"), ("content-type", "text/plain;charset=utf-8"),
  ("range", "bytes=0-"), ("strict-transport-security", "max-age=31536000"),
  ("strict-transport-security", "max-age=31536000; includesubdomains"),
  ("strict-transport-security", "max-age=31536000; includesubdomains; preload"),
  ("vary", "accept-encoding"), ("vary", "origin"), ("x-content-type-options", "nosniff"),
  ("x-xss-protection", "1; mode=block"), (":status", "100"), (":status", "204"),
  (":status", "206"), (":status", "302"), (":status", "400"), (":status", "403"),
  (":status", "421"), (":status", "425"), (":status", "500"),
  ("accept-language", ""), ("access-control-allow-credentials", "FALSE"),
  ("access-control-allow-credentials", "TRUE"), ("access-control-allow-headers", "*"),
  ("access-control-allow-methods", "get"), ("access-control-allow-methods", "get, post, options"),
  ("access-control-allow-methods", "options"), ("access-control-expose-headers", "content-length"),
  ("access-control-request-headers", "content-type"), ("access-control-request-method", "get"),
  ("access-control-request-method", "post"), ("alt-svc", "clear"), ("authorization", ""),
  ("content-security-policy", "script-src 'none'; object-src 'none'; base-uri 'none'"),
  ("early-data", "1"), ("expect-ct", ""), ("forwarded", ""), ("if-range", ""),
  ("origin", ""), ("purpose", "prefetch"), ("server", ""), ("timing-allow-origin", "*"),
  ("upgrade-insecure-requests", "1"), ("user-agent", ""), ("x-forwarded-for", ""),
  ("x-frame-options", "deny"), ("x-frame-options", "sameorigin") ]

private def stringAt (bytes : ByteArray) (pos bits : Nat) (huffmanMask : UInt8) :
    Option (String × Nat) := do
  let first ← bytes[pos]?
  let (length, start) ← LeanServer.decodeInteger bytes pos bits
  if start + length > bytes.size then none else do
    let raw := bytes.extract start (start + length)
    let decoded ← if first &&& huffmanMask != 0 then LeanServer.huffmanDecode raw else some raw
    let value ← String.fromUTF8? decoded
    return (value, start + length)

def decode (bytes : ByteArray) (limits : Limits := {}) : Option Headers := do
  let (required, pos) ← LeanServer.decodeInteger bytes 0 8
  let (base, pos) ← LeanServer.decodeInteger bytes pos 7
  if required != 0 || base != 0 then none else Id.run do
    let mut pos := pos
    let mut headers : Headers := #[]
    let mut size := 0
    for _ in [:bytes.size] do
      if pos == bytes.size then return some headers
      let some first := bytes[pos]? | return none
      let field : Option (Header × Nat) := do
        if first &&& 0x80 != 0 then
          if first &&& 0x40 == 0 then none else do
            let (index, next) ← LeanServer.decodeInteger bytes pos 6
            let (name, value) ← staticTable[index]?
            return (⟨name, value⟩, next)
        else if first &&& 0xc0 == 0x40 then
          if first &&& 0x10 == 0 then none else do
            let (index, next) ← LeanServer.decodeInteger bytes pos 4
            let (name, _) ← staticTable[index]?
            let (value, next) ← stringAt bytes next 7 0x80
            return (⟨name, value⟩, next)
        else if first &&& 0xe0 == 0x20 then
          let (name, next) ← stringAt bytes pos 3 0x08
          let (value, next) ← stringAt bytes next 7 0x80
          return (⟨name, value⟩, next)
        else none
      let some (header, next) := field | return none
      size := size + header.name.utf8ByteSize + header.value.utf8ByteSize + 32
      if size > limits.maxHeaderBytes then return none
      headers := headers.push header
      pos := next
    return if pos == bytes.size then some headers else none

/-- Literals require no encoder stream synchronization and preserve duplicates. -/
def encode (headers : Headers) : ByteArray :=
  headers.foldl (fun bytes h =>
    let name := (headerName h.name).toUTF8
    let value := h.value.toUTF8
    bytes ++ LeanServer.encodeInteger name.size 3 0x20 ++ name ++
      LeanServer.encodeInteger value.size 7 0 ++ value) (ByteArray.mk #[0, 0])

end LeanServer.HTTP.QPACK
