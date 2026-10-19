import Proof.ServiceProofs

namespace FrontendBackend

open LeanServer.HTTP

/-- UTF-8 bytes of all parsed header names and values, including duplicates.
Separators and line endings are accounted for separately by the encoder proof. -/
def headerContentBytes (headers : Headers) : Nat :=
  (headers.toList.map fun h => h.name.utf8ByteSize + h.value.utf8ByteSize).sum

/-- Input restrictions on the original parsed request, before frontend rewriting.
These do not assume that encoding or parsing a forwarded request succeeds. -/
structure ForwardingConstraint (request : Request) : Prop where
  headerCount : request.headers.size < 64
  headerBytes : headerContentBytes request.headers ≤ 48 * 1024
  targetBytes : request.target.utf8ByteSize ≤ 8 * 1024
  bodyBytes : request.body.size ≤ 10 * 1024 * 1024

private theorem ascii_bytes (cs : List Char) (ascii : ∀ c ∈ cs, c.toNat ≤ 127) :
    cs.utf8Encode.size = cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := ascii c (by simp)
    have size : c.utf8Size = 1 := by
      unfold Char.utf8Size
      have h : c.val ≤ 127 := hc
      simp [h]
    have single : [c].utf8Encode.size = 1 := by
      rw [← String.toByteArray_singleton, String.size_toByteArray,
        String.utf8ByteSize_singleton, size]
    rw [List.utf8Encode_cons, ByteArray.size_append, single, ih]
    · simp only [List.length_cons]; omega
    · intro d hd
      exact ascii d (by simp [hd])

theorem decimal_bytes_le_eight (n : Nat) (bound : n ≤ 10 * 1024 * 1024) :
    (toString n).utf8ByteSize ≤ 8 := by
  rw [Nat.toString_eq_ofList_toDigits, ← String.size_toByteArray, String.toByteArray_ofList]
  rw [ascii_bytes]
  · apply (Nat.length_toDigits_le_iff (by decide : 1 < 10) (by decide : 0 < 8)).mpr
    omega
  · intro c hc
    have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at digit
    change 48 ≤ c.toNat ∧ c.toNat ≤ 57 at digit
    omega

private theorem sum_filter_le (hs : List Header) (p : Header → Bool) :
    ((hs.filter p).map fun h => h.name.utf8ByteSize + h.value.utf8ByteSize).sum ≤
      (hs.map fun h => h.name.utf8ByteSize + h.value.utf8ByteSize).sum := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    cases hp : p h <;> simp [hp] <;> omega

theorem header_content_filter_le (headers : Headers) (p : Header → Bool) :
    headerContentBytes (headers.filter p) ≤ headerContentBytes headers := by
  simpa [headerContentBytes] using sum_filter_le headers.toList p

private theorem serialized_headers_size (hs : List Header) (acc : String) :
    (hs.foldl (fun out h => out ++ h.name ++ ": " ++ h.value ++ "\r\n") acc).utf8ByteSize =
      acc.utf8ByteSize +
      (hs.map fun h => h.name.utf8ByteSize + h.value.utf8ByteSize).sum + 4 * hs.length := by
  induction hs generalizing acc with
  | nil => simp
  | cons h hs ih =>
    simp only [List.foldl_cons, ih, String.utf8ByteSize_append, List.map_cons,
      List.sum_cons, List.length_cons]
    have colon : ": ".utf8ByteSize = 2 := rfl
    have crlf : "\r\n".utf8ByteSize = 2 := rfl
    rw [colon, crlf]
    omega

theorem forward_headers_size (request : Request) :
    (forwardHeaders request).utf8ByteSize =
      headerContentBytes (retainedHeaders request) + 4 * (retainedHeaders request).size := by
  rw [ServiceProofs.forwardHeaders_eq_retained, serialized_headers_size]
  simp [headerContentBytes]

/-- Credential removal cannot increase any of the constrained quantities. -/
theorem forwarding_constraint_rewrite (request : Request) (h : ForwardingConstraint request) :
    ForwardingConstraint (backendRequest request) := by
  constructor
  · exact Nat.lt_of_le_of_lt (Array.size_filter_le ..) h.headerCount
  · exact Nat.le_trans (header_content_filter_le ..) h.headerBytes
  · exact h.targetBytes
  · exact h.bodyBytes

/-- Exact size of the actual GET header encoder for this example's backend.
76 counts fixed syntax, the configured Host, and the final empty line. -/
theorem upstream_head_size (request : Request) (method : request.method = "GET") :
    (encodeUpstreamHead backendAddr request).size =
      request.target.utf8ByteSize + headerContentBytes (retainedHeaders request) +
        4 * (retainedHeaders request).size + 76 + (toString request.body.size).utf8ByteSize := by
  unfold encodeUpstreamHead
  simp only [String.toUTF8_eq_toByteArray, String.size_toByteArray,
    String.utf8ByteSize_append, method, forward_headers_size]
  change 3 + 1 + request.target.utf8ByteSize + 11 +
    (headerContentBytes (retainedHeaders request) + 4 * (retainedHeaders request).size +
      6 + 9 + 1 + 4 + 2 + (16 + (toString request.body.size).utf8ByteSize + 21)) + 2 = _
  omega

theorem constrained_head_bound (request : Request) (h : ForwardingConstraint request)
    (method : request.method = "GET") :
    (encodeUpstreamHead backendAddr request).size ≤ 57680 := by
  have content := header_content_filter_le request.headers (fun h => !omitForwardHeader h)
  have count := Array.size_filter_le (p := fun h => !omitForwardHeader h) (xs := request.headers)
  have digits := decimal_bytes_le_eight request.body.size h.bodyBytes
  rw [upstream_head_size request method]
  change headerContentBytes (retainedHeaders request) ≤ _ at content
  change (retainedHeaders request).size ≤ _ at count
  have hc := h.headerCount
  have hb := h.headerBytes
  have ht := h.targetBytes
  omega

theorem forwarded_head_bound (request : Request) (h : ForwardingConstraint request)
    (method : request.method = "GET") :
    (encodeUpstreamHead backendAddr (backendRequest request)).size ≤ 57680 :=
  constrained_head_bound (backendRequest request) (forwarding_constraint_rewrite request h) method

/-- These are size guarantees only. Request syntax and parser roundtrip remain
separate proof obligations; no codec or runtime assumptions are used. -/
theorem forwarded_size_limits (request : Request) (h : ForwardingConstraint request)
    (method : request.method = "GET") :
    (encodeUpstreamHead backendAddr (backendRequest request)).size ≤ ({} : Limits).maxHeaderBytes ∧
    (backendRequest request).body.size ≤ ({} : Limits).maxBodyBytes := by
  have head := forwarded_head_bound request h method
  constructor
  · change _ ≤ 65536
    omega
  · exact h.bodyBytes

theorem forwarded_request_size (request : Request) (h : ForwardingConstraint request)
    (method : request.method = "GET") :
    (encodeUpstreamRequest backendAddr (backendRequest request)).size ≤ 57680 + request.body.size := by
  have head := forwarded_head_bound request h method
  simpa only [encodeUpstreamRequest, ByteArray.size_append, backendRequest]
    using Nat.add_le_add_right head request.body.size

end FrontendBackend
