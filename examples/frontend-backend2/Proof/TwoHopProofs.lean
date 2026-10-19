import Proof.CodecProofs

namespace FrontendBackend2

open LeanServer.HTTP

/-- Protocol headers generated on the first hop are removed on the next hop;
only the normalized retained headers survive. -/
theorem decoded_retained (destination : ForwardDestination) (request : Request) :
    retainedHeaders (decodedRequest destination request) =
      (retainedHeaders request).map reparsedHeader := by
  have protocol : (#[Header.mk "Host" destination.authority,
      ⟨"Content-Length", toString request.body.size⟩, ⟨"Connection", "close"⟩].filter
      (fun h => !omitForwardHeader h)) = #[] := by
    have host : headerName "Host" = "host" := by native_decide
    have length : headerName "Content-Length" = "content-length" := by native_decide
    have connection : headerName "Connection" = "connection" := by native_decide
    simp [omitForwardHeader, connectionHeaders, host, length, connection]
  have keep : ((retainedHeaders request).map reparsedHeader).filter
      (fun h => !omitForwardHeader h) = (retainedHeaders request).map reparsedHeader := by
    apply Array.filter_eq_self.mpr
    intro h mem
    obtain ⟨original, originalMem, eq⟩ := Array.mem_map.mp mem
    subst h
    exact (Array.mem_filter.mp originalMem).2
  change (((retainedHeaders request).map reparsedHeader ++ _).filter _) = _
  rw [Array.filter_append (by simp), protocol, keep, Array.append_empty]

/-- Conservative bound: even counting the inserted separator space as retained
payload costs at most one byte per header. No trim canonicality is assumed. -/
theorem reparsed_content_bound (headers : Headers) :
    headerContentBytes (headers.map reparsedHeader) ≤ headerContentBytes headers + headers.size := by
  have listBound : ∀ hs : List Header,
      (hs.map (fun h => h.name.utf8ByteSize + (reparsedHeader h).value.utf8ByteSize)).sum ≤
      (hs.map (fun h => h.name.utf8ByteSize + h.value.utf8ByteSize)).sum + hs.length := by
    intro hs
    induction hs with
    | nil => simp
    | cons h hs ih =>
      have size := trim_size_le (" " ++ h.value)
      simp only [String.utf8ByteSize_append] at size
      change (reparsedHeader h).value.utf8ByteSize ≤ 1 + h.value.utf8ByteSize at size
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  simpa [headerContentBytes, Array.toList_map, List.map_map, reparsedHeader] using listBound headers.toList

theorem first_hop_parsed (destination : ForwardDestination)
    (wire : ByteArray) (request : Request) (rest : ByteArray)
    (parsed : parseHTTP1 wire = .ok (some (request, rest)))
    (constraint : ForwardingConstraint request) (method : request.method = "GET") :
    parseHTTP1 (encodeUpstreamRequest destination.address (backendRequest request)) =
      .ok (some (decodedRequest destination (backendRequest request), ByteArray.empty)) := by
  obtain ⟨_, _, _, nonempty, good⟩ := parsed_request_head wire request rest parsed
  apply request_roundtrip destination (backendRequest request) method nonempty good
    (forwarded_headers_valid wire request rest parsed)
  · rw [destination_head_size]
    exact (forwarded_size_limits request constraint method).1
  · exact constraint.bodyBytes

/-- The second hop is bounded from the ORIGINAL request. The intermediate
request need not have fewer than 64 total headers: the three generated protocol
headers are discarded before encoding. 57743 is below the parser's 65536 limit. -/
theorem second_hop_head_bound (destination : ForwardDestination) (request : Request)
    (constraint : ForwardingConstraint request) :
    (encodeUpstreamHead backendAddr
      (decodedRequest destination (backendRequest request))).size ≤ 57743 := by
  let r := backendRequest request
  have rewritten := forwarding_constraint_rewrite request constraint
  have content := header_content_filter_le r.headers (fun h => !omitForwardHeader h)
  have count := Array.size_filter_le (p := fun h => !omitForwardHeader h) (xs := r.headers)
  have normalized := reparsed_content_bound (retainedHeaders r)
  have digits := decimal_bytes_le_eight request.body.size constraint.bodyBytes
  rw [upstream_head_size _ rfl, decoded_retained, Array.size_map]
  change request.target.utf8ByteSize + headerContentBytes ((retainedHeaders r).map reparsedHeader) +
    4 * (retainedHeaders r).size + 76 + (toString request.body.size).utf8ByteSize ≤ 57743
  change headerContentBytes (retainedHeaders r) ≤ headerContentBytes r.headers at content
  change (retainedHeaders r).size ≤ r.headers.size at count
  have hc : r.headers.size < 64 := rewritten.headerCount
  have hb : headerContentBytes r.headers ≤ 48 * 1024 := rewritten.headerBytes
  have ht := constraint.targetBytes
  omega

theorem second_hop_parsed (destination : ForwardDestination)
    (wire : ByteArray) (request : Request) (rest : ByteArray)
    (parsed : parseHTTP1 wire = .ok (some (request, rest)))
    (constraint : ForwardingConstraint request) :
    let middle := decodedRequest destination (backendRequest request)
    parseHTTP1 (encodeUpstreamRequest backendAddr middle) =
      .ok (some (decodedRequest .backend middle, ByteArray.empty)) := by
  dsimp only
  obtain ⟨_, _, _, nonempty, good⟩ := parsed_request_head wire request rest parsed
  apply request_roundtrip .backend (decodedRequest destination (backendRequest request)) rfl nonempty good
  · rw [decoded_retained]
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro h mem
    obtain ⟨original, originalMem, eq⟩ := Array.mem_map.mp mem
    subst h
    exact reparsed_header_valid original
      (Array.all_eq_true_iff_forall_mem.mp (forwarded_headers_valid wire request rest parsed) original originalMem)
  · have bound := second_hop_head_bound destination request constraint
    change (encodeUpstreamHead backendAddr
      (decodedRequest destination (backendRequest request))).size ≤ 65536
    omega
  · exact constraint.bodyBytes

end FrontendBackend2
