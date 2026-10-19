import FrontendCore
import BackendCore
import Init.Data.Nat.ToString

namespace FrontendBackend.ServiceProofs

open LeanServer.HTTP

/-! Properties of the actual pure application code. No transport assumptions. -/

def recordUpstream (result : UpstreamResult) (addr : Upstream) (request : Request) :
    StateM (List ForwardCall) UpstreamResult := do
  modify (· ++ [{ upstream := addr, request }])
  pure result

def runFrontend (result : UpstreamResult) (ctx : Context) : Response × List ForwardCall :=
  (frontendWith (recordUpstream result) ctx).run []

theorem frontend_rejected_no_call (ctx : Context) (result : UpstreamResult)
    (notLogin : ctx.path ≠ "/login") (rejected : credentialsMatch ctx = false) :
    runFrontend result ctx = (unauthorizedResponse, []) := by
  simp [runFrontend, frontendWith, notLogin, rejected]
  rfl

theorem frontend_authorized_call (ctx : Context) (result : UpstreamResult)
    (notLogin : ctx.path ≠ "/login") (authorized : credentialsMatch ctx = true) :
    (runFrontend result ctx).2 =
      [{ upstream := backendAddr, request := backendRequest ctx.request }] := by
  cases result <;>
    simp [runFrontend, frontendWith, notLogin, authorized, proxyHandler,
      singlePlan, recordUpstream, firstUpstreamResponse] <;> rfl

theorem frontend_login_no_call (ctx : Context) (result : UpstreamResult)
    (login : ctx.path = "/login") :
    (runFrontend result ctx).2 = [] := by
  simp [runFrontend, frontendWith, login]
  rfl

/-- The recording interpretation has exactly the same response as the Id one.
Unlike a response-only replay, it exposes which address and request were used. -/
theorem runFrontend_response (ctx : Context) (result : UpstreamResult) :
    (runFrontend result ctx).1 =
      frontendWith (m := Id) (fun _ _ => result) ctx := by
  unfold runFrontend frontendWith
  split
  · rfl
  · split
    · rfl
    · cases result <;>
        simp [proxyHandler, singlePlan, recordUpstream, firstUpstreamResponse] <;> rfl

theorem credentials_match_iff (ctx : Context) :
    credentialsMatch ctx = true ↔
      ctx.request.headers.getAll "x-username" = #["Tom"] ∧
      ctx.request.headers.getAll "x-password" = #["123456"] := by
  simp [credentialsMatch]

/-- The frontend rewrite changes only headers. -/
theorem backend_request_fields (request : Request) :
    (backendRequest request).method = request.method ∧
    (backendRequest request).target = request.target ∧
    (backendRequest request).body = request.body := by
  exact ⟨rfl, rfl, rfl⟩

/-- Decimal Content-Length values satisfy the real header validator. -/
theorem decimal_value_valid (n : Nat) : (toString n).toList.all
    (fun c => c == '\t' || (c.toNat ≥ 32 && c.toNat != 127)) = true := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  apply List.all_eq_true.mpr
  intro c hc
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at digit
  change 48 ≤ c.toNat ∧ c.toNat ≤ 57 at digit
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  right
  constructor <;> omega

theorem response_headers_valid (r : Response) (valid : r.valid = true) :
    (responseHeaders r).all Header.valid = true := by
  have headers : r.headers.all Header.valid = true := (Bool.and_eq_true_iff.mp valid).2
  have filtered : (r.headers.filter fun h =>
      !["connection", "keep-alive", "upgrade", "transfer-encoding", "proxy-connection", "content-length"].contains
        (headerName h.name)).all Header.valid = true := by
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro h mem
    exact Array.all_eq_true_iff_forall_mem.mp headers h (Array.mem_filter.mp mem).1
  unfold responseHeaders
  split
  · exact filtered
  · rw [Array.all_push, filtered, Bool.true_and]
    simp only [Header.valid]
    have token : isToken "content-length" = true := by native_decide
    simp only [token, Bool.true_and]
    exact decimal_value_valid _

theorem retained_headers_no_username (request : Request) :
    (retainedHeaders (backendRequest request)).getAll "x-username" = #[] := by
  have key : headerName "x-username" = "x-username" := by native_decide
  simp only [retainedHeaders, backendRequest, Headers.getAll, Array.filter_filter, key]
  have empty : request.headers.filter (fun h =>
      (headerName h.name == "x-username") && (!omitForwardHeader h && !omitBackendHeader h)) = #[] := by
    apply Array.filter_eq_empty_iff.mpr
    intro h _
    by_cases same : headerName h.name = "x-username" <;> simp [omitBackendHeader, same]
  rw [empty]
  simp

theorem retained_headers_no_password (request : Request) :
    (retainedHeaders (backendRequest request)).getAll "x-password" = #[] := by
  have key : headerName "x-password" = "x-password" := by native_decide
  simp only [retainedHeaders, backendRequest, Headers.getAll, Array.filter_filter, key]
  have empty : request.headers.filter (fun h =>
      (headerName h.name == "x-password") && (!omitForwardHeader h && !omitBackendHeader h)) = #[] := by
    apply Array.filter_eq_empty_iff.mpr
    intro h _
    by_cases same : headerName h.name = "x-password" <;> simp [omitBackendHeader, same]
  rw [empty]
  simp

/-- Relates the proved filter to the actual encoder, not a separate mock. -/
theorem forwardHeaders_eq_retained (request : Request) :
    forwardHeaders request =
      (retainedHeaders request).toList.foldl
        (fun output h => output ++ h.name ++ ": " ++ h.value ++ "\r\n") "" := by
  simp only [forwardHeaders, retainedHeaders, Array.toList_filter, List.foldl_filter]
  congr 1
  funext output h
  cases omitForwardHeader h <;> simp

/-- Frontend rewriting followed by generic encoding preserves the old combined
encoder byte for byte, for arbitrary requests and backend addresses. -/
theorem encodeUpstreamRequest_unchanged (addr : Upstream) (request : Request) :
    encodeUpstreamRequest addr (backendRequest request) =
      let headers := request.headers.toList.foldl (fun output h =>
        let name := headerName h.name
        if name == "x-username" || name == "x-password" || name == "host" ||
            name == "content-length" || connectionHeaders.contains name then output
        else output ++ h.name ++ ": " ++ h.value ++ "\r\n") ""
      (request.method ++ " " ++ request.target ++ " HTTP/1.1\r\n" ++
        (headers ++ "Host: " ++ addr.host ++ ":" ++ toString addr.port ++ "\r\n" ++
          s!"Content-Length: {request.body.size}\r\nConnection: close\r\n") ++
        "\r\n").toUTF8 ++ request.body := by
  have headers : forwardHeaders (backendRequest request) =
      request.headers.toList.foldl (fun output h =>
        let name := headerName h.name
        if name == "x-username" || name == "x-password" || name == "host" ||
            name == "content-length" || connectionHeaders.contains name then output
        else output ++ h.name ++ ": " ++ h.value ++ "\r\n") "" := by
    simp only [forwardHeaders, backendRequest, Array.toList_filter, List.foldl_filter]
    congr 1
    funext output h
    simp only [omitBackendHeader, omitForwardHeader]
    cases hUser : (headerName h.name == "x-username") <;>
      cases hPassword : (headerName h.name == "x-password") <;> simp
  unfold encodeUpstreamRequest encodeUpstreamHead
  rw [headers]
  rfl

end FrontendBackend.ServiceProofs
