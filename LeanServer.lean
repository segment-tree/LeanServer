-- LeanServer — Root Library Module (Full)
--
-- Legacy full umbrella, including optional crypto and database backends.
-- HTTPServer imports LeanServerPure directly and does not require this module.
--
-- For the pure subset (zero C dependencies), use `import LeanServerPure` instead.
-- See LeanServerPure.lean for details on the pure library.
--
-- Module tiers:
--   Core      : Fundamental types, encoding, error handling (8 modules)
--   Crypto    : Pure-Lean cryptographic primitives and TLS (14 modules, incl. FFI)
--   Protocol  : Wire protocols — HTTP/2, QUIC, WebSocket, gRPC, HPACK (9 modules)
--   Server    : Concurrency and load balancing primitives (2 modules)
--   Db        : Database abstractions (FFI for MySQL, PostgreSQL, SQLite) (4 modules)
--   Proofs    : Formal verification — 914 theorems, 0 axioms, 0 sorry (1 module)
--   Spec      : Formal specifications and refinement proofs (11 modules)
--
-- Runtime extensions and Web convenience APIs are imported separately:
--   Server.HTTPServer and all Server.HTTPServer.* extensions
--   Server middleware: Benchmark, BlueGreen, Canary, CircuitBreaker, ConfigReload,
--     ContentNegotiation, CORS, DistributedTracing, GracefulShutdown, HealthCheck,
--     Metrics, Production, RequestId, ResponseCompression, Timeout
--   Web.*: WebApplication, WebApplicationSimple, SampleWebApp, WebAppTests
--
-- The canonical HTTP/Web application API is exported by LeanServerPure.
-- Import LeanServer.Server.HTTPServer explicitly to execute an application.

-- ── Core ──────────────────────────────────────────────────
import LeanServer.Core.Basic
import LeanServer.Core.Base64
import LeanServer.Core.BufferPool
import LeanServer.Core.ByteSlice
import LeanServer.Core.Logger
import LeanServer.Core.ParserCombinators
import LeanServer.Core.SafeAccess
import LeanServer.Core.ServerError

-- ── Crypto ────────────────────────────────────────────────
import LeanServer.Crypto.AES
import LeanServer.Crypto.Crypto
import LeanServer.Crypto.CertificateManager
import LeanServer.Crypto.FFI
import LeanServer.Crypto.MTLSAuth
import LeanServer.Crypto.NonceManager
import LeanServer.Crypto.RSA
import LeanServer.Crypto.SHA256
import LeanServer.Crypto.SideChannel
import LeanServer.Crypto.TLSHandshake
import LeanServer.Crypto.TLSKeySchedule
import LeanServer.Crypto.TLSSession
import LeanServer.Crypto.X25519
import LeanServer.Crypto.X509Validation

-- ── Protocols ─────────────────────────────────────────────
import LeanServer.Protocol.GRPC
import LeanServer.Protocol.HPACK
import LeanServer.Protocol.HTTP2
import LeanServer.Protocol.HTTP3
import LeanServer.Protocol.QUIC
import LeanServer.Protocol.QUICRetry
import LeanServer.Protocol.WebSocket
import LeanServer.Protocol.WebSocketOverHTTP2
import LeanServer.Protocol.WSCompression

-- ── Server (cycle-free subset) ────────────────────────────
import LeanServer.Server.Concurrency
import LeanServer.Server.LoadBalancer

-- ── Database ──────────────────────────────────────────────
import LeanServer.Db.Database
import LeanServer.Db.PostgreSQL
import LeanServer.Db.MySQL
import LeanServer.Db.SQLite

-- ── Proofs ────────────────────────────────────────────────
import LeanServer.Proofs

-- ── Spec (F2.0 Refinement Architecture) ───────────────────
import LeanServer.Spec.TLSSpec
import LeanServer.Spec.TLSModel
import LeanServer.Spec.TLSRefinement
import LeanServer.Spec.ServerStep
import LeanServer.Spec.UniversalCodecProofs
import LeanServer.Spec.TLSStateMachineProofs
import LeanServer.Spec.ProtocolInvariants
import LeanServer.Spec.CompositionProofs
import LeanServer.Spec.AdvancedProofs
import LeanServer.Spec.AdvancedProofs2
import LeanServer.Spec.AdvancedProofs3
