import Lake
open Lake DSL System

package LeanServer where
  version := v!"0.2.0"
  buildDir := (get_config? buildDir).getD ".lake/build"

private def nativeArchive (pkg : Package) (name : String) (sources : Array String) :
    FetchM (Job FilePath) := do
  let objects ← sources.mapM fun source => do
    let input ← inputTextFile (pkg.dir / "src" / (source ++ ".c"))
    buildLeanO (pkg.buildDir / "native" / (source ++ ".o")) input #[] #["-fPIC"]
  buildStaticLib (pkg.buildDir / "lib" / nameToStaticLib name) objects

target network pkg : FilePath :=
  nativeArchive pkg "LeanServerNetwork" #["Network"]

target optionalNative pkg : FilePath :=
  nativeArchive pkg "LeanServerOptional" #["db_stubs", "crypto_ffi", "sqlite_ffi"]

@[default_target]
lean_lib LeanServer

lean_lib LeanServerRuntime where
  roots := #[`LeanServer.Server, `LeanServer.Web]
  globs := #[.one `LeanServer.Server.HTTPServer]
  moreLinkObjs := #[network]

lean_lib LeanServerOptional where
  roots := #[`LeanServer.Db, `LeanServer.Crypto.FFI]
  moreLinkObjs := #[optionalNative]

-- Declared last so these modules do not inherit runtime native dependencies.
lean_lib LeanServerPure where
  roots := #[`LeanServerPure, `LeanServer.HTTP, `LeanServer.Server.Concurrency,
    `LeanServer.Web,
    `LeanServer.Server.CORSMiddleware, `LeanServer.Server.ContentNegotiation,
    `LeanServer.Server.ResponseCompression]
  globs := #[.one `LeanServerPure]

lean_lib LeanServerExamples where
  roots := #[`examples]
  globs := #[.one `examples.HeaderEchoApp]

lean_exe leanserver where
  root := `Main

lean_exe webserver where
  root := `app.WebServerMainSimple
  moreLinkObjs := #[network]

lean_exe realhttps where
  root := `app.RealHTTPServer

lean_exe test where
  root := `tests.Test

lean_exe testfileio where
  root := `tests.TestFileIO

lean_exe testquic where
  root := `tests.TestQUIC

lean_exe testdatabase where
  root := `tests.TestDatabase

lean_exe databaseexamples where
  root := `tests.DatabaseExamples

lean_exe testtcp where
  root := `tests.TestTCP
  moreLinkObjs := #[network]

lean_exe test_primitives where
  root := `tests.TestCryptoPrimitives

lean_exe test_aes where
  root := `tests.TestAES

lean_exe test_x25519 where
  root := `tests.TestX25519

lean_exe webapptests where
  root := `LeanServer.Web.WebAppTests

lean_exe test_rfc_vectors where
  root := `tests.TestRFCVectors

lean_exe differential_crypto where
  root := `tests.DifferentialCrypto

lean_exe http2_conformance where
  root := `tests.HTTP2Conformance

lean_exe tls_handshake_e2e where
  root := `tests.TLSHandshakeE2E

lean_exe test_integration where
  root := `tests.TestIntegration

lean_exe fuzz_tls where
  root := `fuzz.FuzzTLS

lean_exe fuzz_http2 where
  root := `fuzz.FuzzHTTP2

lean_exe fuzz_quic where
  root := `fuzz.FuzzQUIC

lean_exe fuzz_websocket where
  root := `fuzz.FuzzWebSocket

lean_exe prop_tests where
  root := `tests.PropertyTests

lean_exe test_integration_real where
  root := `tests.TestIntegrationReal

lean_exe fuzz_extended where
  root := `tests.FuzzExtended

lean_exe header_echo where
  root := `examples.HeaderEcho

lean_exe framework_tests where
  root := `tests.Framework

lean_exe framework_server where
  root := `tests.FrameworkServer
