import Proof.Proof

-- Expected: standard Lean axioms and generated _native.native_decide.ax_*
-- dependencies for closed codec computations. No sorryAx or business axioms.
#print axioms FrontendBackend2.Proof.remote_resource_iff_credentials
#print axioms FrontendBackend2.ServiceProofs.frontend_odd_call
#print axioms FrontendBackend2.ServiceProofs.frontend_even_call
#print axioms FrontendBackend2.ServiceProofs.relay_identity_call
#print axioms FrontendBackend2.second_hop_parsed
