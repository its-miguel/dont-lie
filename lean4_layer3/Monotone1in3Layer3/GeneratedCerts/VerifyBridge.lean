import Monotone1in3Layer3.Certificate
import Monotone1in3Layer3.GeneratedCerts.Tseitin610Cert
import Monotone1in3Layer3.GeneratedCerts.Pigeonhole637Cert
import Monotone1in3Layer3.GeneratedCerts.HybridF2Z600Cert

/-!
# End-to-End Rust → Lean 4 Kernel Verification Bridge (n ≥ 610)

Instantiates `unified_certificate_sound` directly on the two real high-scale UNSAT
certificates emitted by `rust_layer2 --export-cert`:
1. `F3_tseitin_expander_unsat_t600_s20324691` (n = 610, m = 433)
2. `F5_pigeonhole_PHP9_10_s20332763` (n = 637, m = 556)

Zero `sorry` placeholders.
-/

namespace Monotone1in3.Bridge

open Monotone1in3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem tseitin_610_rust_cert_valid :
    verifyCertificate Tseitin610Cert.formula Tseitin610Cert.cert = true := by
  decide

theorem tseitin_610_unsat :
    ¬ ∃ x : Nat → Bool, SatisfiesFormula Tseitin610Cert.formula x :=
  unified_certificate_sound Tseitin610Cert.formula Tseitin610Cert.cert tseitin_610_rust_cert_valid

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem php_637_rust_cert_valid :
    verifyCertificate Pigeonhole637Cert.formula Pigeonhole637Cert.cert = true := by
  decide

theorem php_637_unsat :
    ¬ ∃ x : Nat → Bool, SatisfiesFormula Pigeonhole637Cert.formula x :=
  unified_certificate_sound Pigeonhole637Cert.formula Pigeonhole637Cert.cert php_637_rust_cert_valid

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
theorem hybrid_f2_z_783_rust_cert_valid :
    verifyCertificate HybridF2Z600Cert.formula HybridF2Z600Cert.cert = true := by
  decide

theorem hybrid_f2_z_783_unsat :
    ¬ ∃ x : Nat → Bool, SatisfiesFormula HybridF2Z600Cert.formula x :=
  unified_certificate_sound HybridF2Z600Cert.formula HybridF2Z600Cert.cert hybrid_f2_z_783_rust_cert_valid

end Monotone1in3.Bridge
