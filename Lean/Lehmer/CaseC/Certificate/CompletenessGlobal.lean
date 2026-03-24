-- FILE: Lean/Lehmer/CaseC/Certificate/CompletenessGlobal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.Certificate.CheckerGlobal : def thm
- Lehmer.CaseC.Certificate.SoundnessGlobal : def thm
- Lehmer.CaseC.Certificate.CompletenessLocal : thm
-/

import Lehmer.Prelude
import Lehmer.CaseC.Certificate.CheckerGlobal
import Lehmer.CaseC.Certificate.SoundnessGlobal
import Lehmer.CaseC.Certificate.CompletenessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

/--
If a head record resolves to `children` and is semantically locally valid there,
then the global head checker accepts it.
-/
theorem validHead_implies_checkRecordGlobal_true
    (cert : List Record) (R : Record) (children : List Record)
    (hres : localChildren? cert R = some children)
    (hvalid : ValidLocalRecord R children) :
    checkRecordGlobal cert R = true := by
  rw [checkRecordGlobal_some cert R children hres]
  exact validLocalRecord_implies_checkRecordLocal_true R children hvalid

/--
Main global completeness theorem:
if a certificate is semantically valid, then the global checker accepts it.
-/
theorem validCertificate_implies_checkCertificate_true : ∀ cert : List Record,
    ValidCertificate cert → checkCertificate cert = true
  | [], _ => by
      simp [checkCertificate]
  | R :: Rs, h => by
      rcases h with ⟨⟨children, hres, hvalid⟩, htail⟩
      have hhead : checkRecordGlobal (R :: Rs) R = true := by
        exact validHead_implies_checkRecordGlobal_true (R :: Rs) R children hres hvalid
      have htail' : checkCertificate Rs = true := by
        exact validCertificate_implies_checkCertificate_true Rs htail
      simp [checkCertificate, hhead, htail']

/--
A semantically valid certificate is accepted by the global checker.
-/
theorem checkCertificate_true_of_valid
    (cert : List Record)
    (h : ValidCertificate cert) :
    checkCertificate cert = true := by
  exact validCertificate_implies_checkCertificate_true cert h

end Certificate
end CaseC
end Lehmer