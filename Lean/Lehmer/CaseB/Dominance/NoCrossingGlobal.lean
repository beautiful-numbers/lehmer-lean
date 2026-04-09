-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossingGlobal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.CaseB.Dominance.AnalyticNoCrossing : thm
-/

import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.AnalyticNoCrossing

namespace Lehmer
namespace CaseB

abbrev NoCrossingGlobalCertificate : Prop :=
  NoCrossingBeyondYstar

@[simp] theorem NoCrossingGlobalCertificate_def :
    NoCrossingGlobalCertificate = NoCrossingBeyondYstar := rfl

theorem noCrossingGlobalCertificate_of_noCrossingBeyondYstar
    (h : NoCrossingBeyondYstar) :
    NoCrossingGlobalCertificate := by
  exact h

theorem noCrossingAt_of_NoCrossingGlobalCertificate
    (h : NoCrossingGlobalCertificate)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt y := by
  exact h y hy hp

end CaseB
end Lehmer