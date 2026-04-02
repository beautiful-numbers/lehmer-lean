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

/--
Closed analytic bounds package for the Case B no-crossing regime.

This file is intentionally only a final assembly layer: all substantive
analytic work must already have been exported by `AnalyticNoCrossing`.

At the current stage, the pivot-side connector
`Nat.ceil (analyticBarrier y) ≤ mreq y` is not yet exported as a theorem by
`AnalyticNoCrossing`, so the assembly must be parameterized by that connector.
-/
theorem caseB_analyticBounds
    (hbarrier :
      ∀ y : ℕ, Y0 ≤ y →
        Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y) :
    CaseBAnalyticBounds := by
  refine
    { Mc_le_Mhat := ?_
      Mhat_lt_barrier := ?_
      McNat_lt_barrierCeil := ?_
      barrierCeil_le_mreq := ?_ }
  · exact mc_le_mhat
  · exact mhat_lt_barrier
  · exact mcNat_lt_barrierCeil
  · exact hbarrier

/--
Global closed no-crossing theorem for the large-pivot Case B regime.

This theorem is purely an assembly corollary of the three Case B analytic
connectors plus the final pivot-side connector.
-/
theorem no_crossing_beyond_ystar
    (hbarrier :
      ∀ y : ℕ, Y0 ≤ y →
        Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y) :
    NoCrossingBeyondYstar := by
  exact noCrossingBeyondYstar_of_analyticBounds (caseB_analyticBounds hbarrier)

end CaseB
end Lehmer