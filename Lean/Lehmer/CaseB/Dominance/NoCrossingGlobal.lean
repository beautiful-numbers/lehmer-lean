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
-/
theorem caseB_analyticBounds : CaseBAnalyticBounds := by
  refine
    { Mc_le_Mhat := ?_
      Mhat_lt_barrier := ?_
      McNat_lt_barrierCeil := ?_
      barrierCeil_le_mreq := ?_ }
  · exact mc_le_mhat
  · exact mhat_lt_barrier
  · exact mcNat_lt_barrierCeil
  · exact barrierCeil_le_mreq

/--
Global closed no-crossing theorem for the large-pivot Case B regime.
-/
theorem no_crossing_beyond_ystar : NoCrossingBeyondYstar := by
  exact noCrossingBeyondYstar_of_analyticBounds caseB_analyticBounds

end CaseB
end Lehmer