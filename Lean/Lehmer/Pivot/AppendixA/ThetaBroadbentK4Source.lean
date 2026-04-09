-- FILE: Lean/Lehmer/Pivot/AppendixA/ThetaBroadbentK4Source.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.AppendixA.ThetaDefs : def
- Lehmer.Pivot.AppendixA.ThetaBroadbentTheorem1 : thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.AppendixA.ThetaDefs
import Lehmer.Pivot.AppendixA.ThetaBroadbentTheorem1

namespace Lehmer
namespace Pivot
namespace AppendixA
namespace ThetaBroadbentK4Source

open scoped Real

theorem theta_broadbent_k4_source
    {x : ℝ}
    (hx1 : (1 : ℝ) ≤ x) :
    |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
  exact ThetaBroadbentTheorem1.theta_k4_case_X0_X1_eq_one hx1

end ThetaBroadbentK4Source
end AppendixA
end Pivot
end Lehmer