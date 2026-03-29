-- FILE: Lean/Lehmer/Pivot/AppendixA/Core.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.LargeRangeExplicit : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.LargeRangeExplicit

namespace Lehmer
namespace Pivot
namespace AppendixA

/--
Choice-2 Appendix A facade.

In the current Lean architecture, we do not expose a full general Appendix A
proof. We only retain the explicit large-range endpoint certificate interface
used downstream.
-/
def AppendixAReady : Prop :=
  LargeRangeEndpointCertified

/--
The explicit endpoint certificate is available.
-/
theorem appendixA_ready : AppendixAReady := by
  exact largeRangeEndpointCertified

/--
Public re-export of the shared large-range threshold.
-/
def appendixA_Y0 : ℕ :=
  largeRangeEndpointY0

@[simp] theorem appendixA_Y0_eq :
    appendixA_Y0 = Y0 := by
  rfl

end AppendixA
end Pivot
end Lehmer