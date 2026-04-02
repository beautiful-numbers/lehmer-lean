-- FILE: Lean/Lehmer/Pivot/MreqAnalytic.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.FiniteTableBridge : def thm
- Lehmer.Pivot.MreqLargeRange : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.FiniteTableBridge
import Lehmer.Pivot.MreqLargeRange

namespace Lehmer
namespace Pivot

/--
Thin public facade for the current choice-2 pivot data bridges.

This file deliberately re-exports only:
- the shared analytic constants,
- the visible finite prefix bridge,
- the explicit large-range endpoint certificate bridge.

It does not claim that a full uniform Appendix A large-range proof has been
internalized in Lean.
-/
def mreqAnalyticReady : Bool := true

/--
Public finite exact prefix currently exposed by the finite table bridge.
-/
def mreqFinitePrefix : List (ℕ × ℕ) :=
  finiteMreqPrefix

/--
Public lookup into the currently exposed finite exact prefix.
-/
def mreqFinitePrefixLookup (y : ℕ) : Option ℕ :=
  finiteMreqPrefixLookup y

/--
Public propositional certificate for the explicit large-range endpoint.
-/
def mreqLargeRangeCertified : Prop :=
  MreqLargeRangeEndpointCertified

/--
The packaged large-range certificate is available.
-/
theorem mreqLargeRangeCertified_true : mreqLargeRangeCertified := by
  exact mreqLargeRangeEndpointCertified

@[simp] theorem mreqAnalyticReady_eq_true :
    mreqAnalyticReady = true := by
  rfl

end Pivot
end Lehmer