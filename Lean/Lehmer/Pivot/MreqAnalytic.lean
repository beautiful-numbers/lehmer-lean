-- FILE: Lean/Lehmer/Pivot/MreqAnalytic.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.FiniteTableBridge : def thm
- Lehmer.Pivot.LargeRangeExplicit : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.FiniteTableBridge
import Lehmer.Pivot.LargeRangeExplicit

namespace Lehmer
namespace Pivot

/--
Thin public facade for the current choice-2 pivot data bridges.

This file deliberately re-exports only:
- the shared analytic constants,
- the visible finite prefix bridge,
- the explicit large-range endpoint certificate bridge.
-/
def mreqAnalyticReady : Bool := true

def mreqFinitePrefix : List (ℕ × ℕ) :=
  finiteMreqPrefix

def mreqFinitePrefixLookup (y : ℕ) : Option ℕ :=
  finiteMreqPrefixLookup y

def mreqLargeRangeY0 : ℕ :=
  largeRangeEndpointY0

def mreqLargeRangeEndpointM : ℕ :=
  largeRangeEndpointM

def mreqLargeRangeCertified : Prop :=
  LargeRangeEndpointCertified

theorem mreqLargeRangeCertified_true : mreqLargeRangeCertified := by
  exact largeRangeEndpointCertified

@[simp] theorem mreqAnalyticReady_eq_true :
    mreqAnalyticReady = true := by
  rfl

end Pivot
end Lehmer