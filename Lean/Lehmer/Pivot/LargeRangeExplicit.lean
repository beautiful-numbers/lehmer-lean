-- FILE: Lean/Lehmer/Pivot/LargeRangeExplicit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Data.Pivot.Log2Enclosure : def
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Data.Pivot.Log2Enclosure

namespace Lehmer
namespace Pivot

/--
Choice-2 bridge:
this file exposes only the explicit endpoint certificate data already
internalized in `Data.Pivot.Log2Enclosure`.

It does not claim a full general Appendix A proof in Lean.
-/
def largeRangeEndpointY0 : ℕ :=
  Lehmer.Data.Pivot.pivotA_Y0

def largeRangeEndpointM : ℕ :=
  Lehmer.Data.Pivot.pivotA_endpoint_m

def largeRangeEndpointN : ℕ :=
  Lehmer.Data.Pivot.pivotA_endpoint_n

def largeRangeEndpointOk : Bool :=
  Lehmer.Data.Pivot.pivotA_endpoint_ok

/--
Propositional wrapper for the endpoint certificate.
-/
def LargeRangeEndpointCertified : Prop :=
  largeRangeEndpointOk = true

theorem largeRangeEndpointCertified : LargeRangeEndpointCertified := by
  rfl

@[simp] theorem largeRangeEndpointY0_eq :
    largeRangeEndpointY0 = 30000 := by
  rfl

@[simp] theorem largeRangeEndpointM_eq :
    largeRangeEndpointM = 87302 := by
  rfl

@[simp] theorem largeRangeEndpointN_eq :
    largeRangeEndpointN = 117301 := by
  rfl

@[simp] theorem largeRangeEndpointOk_eq_true :
    largeRangeEndpointOk = true := by
  rfl

/--
Compatibility check with the shared pivot threshold constant.
-/
theorem largeRangeEndpoint_matches_Y0 :
    largeRangeEndpointY0 = Y0 := by
  rfl

end Pivot
end Lehmer