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

/--
Audit-facing packaged view of the explicit large-range endpoint data.

This is only a consumable API layer over the already exposed endpoint constants.
It does not add any new mathematical semantics.
-/
structure LargeRangeEndpointAPI where
  Y0 : ℕ
  M : ℕ
  N : ℕ
  certified : Prop

/--
Canonical packaged endpoint API.
-/
def largeRangeEndpointAPI : LargeRangeEndpointAPI where
  Y0 := largeRangeEndpointY0
  M := largeRangeEndpointM
  N := largeRangeEndpointN
  certified := LargeRangeEndpointCertified

/--
The packaged endpoint API is certified.
-/
theorem largeRangeEndpointAPI_certified :
    largeRangeEndpointAPI.certified := by
  exact largeRangeEndpointCertified

/--
The packaged endpoint API carries the shared threshold `Y0`.
-/
theorem largeRangeEndpointAPI_Y0 :
    largeRangeEndpointAPI.Y0 = Y0 := by
  rfl

/--
The packaged endpoint API carries the exported endpoint index `M`.
-/
theorem largeRangeEndpointAPI_M :
    largeRangeEndpointAPI.M = 87302 := by
  rfl

/--
The packaged endpoint API carries the exported endpoint index `N`.
-/
theorem largeRangeEndpointAPI_N :
    largeRangeEndpointAPI.N = 117301 := by
  rfl

/--
Audit-facing alias for the packaged endpoint threshold.
-/
abbrev largeRangeConsumableY0 : ℕ :=
  largeRangeEndpointAPI.Y0

/--
Audit-facing alias for the packaged endpoint lower index.
-/
abbrev largeRangeConsumableM : ℕ :=
  largeRangeEndpointAPI.M

/--
Audit-facing alias for the packaged endpoint upper index.
-/
abbrev largeRangeConsumableN : ℕ :=
  largeRangeEndpointAPI.N

/--
Audit-facing alias for the packaged endpoint certificate.
-/
abbrev LargeRangeConsumableCertified : Prop :=
  largeRangeEndpointAPI.certified

/--
The consumable certificate is available.
-/
theorem largeRangeConsumableCertified :
    LargeRangeConsumableCertified := by
  exact largeRangeEndpointAPI_certified

/--
Consumable threshold compatibility with the shared pivot threshold constant.
-/
theorem largeRangeConsumable_matches_Y0 :
    largeRangeConsumableY0 = Y0 := by
  rfl

end Pivot
end Lehmer