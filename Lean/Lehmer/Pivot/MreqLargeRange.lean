-- FILE: Lean/Lehmer/Pivot/MreqLargeRange.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.LargeRangeExplicit : def thm
- Lehmer.Data.Pivot.Log2Enclosure : def
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.LargeRangeExplicit
import Lehmer.Data.Pivot.Log2Enclosure

namespace Lehmer
namespace Pivot

/--
Endpoint threshold used by the explicit Appendix A large-range check.

This file is intentionally endpoint-local: it packages the certified numerical
data recorded at `y = Y0`, but does not yet provide any global propagation to
all `y ≥ Y0`, and does not yet expose a final bridge toward `mreq`.
-/
def mreqLargeRangeY0 : ℕ :=
  largeRangeEndpointY0

/--
Endpoint lower index
`m = floor(C1 * y^2 / log y)`
recorded in the explicit Appendix A endpoint certificate.
-/
def mreqLargeRangeEndpointM : ℕ :=
  largeRangeEndpointM

/--
Endpoint upper index
`n = m + y - 1`
recorded in the explicit Appendix A endpoint certificate.
-/
def mreqLargeRangeEndpointN : ℕ :=
  largeRangeEndpointN

@[simp] theorem mreqLargeRangeY0_eq :
    mreqLargeRangeY0 = Y0 := by
  exact largeRangeEndpoint_matches_Y0

@[simp] theorem mreqLargeRangeEndpointM_eq :
    mreqLargeRangeEndpointM = 87302 := by
  exact largeRangeEndpointM_eq

@[simp] theorem mreqLargeRangeEndpointN_eq :
    mreqLargeRangeEndpointN = 117301 := by
  exact largeRangeEndpointN_eq

/--
Raw source path for the explicit endpoint certificate artifact.
-/
def mreqLargeRangeProofSourcePath : String :=
  Lehmer.Data.Pivot.pivotAProofSourcePath

/--
Raw source digest for the explicit endpoint certificate artifact.
-/
def mreqLargeRangeProofSourceSha256 : String :=
  Lehmer.Data.Pivot.pivotAProofSourceSha256

/--
Raw lower enclosure string for `log 2` recorded in the endpoint certificate
data.
-/
def mreqLargeRangeLn2LowerString : String :=
  Lehmer.Data.Pivot.pivotA_ln2_lb

/--
Raw upper enclosure string for the endpoint RHS quantity recorded in the
certificate data.
-/
def mreqLargeRangeRhsUpperString : String :=
  Lehmer.Data.Pivot.pivotA_rhs_upper

/--
Certificate-level proposition exported by this file.

At the current stage, this is the exact certified fact already internalized in
the data layer: the endpoint check has been validated in exact arithmetic.
This file does not yet convert that validation into a global large-range pivot
theorem.
-/
def MreqLargeRangeEndpointCertified : Prop :=
  LargeRangeEndpointCertified

/--
The endpoint certificate is available.
-/
theorem mreqLargeRangeEndpointCertified :
    MreqLargeRangeEndpointCertified := by
  exact largeRangeEndpointCertified

/--
The explicit endpoint certificate is anchored at `Y0 = 30000`.
-/
theorem mreqLargeRange_endpoint_at_Y0 :
    mreqLargeRangeY0 = 30000 := by
  simp [mreqLargeRangeY0]

/--
The explicit endpoint certificate uses the lower index `m = 87302`.
-/
theorem mreqLargeRange_endpoint_M :
    mreqLargeRangeEndpointM = 87302 := by
  simp [mreqLargeRangeEndpointM]

/--
The explicit endpoint certificate uses the upper index `n = 117301`.
-/
theorem mreqLargeRange_endpoint_N :
    mreqLargeRangeEndpointN = 117301 := by
  simp [mreqLargeRangeEndpointN]

/--
Packaged endpoint-local data for the large-range pivot certificate.

This structure is intentionally certificate-facing and endpoint-only.
It records exactly the local constants and the availability of the certified
endpoint check, but does not yet assert any propagated theorem on `UBm` or
`mreq`.
-/
structure MreqLargeRangeEndpointData where
  y0 : ℕ
  m : ℕ
  n : ℕ
  ln2LowerString : String
  rhsUpperString : String
  certified : Prop

/--
Canonical endpoint-local package extracted from the Appendix A certificate.
-/
def mreqLargeRangeEndpointData : MreqLargeRangeEndpointData where
  y0 := mreqLargeRangeY0
  m := mreqLargeRangeEndpointM
  n := mreqLargeRangeEndpointN
  ln2LowerString := mreqLargeRangeLn2LowerString
  rhsUpperString := mreqLargeRangeRhsUpperString
  certified := MreqLargeRangeEndpointCertified

/--
The canonical endpoint-local package is certified.
-/
theorem mreqLargeRangeEndpointData_certified :
    mreqLargeRangeEndpointData.certified := by
  exact mreqLargeRangeEndpointCertified

@[simp] theorem mreqLargeRangeEndpointData_y0 :
    mreqLargeRangeEndpointData.y0 = Y0 := by
  exact mreqLargeRangeY0_eq

@[simp] theorem mreqLargeRangeEndpointData_m :
    mreqLargeRangeEndpointData.m = 87302 := by
  exact mreqLargeRangeEndpointM_eq

@[simp] theorem mreqLargeRangeEndpointData_n :
    mreqLargeRangeEndpointData.n = 117301 := by
  exact mreqLargeRangeEndpointN_eq

@[simp] theorem mreqLargeRangeEndpointData_ln2LowerString :
    mreqLargeRangeEndpointData.ln2LowerString = mreqLargeRangeLn2LowerString := by
  rfl

@[simp] theorem mreqLargeRangeEndpointData_rhsUpperString :
    mreqLargeRangeEndpointData.rhsUpperString = mreqLargeRangeRhsUpperString := by
  rfl

/--
The endpoint certificate source path is the recorded pivot Appendix A artifact.
-/
theorem mreqLargeRangeProofSourcePath_eq :
    mreqLargeRangeProofSourcePath = "data/pivot/pivotA_proof_Y0=30000.txt" := by
  rfl

/--
The endpoint certificate source digest is the recorded SHA256 of the artifact
currently referenced by the data layer.
-/
theorem mreqLargeRangeProofSourceSha256_eq :
    mreqLargeRangeProofSourceSha256 =
      "10e522653f533488d6676d19c0c570501c2907eb81a3038542c3071e5365e3f4" := by
  rfl

end Pivot
end Lehmer