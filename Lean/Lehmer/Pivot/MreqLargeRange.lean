-- FILE: Lean/Lehmer/Pivot/MreqLargeRange.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.LargeRangeExplicit : def thm
- Lehmer.Data.Pivot.Log2Enclosure : def

FILE ROLE
This file is strictly endpoint-certificate-facing.

It packages only the explicit Appendix A endpoint certificate data recorded at
the pivot threshold `Y0`, together with provenance strings and the local
certificate proposition already exposed by the lower data layer.

Paper-facing note:
- In the paper, the public large-range pivot facade appears higher up as the
  effective lower bound on `mreq(y)` in the large range.
- This file does NOT yet provide that public paper-facing large-range theorem.
- This file does NOT propagate anything uniformly in `y`.
- This file does NOT expose a bridge from an analytic barrier to `mreq`.
- This file does NOT state any Case B or no-crossing consequence.

Accordingly, this file should be read as:
- endpoint-only,
- certificate-local,
- provenance-oriented,
- not a propagated theorem.
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.LargeRangeExplicit
import Lehmer.Data.Pivot.Log2Enclosure

namespace Lehmer
namespace Pivot

/--
Endpoint threshold used by the explicit Appendix A large-range check.

This constant is endpoint-only: it records the anchor value at which the
explicit certificate is packaged, and should not be read as a propagated
large-range theorem.
-/
def mreqLargeRangeY0 : ℕ :=
  largeRangeEndpointY0

/--
Endpoint lower index
`m = floor(C1 * y^2 / log y)`
recorded in the explicit Appendix A endpoint certificate.

This is local certificate data only; no global statement is made here.
-/
def mreqLargeRangeEndpointM : ℕ :=
  largeRangeEndpointM

/--
Endpoint upper index
`n = m + y - 1`
recorded in the explicit Appendix A endpoint certificate.

This is local certificate data only; no global statement is made here.
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

This is provenance data only.
-/
def mreqLargeRangeProofSourcePath : String :=
  Lehmer.Data.Pivot.pivotAProofSourcePath

/--
Raw source digest for the explicit endpoint certificate artifact.

This is provenance data only.
-/
def mreqLargeRangeProofSourceSha256 : String :=
  Lehmer.Data.Pivot.pivotAProofSourceSha256

/--
Raw lower enclosure string for `log 2` recorded in the endpoint certificate
data.

This is stored exactly as certificate-facing payload and is not interpreted here
as a propagated theorem.
-/
def mreqLargeRangeLn2LowerString : String :=
  Lehmer.Data.Pivot.pivotA_ln2_lb

/--
Raw upper enclosure string for the endpoint RHS quantity recorded in the
certificate data.

This is stored exactly as certificate-facing payload and is not interpreted here
as a propagated theorem.
-/
def mreqLargeRangeRhsUpperString : String :=
  Lehmer.Data.Pivot.pivotA_rhs_upper

/--
Certificate-level proposition exported by this file.

At the current stage, this is exactly the local endpoint certificate proposition
already internalized in the lower data layer.

Important:
- this is endpoint-only;
- this is not a propagated theorem for all `y ≥ Y0`;
- this is not yet the public paper-facing large-range pivot bound.
-/
def MreqLargeRangeEndpointCertified : Prop :=
  LargeRangeEndpointCertified

/--
The endpoint certificate is available.

This theorem should be read only as local availability of the endpoint
certificate, not as a propagated large-range statement.
-/
theorem mreqLargeRangeEndpointCertified :
    MreqLargeRangeEndpointCertified := by
  exact largeRangeEndpointCertified

/--
The explicit endpoint certificate is anchored at `Y0 = 30000`.

This is an endpoint-local identification only.
-/
theorem mreqLargeRange_endpoint_at_Y0 :
    mreqLargeRangeY0 = 30000 := by
  simp [mreqLargeRangeY0]

/--
The explicit endpoint certificate uses the lower index `m = 87302`.

This is endpoint-local certificate data only.
-/
theorem mreqLargeRange_endpoint_M :
    mreqLargeRangeEndpointM = 87302 := by
  simp [mreqLargeRangeEndpointM]

/--
The explicit endpoint certificate uses the upper index `n = 117301`.

This is endpoint-local certificate data only.
-/
theorem mreqLargeRange_endpoint_N :
    mreqLargeRangeEndpointN = 117301 := by
  simp [mreqLargeRangeEndpointN]

/--
Packaged endpoint-local data for the large-range pivot certificate.

This structure is intentionally certificate-facing and endpoint-only.
It records exactly the local constants and the availability of the certified
endpoint check, but does not assert:
- any propagated theorem on all `y ≥ Y0`,
- any bridge from an analytic barrier to `mreq`,
- any public paper-facing lower bound on `mreq(y)`,
- any Case B / no-crossing consequence.
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

This package is endpoint-only and should not be overread as a global theorem.
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

This is provenance only.
-/
theorem mreqLargeRangeProofSourcePath_eq :
    mreqLargeRangeProofSourcePath = "data/pivot/pivotA_proof_Y0=30000.txt" := by
  rfl

/--
The endpoint certificate source digest is the recorded SHA256 of the artifact
currently referenced by the data layer.

This is provenance only.
-/
theorem mreqLargeRangeProofSourceSha256_eq :
    mreqLargeRangeProofSourceSha256 =
      "10e522653f533488d6676d19c0c570501c2907eb81a3038542c3071e5365e3f4" := by
  rfl

end Pivot
end Lehmer