-- FILE: Lean/Lehmer/Pivot/AppendixB/EndpointMreq.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBmOrder : def thm
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pivot.AppendixB.EndpointUBm : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBmOrder
import Lehmer.Pivot.Mreq
import Lehmer.Pivot.AppendixB.EndpointUBm

namespace Lehmer
namespace Pivot

/-!
# Appendix B endpoint -> mreq bridge

This file is the final endpoint-local bridge in the Appendix B pipeline.

Its role is deliberately narrow:

* input: an endpoint-local theorem of the form `((UBm Y0 M : ℚ) : ℝ) ≤ 2`,
* plus the remaining UBm-side fact:
  - existence of a crossing index,
* output: the local pivot consequence `M < mreq Y0`.

Important scope:
* this file does **not** reprove the theory of `mreq`;
* it does **not** introduce any new axioms;
* it only packages the endpoint-local deduction from the `UBm` endpoint theorem.
-/

/--
Convert a real-cast upper bound on `UBm` back to the rational upper bound.
-/
theorem UBm_le_two_of_cast_le_two
    {y m : ℕ}
    (h : (((UBm y m : ℚ) : ℝ)) ≤ 2) :
    UBm y m ≤ 2 := by
  exact_mod_cast h

/--
Endpoint-local abstract bridge from a `UBm` endpoint bound to the strict lower
bound on `mreq`.

The proof uses:
* existence of some crossing index (`∃ k, UBm Y0 k > 2`);
* monotonicity of `UBm Y0`, now imported from `UBmOrder.lean`.
-/
theorem appendixB_endpointM_lt_mreq_of_UBm_le_two
    (hex : ∃ k : ℕ, UBm appendixBEndpointY0 k > 2)
    (hubm : UBm appendixBEndpointY0 appendixBEndpointM ≤ 2) :
    appendixBEndpointM < mreq appendixBEndpointY0 := by
  by_contra hnot
  have hmreq_le : mreq appendixBEndpointY0 ≤ appendixBEndpointM := by
    exact Nat.not_lt.mp hnot
  have hmreq_gt_two : UBm appendixBEndpointY0 (mreq appendixBEndpointY0) > 2 := by
    exact UBm_gt_two_at_mreq_of_exists hex
  have hle_chain :
      UBm appendixBEndpointY0 (mreq appendixBEndpointY0)
        ≤ UBm appendixBEndpointY0 appendixBEndpointM := by
    exact UBm_monotone appendixBEndpointY0 hmreq_le
  have hmreq_le_two :
      UBm appendixBEndpointY0 (mreq appendixBEndpointY0) ≤ 2 := by
    exact le_trans hle_chain hubm
  exact (not_lt_of_ge hmreq_le_two) hmreq_gt_two

/--
Same endpoint-local result, rewritten at the global constants `Y0` and
`largeRangeEndpointM`.
-/
theorem appendixB_global_endpointM_lt_mreq_of_UBm_le_two
    (hex : ∃ k : ℕ, UBm Y0 k > 2)
    (hubm : UBm Y0 largeRangeEndpointM ≤ 2) :
    largeRangeEndpointM < mreq Y0 := by
  simpa [appendixBEndpointY0, appendixBEndpointM] using
    appendixB_endpointM_lt_mreq_of_UBm_le_two hex hubm

/--
Canonical endpoint-local package for the final Appendix B bridge toward `mreq`.

This structure records:
* the canonical endpoint-local `UBm` package;
* existence of a UBm crossing at `Y0`.

Monotonicity is no longer stored here, since it is provided by `UBmOrder.lean`.
-/
structure CanonicalAppendixBEndpointMreqData where
  ubmData : CanonicalAppendixBEndpointUBmData
  existsCrossingY0 : ∃ k : ℕ, UBm appendixBEndpointY0 k > 2

namespace CanonicalAppendixBEndpointMreqData

/--
Endpoint-local Appendix B consequence on `mreq`:
if the canonical endpoint upper block bound implies the endpoint-local real-cast
`UBm` bound, then the endpoint index `M` lies strictly below `mreq(Y0)`.
-/
theorem endpointM_lt_mreq_of_upper_le_log2
    (D : CanonicalAppendixBEndpointMreqData)
    (hupper : (((AppendixBIntegerEncodings.UP60 D.ubmData.data.productData.blockData.enc
          D.ubmData.data.productData.blockData.endpoint.primeAt
          D.ubmData.data.productData.blockData.endpoint.i
          D.ubmData.data.productData.blockData.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ)) ≤ Real.log 2) :
    appendixBEndpointM < mreq appendixBEndpointY0 := by
  have hubm_cast :
      (((UBm appendixBEndpointY0 appendixBEndpointM : ℚ) : ℝ)) ≤ 2 := by
    exact D.ubmData.UBm_cast_le_two_of_upper_le_log2 hupper
  have hubm :
      UBm appendixBEndpointY0 appendixBEndpointM ≤ 2 := by
    exact UBm_le_two_of_cast_le_two hubm_cast
  exact appendixB_endpointM_lt_mreq_of_UBm_le_two
    D.existsCrossingY0
    hubm

/--
The same result rewritten at the global endpoint constants.
-/
theorem global_endpointM_lt_mreq_of_upper_le_log2
    (D : CanonicalAppendixBEndpointMreqData)
    (hupper : (((AppendixBIntegerEncodings.UP60 D.ubmData.data.productData.blockData.enc
          D.ubmData.data.productData.blockData.endpoint.primeAt
          D.ubmData.data.productData.blockData.endpoint.i
          D.ubmData.data.productData.blockData.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ)) ≤ Real.log 2) :
    largeRangeEndpointM < mreq Y0 := by
  simpa [appendixBEndpointY0, appendixBEndpointM] using
    D.endpointM_lt_mreq_of_upper_le_log2 hupper

end CanonicalAppendixBEndpointMreqData

end Pivot
end Lehmer