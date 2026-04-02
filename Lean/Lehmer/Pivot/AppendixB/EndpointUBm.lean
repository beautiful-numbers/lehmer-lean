-- FILE: Lean/Lehmer/Pivot/AppendixB/EndpointUBm.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixB.EndpointUBmBridge : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.AppendixB.EndpointUBmBridge

open scoped BigOperators
open Finset
open Real

namespace Lehmer
namespace Pivot

noncomputable section

/-!
# Appendix B endpoint -> UBm consequences

This file is intentionally endpoint-local.

It packages the endpoint-local consequences on `UBm` that follow from the
proved mathematical indexing bridge

`endpoint block product = (UBm(y,m) : ℚ : ℝ)`

established in `EndpointUBmBridge.lean`.

Important scope:
* this file does **not** mention `mreq`;
* it does **not** prove the prime-indexing identification globally;
* it only derives the downstream `UBm` consequences from the proved endpoint
  bridge.
-/

namespace AppendixBEndpointUBmData

/--
Rewritten form of the endpoint-local identification with `UBm`.
-/
theorem UBm_cast_eq_endpointProd
    (D : AppendixBEndpointUBmData)
    (hbridge :
      D.productData.endpointProd = (((UBm D.y D.m : ℚ) : ℝ))) :
    (((UBm D.y D.m : ℚ) : ℝ)) = D.productData.endpointProd := by
  symm
  exact hbridge

/--
The endpoint-local `UBm` value is positive, once the indexing bridge is known.
-/
theorem UBm_cast_pos
    (D : AppendixBEndpointUBmData)
    (hbridge :
      D.productData.endpointProd = (((UBm D.y D.m : ℚ) : ℝ))) :
    0 < (((UBm D.y D.m : ℚ) : ℝ)) := by
  rw [D.UBm_cast_eq_endpointProd hbridge]
  exact D.productData.endpointProd_pos

/--
If the endpoint log sum is at most `log 2`, then the endpoint-local `UBm`
value is at most `2`.
-/
theorem UBm_cast_le_two_of_logsum_le_log2
    (D : AppendixBEndpointUBmData)
    (hbridge :
      D.productData.endpointProd = (((UBm D.y D.m : ℚ) : ℝ)))
    (hlog : D.productData.endpointLogSum ≤ Real.log 2) :
    (((UBm D.y D.m : ℚ) : ℝ)) ≤ 2 := by
  rw [D.UBm_cast_eq_endpointProd hbridge]
  exact D.productData.endpointProd_le_two_of_logsum_le_log2 hlog

/--
If the endpoint log sum is strictly below `log 2`, then the endpoint-local
`UBm` value is strictly below `2`.
-/
theorem UBm_cast_lt_two_of_logsum_lt_log2
    (D : AppendixBEndpointUBmData)
    (hbridge :
      D.productData.endpointProd = (((UBm D.y D.m : ℚ) : ℝ)))
    (hlog : D.productData.endpointLogSum < Real.log 2) :
    (((UBm D.y D.m : ℚ) : ℝ)) < 2 := by
  rw [D.UBm_cast_eq_endpointProd hbridge]
  exact D.productData.endpointProd_lt_two_of_logsum_lt_log2 hlog

/--
If the endpoint upper block bound is at most `log 2`, then the endpoint-local
`UBm` value is at most `2`.
-/
theorem UBm_cast_le_two_of_upper_le_log2
    (D : AppendixBEndpointUBmData)
    (hbridge :
      D.productData.endpointProd = (((UBm D.y D.m : ℚ) : ℝ)))
    (hupper : (((AppendixBIntegerEncodings.UP60 D.productData.blockData.enc
          D.productData.blockData.endpoint.primeAt
          D.productData.blockData.endpoint.i
          D.productData.blockData.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ)) ≤ Real.log 2) :
    (((UBm D.y D.m : ℚ) : ℝ)) ≤ 2 := by
  rw [D.UBm_cast_eq_endpointProd hbridge]
  exact D.productData.endpointProd_le_two_of_upper_le_log2 hupper

/--
Endpoint-local version specialized to the canonical large-range endpoint
parameter `Y0`.
-/
theorem UBm_cast_le_two_at_Y0_of_y_eq_Y0
    (D : AppendixBEndpointUBmData)
    (hbridge :
      D.productData.endpointProd = (((UBm D.y D.m : ℚ) : ℝ)))
    (hy0 : D.y = Y0)
    (hupper : (((AppendixBIntegerEncodings.UP60 D.productData.blockData.enc
          D.productData.blockData.endpoint.primeAt
          D.productData.blockData.endpoint.i
          D.productData.blockData.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ)) ≤ Real.log 2) :
    (((UBm Y0 D.m : ℚ) : ℝ)) ≤ 2 := by
  subst hy0
  exact D.UBm_cast_le_two_of_upper_le_log2 hbridge hupper

end AppendixBEndpointUBmData

namespace CanonicalAppendixBEndpointUBmData

/--
Canonical endpoint-local bridge imported from `EndpointUBmBridge.lean`.
-/
theorem endpointProd_eq_UBm_cast
    (D : CanonicalAppendixBEndpointUBmData) :
    D.data.productData.endpointProd =
      (((UBm D.data.y D.data.m : ℚ) : ℝ)) := by
  exact appendixB_endpointProd_eq_UBm_cast D

/--
Canonical endpoint-local `UBm` theorem:
if the endpoint upper block bound is at most `log 2`, then
`((UBm Y0 appendixBEndpointM : ℚ) : ℝ) ≤ 2`.
-/
theorem UBm_cast_le_two_of_upper_le_log2
    (D : CanonicalAppendixBEndpointUBmData)
    (hupper : (((AppendixBIntegerEncodings.UP60 D.data.productData.blockData.enc
          D.data.productData.blockData.endpoint.primeAt
          D.data.productData.blockData.endpoint.i
          D.data.productData.blockData.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ)) ≤ Real.log 2) :
    (((UBm appendixBEndpointY0 appendixBEndpointM : ℚ) : ℝ)) ≤ 2 := by
  rw [← D.hy0, ← D.hm0]
  exact D.data.UBm_cast_le_two_of_upper_le_log2 (D.endpointProd_eq_UBm_cast) hupper

/--
The same theorem rewritten at the global endpoint constants
`Y0 = 30000` and `m = 87302`.
-/
theorem UBm_cast_le_two_at_global_endpoint_of_upper_le_log2
    (D : CanonicalAppendixBEndpointUBmData)
    (hupper : (((AppendixBIntegerEncodings.UP60 D.data.productData.blockData.enc
          D.data.productData.blockData.endpoint.primeAt
          D.data.productData.blockData.endpoint.i
          D.data.productData.blockData.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ)) ≤ Real.log 2) :
    (((UBm Y0 largeRangeEndpointM : ℚ) : ℝ)) ≤ 2 := by
  simpa [appendixBEndpointY0, appendixBEndpointM] using
    D.UBm_cast_le_two_of_upper_le_log2 hupper

end CanonicalAppendixBEndpointUBmData

end

end Pivot
end Lehmer