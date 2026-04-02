-- FILE: Lean/Lehmer/Pivot/AppendixB/EndpointUBmBase.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixB.ProductBridge : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AppendixB.ProductBridge

open scoped BigOperators
open Finset
open Real

namespace Lehmer
namespace Pivot

noncomputable section

/-!
# Appendix B endpoint -> UBm base data

This file contains only the common endpoint-local data structures used by the
Appendix B `UBm` bridge and consequence layers.

It is intentionally kept free of any bridge theorem so that:
* `EndpointUBmBridge.lean` can import it without circularity;
* `EndpointUBm.lean` can later import the bridge file and consume the actual
  bridge theorem directly.
-/

/--
Endpoint-local data coming from the previous Appendix B layers.

At this stage, this file only depends on the endpoint-local product bridge.
-/
structure AppendixBEndpointUBmData where
  productData : AppendixBEndpointProductBridgeData

namespace AppendixBEndpointUBmData

/--
The endpoint-local pivot parameter `y`.
-/
def y (D : AppendixBEndpointUBmData) : ℕ :=
  D.productData.blockData.endpoint.y

/--
The endpoint-local pivot parameter `m`.
-/
def m (D : AppendixBEndpointUBmData) : ℕ :=
  D.productData.blockData.endpoint.m

@[simp] theorem y_eq
    (D : AppendixBEndpointUBmData) :
    D.y = D.productData.blockData.endpoint.y := by
  rfl

@[simp] theorem m_eq
    (D : AppendixBEndpointUBmData) :
    D.m = D.productData.blockData.endpoint.m := by
  rfl

/--
The endpoint block starts at `y`.
-/
theorem endpoint_startPrime_eq_y
    (D : AppendixBEndpointUBmData) :
    D.productData.blockData.endpoint.toPrimeBlock.startPrime = D.y := by
  exact D.productData.blockData.endpoint_startPrime_eq_y

/--
The endpoint block length is `m`.
-/
theorem endpoint_length_eq_m
    (D : AppendixBEndpointUBmData) :
    D.productData.blockData.endpoint.toPrimeBlock.length = D.m := by
  exact D.productData.blockData.endpoint_length_eq_m

end AppendixBEndpointUBmData

/--
Canonical endpoint-local package specialized to the canonical Appendix B
endpoint data.
-/
structure CanonicalAppendixBEndpointUBmData where
  data : AppendixBEndpointUBmData
  hy0 : data.y = appendixBEndpointY0
  hm0 : data.m = appendixBEndpointM

namespace CanonicalAppendixBEndpointUBmData

@[simp] theorem y_eq_Y0
    (D : CanonicalAppendixBEndpointUBmData) :
    D.data.y = appendixBEndpointY0 := by
  exact D.hy0

@[simp] theorem m_eq_endpointM
    (D : CanonicalAppendixBEndpointUBmData) :
    D.data.m = appendixBEndpointM := by
  exact D.hm0

/--
The endpoint block starts at `Y0`.
-/
theorem endpoint_startPrime_eq_Y0
    (D : CanonicalAppendixBEndpointUBmData) :
    D.data.productData.blockData.endpoint.toPrimeBlock.startPrime = appendixBEndpointY0 := by
  rw [D.data.endpoint_startPrime_eq_y, D.hy0]

/--
The endpoint block length is `appendixBEndpointM`.
-/
theorem endpoint_length_eq_endpointM
    (D : CanonicalAppendixBEndpointUBmData) :
    D.data.productData.blockData.endpoint.toPrimeBlock.length = appendixBEndpointM := by
  rw [D.data.endpoint_length_eq_m, D.hm0]

end CanonicalAppendixBEndpointUBmData

end

end Pivot
end Lehmer