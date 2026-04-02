-- FILE: Lean/Lehmer/Pivot/AppendixB/EndpointUBmBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixB.EndpointUBmBase : def
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.AppendixB.EndpointUBmBase

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot

noncomputable section

/-!
# Appendix B endpoint -> UBm indexing bridge

This file proves the endpoint-local indexing bridge between the explicit
endpoint block product and the pivot product `UBm`.

Important type note:
* the endpoint block product in the Appendix B product layer is valued in `ℝ`;
* `UBm` is valued in `ℚ`.

Accordingly, the bridge proved here is the mathematically correct one:
the endpoint block product equals the real cast of `UBm`.
-/

/-- Real block product over `nthPrimeFrom y` on `Finset.range m`. -/
def ubmRangeProdR (y m : ℕ) : ℝ :=
  ∏ k in Finset.range m, (((pivotFactor (nthPrimeFrom y k) : ℚ) : ℝ))

/--
Head-tail decomposition of a product on `Finset.range (m+1)`.
-/
theorem prod_range_succ_shift
    {α : Type*} [CommMonoid α] (f : ℕ → α) (m : ℕ) :
    (∏ k in Finset.range (m + 1), f k) =
      f 0 * ∏ k in Finset.range m, f (k + 1) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
      simp [mul_assoc, mul_left_comm, mul_comm]

/--
The real cast of `pivotFactor p` is the usual real ratio `p/(p-1)`.
-/
theorem cast_pivotFactor_eq_real_ratio {p : ℕ} (hp1 : 1 ≤ p) :
    (((pivotFactor p : ℚ) : ℝ)) = (p : ℝ) / ((p : ℝ) - 1) := by
  rw [pivotFactor]
  norm_num [Nat.cast_sub hp1]

/--
Real-cast form of the `UBm` product as the explicit product over
`nthPrimeFrom y k`, `k < m`.
-/
theorem UBm_cast_eq_ubmRangeProdR (y m : ℕ) :
    (((UBm y m : ℚ) : ℝ)) = ubmRangeProdR y m := by
  induction m generalizing y with
  | zero =>
      simp [UBm_zero, ubmRangeProdR]
  | succ m ih =>
      rw [UBm_succ, Rat.cast_mul, ih]
      rw [ubmRangeProdR, prod_range_succ_shift]
      congr 1
      · simp [nthPrimeFrom_zero]
      · apply Finset.prod_congr rfl
        intro k hk
        simp [nthPrimeFrom_succ]

/--
The explicit endpoint block product reindexed as the explicit `nthPrimeFrom`
product over `Finset.range m`.
-/
theorem endpointProd_eq_ubmRangeProdR
    (D : CanonicalAppendixBEndpointUBmData) :
    D.data.productData.endpointProd = ubmRangeProdR D.data.y D.data.m := by
  classical
  rcases D with ⟨data, hy0, hm0⟩
  rcases data with ⟨productData⟩
  rcases productData with ⟨blockData, one_lt_prime⟩
  rcases blockData with ⟨enc, termCert, endpoint⟩
  rcases endpoint with ⟨primeAt, i, j, y, m, hy, hm, hj, hindex⟩

  simp [AppendixBEndpointProductBridgeData.endpointProd,
    appendixBBlockProd, ubmRangeProdR]

  rw [hj]

  have hset :
      Finset.Icc i (i + m - 1) = (Finset.range m).image (fun k => i + k) := by
    ext t
    constructor
    · intro ht
      rw [Finset.mem_image]
      refine ⟨t - i, ?_, ?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · omega
    · intro ht
      rcases Finset.mem_image.mp ht with ⟨k, hk, rfl⟩
      rw [Finset.mem_Icc]
      constructor
      · exact Nat.le_add_right i k
      · have hk' : k < m := Finset.mem_range.mp hk
        omega

  rw [hset]
  rw [Finset.prod_image]
  · refine Finset.prod_congr rfl ?_
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    rw [hindex k hklt]
    have hp1 : 1 ≤ nthPrimeFrom y k := by
      exact le_trans (by decide : 1 ≤ 2) (nthPrimeFrom_prime y k).two_le
    rw [cast_pivotFactor_eq_real_ratio hp1]
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

/--
Endpoint-local bridge: the explicit endpoint product equals the real cast of
`UBm y m`.
-/
theorem appendixB_endpointProd_eq_UBm_cast
    (D : CanonicalAppendixBEndpointUBmData) :
    D.data.productData.endpointProd = (((UBm D.data.y D.data.m : ℚ) : ℝ)) := by
  rw [endpointProd_eq_ubmRangeProdR, ← UBm_cast_eq_ubmRangeProdR]

end

end Pivot
end Lehmer