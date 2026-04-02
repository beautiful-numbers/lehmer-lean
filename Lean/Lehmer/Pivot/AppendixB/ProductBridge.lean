-- FILE: Lean/Lehmer/Pivot/AppendixB/ProductBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixB.BlockBounds : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.AppendixB.BlockBounds

open scoped BigOperators
open Finset
open Real

namespace Lehmer
namespace Pivot

noncomputable section

/-!
# Appendix B product bridge

This file proves the clean bridge

`sum of logs  ->  product over the same block`

for the Appendix B endpoint pipeline.

Important scope:
* this file does **not** identify the block product with `UBm`;
* it does **not** mention `mreq`;
* it only turns a block log bound into a block product bound.

The positivity needed for `log` / `exp` is now derived from the endpoint
prime-indexing data, rather than stored as an extra field.
-/

/-! ## Block product attached to the same consecutive prime block -/

/--
The block product attached to the consecutive prime block `[i,j)`:
`∏ p_t / (p_t - 1)`.
-/
def appendixBBlockProd (primeAt : ℕ → ℕ) (i j : ℕ) : ℝ :=
  ∏ t in Finset.Icc i (j - 1),
    ((primeAt t : ℝ) / ((primeAt t : ℝ) - 1))

/-! ## Positivity of the prime ratio -/

/--
If `1 < p`, then `(p : ℝ) / ((p : ℝ) - 1)` is positive.
-/
theorem appendixBPrimeRatio_pos_of_one_lt {p : ℕ} (hp : 1 < p) :
    0 < ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp
  have hnum : 0 < (p : ℝ) := by
    linarith
  have hden : 0 < (p : ℝ) - 1 := by
    linarith
  exact div_pos hnum hden

/--
Under the blockwise hypothesis `1 < primeAt t`, the whole block product is
positive.
-/
theorem appendixBBlockProd_pos
    {primeAt : ℕ → ℕ} {i j : ℕ}
    (hgt : ∀ t ∈ Finset.Icc i (j - 1), 1 < primeAt t) :
    0 < appendixBBlockProd primeAt i j := by
  classical
  unfold appendixBBlockProd
  exact Finset.prod_pos (fun t ht => appendixBPrimeRatio_pos_of_one_lt (hgt t ht))

/-! ## Log of product = sum of logs on the block -/

/--
On a block where all entries satisfy `1 < primeAt t`, the log of the block
product is exactly the block log sum.
-/
theorem log_appendixBBlockProd_eq_blockLogSum
    {primeAt : ℕ → ℕ} {i j : ℕ}
    (hgt : ∀ t ∈ Finset.Icc i (j - 1), 1 < primeAt t) :
    Real.log (appendixBBlockProd primeAt i j) = appendixBBlockLogSum primeAt i j := by
  classical
  unfold appendixBBlockProd appendixBBlockLogSum appendixBLogFactor
  rw [Real.log_prod]
  · rfl
  · intro t ht
    exact appendixBPrimeRatio_pos_of_one_lt (hgt t ht)

/--
Equivalent rewritten form of the previous theorem.
-/
theorem appendixBBlockLogSum_eq_log_appendixBBlockProd
    {primeAt : ℕ → ℕ} {i j : ℕ}
    (hgt : ∀ t ∈ Finset.Icc i (j - 1), 1 < primeAt t) :
    appendixBBlockLogSum primeAt i j = Real.log (appendixBBlockProd primeAt i j) := by
  symm
  exact log_appendixBBlockProd_eq_blockLogSum hgt

/-! ## Exponentiating the block log sum recovers the block product -/

/--
Exponentiating the block log sum recovers the block product.
-/
theorem exp_appendixBBlockLogSum_eq_blockProd
    {primeAt : ℕ → ℕ} {i j : ℕ}
    (hgt : ∀ t ∈ Finset.Icc i (j - 1), 1 < primeAt t) :
    Real.exp (appendixBBlockLogSum primeAt i j) = appendixBBlockProd primeAt i j := by
  rw [appendixBBlockLogSum_eq_log_appendixBBlockProd hgt]
  exact Real.exp_log (appendixBBlockProd_pos hgt)

/-! ## Sum-of-logs bound -> product bound -/

/--
If the block log sum is at most `log 2`, then the block product is at most `2`.
-/
theorem appendixBBlockProd_le_two_of_logsum_le_log2
    {primeAt : ℕ → ℕ} {i j : ℕ}
    (hgt : ∀ t ∈ Finset.Icc i (j - 1), 1 < primeAt t)
    (hlog : appendixBBlockLogSum primeAt i j ≤ Real.log 2) :
    appendixBBlockProd primeAt i j ≤ 2 := by
  have hexp : Real.exp (appendixBBlockLogSum primeAt i j) ≤ Real.exp (Real.log 2) := by
    exact Real.exp_le_exp.mpr hlog
  rw [exp_appendixBBlockLogSum_eq_blockProd hgt] at hexp
  have h2 : Real.exp (Real.log 2) = 2 := by
    have hpos : (0 : ℝ) < 2 := by norm_num
    simpa using Real.exp_log hpos
  simpa [h2] using hexp

/--
If the block log sum is strictly below `log 2`, then the block product is
strictly below `2`.
-/
theorem appendixBBlockProd_lt_two_of_logsum_lt_log2
    {primeAt : ℕ → ℕ} {i j : ℕ}
    (hgt : ∀ t ∈ Finset.Icc i (j - 1), 1 < primeAt t)
    (hlog : appendixBBlockLogSum primeAt i j < Real.log 2) :
    appendixBBlockProd primeAt i j < 2 := by
  have hexp : Real.exp (appendixBBlockLogSum primeAt i j) < Real.exp (Real.log 2) := by
    exact Real.exp_lt_exp.mpr hlog
  rw [exp_appendixBBlockLogSum_eq_blockProd hgt] at hexp
  have h2 : Real.exp (Real.log 2) = 2 := by
    have hpos : (0 : ℝ) < 2 := by norm_num
    simpa using Real.exp_log hpos
  simpa [h2] using hexp

/-! ## Endpoint-specialized packaging -/

/--
Endpoint-specialized data for the product bridge:
* block-bounds data.

Positivity of the endpoint primes is derived from the endpoint prime-indexing
data and is not stored as an extra field.
-/
structure AppendixBEndpointProductBridgeData where
  blockData : AppendixBEndpointBlockBoundsData

namespace AppendixBEndpointProductBridgeData

/--
Every prime indexed inside the endpoint block is prime.
-/
theorem endpoint_primeAt_prime
    (D : AppendixBEndpointProductBridgeData)
    {t : ℕ}
    (ht : t ∈ Finset.Icc D.blockData.endpoint.i (D.blockData.endpoint.j - 1)) :
    Nat.Prime (D.blockData.endpoint.primeAt t) := by
  rcases D.blockData.endpoint with ⟨primeAt, i, j, y, m, hy, hm, hj, hindex⟩
  have hti : i ≤ t := (Finset.mem_Icc.mp ht).1
  have htj : t ≤ j - 1 := (Finset.mem_Icc.mp ht).2
  rw [hj] at htj
  have hk : t - i < m := by
    omega
  have hrepr : t = i + (t - i) := by
    omega
  rw [hrepr, hindex (t - i) hk]
  exact nthPrimeFrom_prime y (t - i)

/--
Every prime indexed inside the endpoint block is strictly greater than `1`.
-/
theorem endpoint_one_lt_prime
    (D : AppendixBEndpointProductBridgeData)
    {t : ℕ}
    (ht : t ∈ Finset.Icc D.blockData.endpoint.i (D.blockData.endpoint.j - 1)) :
    1 < D.blockData.endpoint.primeAt t := by
  have hprime : Nat.Prime (D.blockData.endpoint.primeAt t) :=
    D.endpoint_primeAt_prime ht
  exact lt_of_lt_of_le (by decide : 1 < 2) hprime.two_le

/--
The endpoint block product.
-/
def endpointProd (D : AppendixBEndpointProductBridgeData) : ℝ :=
  appendixBBlockProd D.blockData.endpoint.primeAt
    D.blockData.endpoint.i D.blockData.endpoint.j

/--
The endpoint block log sum.
-/
def endpointLogSum (D : AppendixBEndpointProductBridgeData) : ℝ :=
  appendixBBlockLogSum D.blockData.endpoint.primeAt
    D.blockData.endpoint.i D.blockData.endpoint.j

/--
The endpoint block product is positive.
-/
theorem endpointProd_pos
    (D : AppendixBEndpointProductBridgeData) :
    0 < D.endpointProd := by
  exact appendixBBlockProd_pos (fun t ht => D.endpoint_one_lt_prime ht)

/--
Exponentiating the endpoint log sum recovers the endpoint product.
-/
theorem exp_endpointLogSum_eq_endpointProd
    (D : AppendixBEndpointProductBridgeData) :
    Real.exp D.endpointLogSum = D.endpointProd := by
  exact exp_appendixBBlockLogSum_eq_blockProd (fun t ht => D.endpoint_one_lt_prime ht)

/--
If the endpoint log sum is at most `log 2`, then the endpoint product is at
most `2`.
-/
theorem endpointProd_le_two_of_logsum_le_log2
    (D : AppendixBEndpointProductBridgeData)
    (hlog : D.endpointLogSum ≤ Real.log 2) :
    D.endpointProd ≤ 2 := by
  exact appendixBBlockProd_le_two_of_logsum_le_log2
    (fun t ht => D.endpoint_one_lt_prime ht) hlog

/--
If the endpoint log sum is strictly below `log 2`, then the endpoint product is
strictly below `2`.
-/
theorem endpointProd_lt_two_of_logsum_lt_log2
    (D : AppendixBEndpointProductBridgeData)
    (hlog : D.endpointLogSum < Real.log 2) :
    D.endpointProd < 2 := by
  exact appendixBBlockProd_lt_two_of_logsum_lt_log2
    (fun t ht => D.endpoint_one_lt_prime ht) hlog

/--
Convenient mixed bridge:
if the endpoint upper block bound is at most `log 2`, then the endpoint product
is at most `2`.
-/
theorem endpointProd_le_two_of_upper_le_log2
    (D : AppendixBEndpointProductBridgeData)
    (hupper : (((AppendixBIntegerEncodings.UP60 D.blockData.enc
          D.blockData.endpoint.primeAt
          D.blockData.endpoint.i
          D.blockData.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ)) ≤ Real.log 2) :
    D.endpointProd ≤ 2 := by
  have hlogsum : D.endpointLogSum ≤ Real.log 2 := by
    exact le_trans (D.blockData.endpoint_upper) hupper
  exact D.endpointProd_le_two_of_logsum_le_log2 hlogsum

end AppendixBEndpointProductBridgeData

end

end Pivot
end Lehmer