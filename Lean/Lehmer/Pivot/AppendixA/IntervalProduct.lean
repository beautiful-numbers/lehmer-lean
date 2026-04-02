-- FILE: Lean/Lehmer/Pivot/AppendixA/IntervalProduct.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.UBmOrder : thm
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.UBmRangeProduct : def thm
- Lehmer.Pivot.AppendixA.IntervalUpperBound : thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.UBmOrder
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.UBmRangeProduct
import Lehmer.Pivot.AppendixA.IntervalUpperBound
import Lehmer.Pivot.AppendixA.PrimeCountDefs

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

noncomputable section

/-!
# Appendix A interval product bridge

This file contains the actual structural bridge from:
* the finite-product form of `UBm`,
* the interval upper bound placing the first `m` primes `≥ y` inside `[y, xA y]`,

to domination by the total pivot-factor product over primes in `[y, xA y]`.

Important scope:
* no analytic proof yet that the interval product is `≤ 2`;
* no `mreq` yet.
-/

/--
The total pivot-factor product over primes in the discrete Appendix A interval
`[y, xA y]`.
-/
def intervalPrimeProd (y : ℕ) : ℚ :=
  ∏ p in primesInIcc y (xA y), pivotFactor p

@[simp] theorem intervalPrimeProd_def (y : ℕ) :
    intervalPrimeProd y =
      ∏ p in primesInIcc y (xA y), pivotFactor p := by
  rfl

/--
`UBm y m` written as the product of `pivotFactor` over `firstPrimesFrom y m`.
-/
theorem UBm_eq_firstPrimesFrom_prod
    (y m : ℕ) :
    UBm y m = ∏ p in firstPrimesFrom y m, pivotFactor p := by
  classical
  rw [UBm_eq_ubmRangeProdQ, ubmRangeProdQ, firstPrimesFrom]
  rw [Finset.prod_image]
  · rfl
  · intro a _ha b _hb hab
    exact (nthPrimeFrom_strictMono y).injective hab

/--
Under the interval upper bound, every member of `firstPrimesFrom y m` belongs to
the prime interval `[y, xA y]`.
-/
theorem firstPrimesFrom_subset_primesInIcc_of_HasIntervalUpperBound
    {y m : ℕ}
    (hup : HasIntervalUpperBound y m) :
    firstPrimesFrom y m ⊆ primesInIcc y (xA y) := by
  intro p hp
  rcases (mem_firstPrimesFrom_iff).mp hp with ⟨k, hk, rfl⟩
  exact mem_primesInIcc_iff.mpr
    ⟨nthPrimeFrom_ge y k, hup k hk, nthPrimeFrom_prime y k⟩

/--
Domination of `UBm y m` by the total interval product over primes in
`[y, xA y]`.
-/
theorem UBm_le_intervalPrimeProd_of_HasIntervalUpperBound
    {y m : ℕ}
    (hup : HasIntervalUpperBound y m) :
    UBm y m ≤ intervalPrimeProd y := by
  classical
  rw [UBm_eq_firstPrimesFrom_prod, intervalPrimeProd]
  exact Finset.prod_le_prod_of_subset_of_one_le
    (firstPrimesFrom_subset_primesInIcc_of_HasIntervalUpperBound hup)
    (by
      intro p hp hpnot
      exact one_le_pivotFactor_of_prime (prime_of_mem_primesInIcc hp))

/--
If the total interval product is at most `2`, then `UBm y m ≤ 2`.
-/
theorem UBm_le_two_of_intervalPrimeProd_le_two
    {y m : ℕ}
    (hup : HasIntervalUpperBound y m)
    (htwo : intervalPrimeProd y ≤ 2) :
    UBm y m ≤ 2 := by
  exact le_trans
    (UBm_le_intervalPrimeProd_of_HasIntervalUpperBound hup)
    htwo

/--
Real-cast form of the previous theorem.
-/
theorem UBm_cast_le_two_of_intervalPrimeProd_le_two
    {y m : ℕ}
    (hup : HasIntervalUpperBound y m)
    (htwo : intervalPrimeProd y ≤ 2) :
    (((UBm y m : ℚ) : ℝ)) ≤ 2 := by
  exact_mod_cast (UBm_le_two_of_intervalPrimeProd_le_two hup htwo)

end

end AppendixA
end Pivot
end Lehmer