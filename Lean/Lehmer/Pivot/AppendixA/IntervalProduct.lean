-- FILE: Lean/Lehmer/Pivot/AppendixA/IntervalProduct.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixA.UBmRangeProduct : def thm
- Lehmer.Pivot.AppendixA.IntervalUpperBound : thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
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

This file contains the structural product domination step used in Appendix A.

Core output:
* if the prime-count bound on `[y, xA y]` is available, then
  `UBm y m ≤ intervalPrimeProd y`.

Scope:
* no analytic large-range estimate yet;
* no unconditional `≤ 2` theorem yet;
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
      ∏ p in primesInIcc y (xA y), pivotFactor p := rfl

/--
`UBm y m` written as the finite product over the first `m` primes at least `y`.
-/
theorem UBm_eq_firstPrimesFrom_prod
    (y m : ℕ) :
    UBm y m = ∏ p in firstPrimesFrom y m, pivotFactor p := by
  rw [UBm_eq_UB_firstPrimesFrom, UB]

/--
Under the paper-facing prime-count bound, every member of `firstPrimesFrom y m`
lies in the prime interval `[y, xA y]`.
-/
theorem firstPrimesFrom_subset_primesInIcc_of_primePi_bound
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ primePi (xA y) - primePi y + 1) :
    firstPrimesFrom y m ⊆ primesInIcc y (xA y) := by
  intro p hp
  have hIcc : y ≤ p ∧ p ≤ xA y :=
    firstPrimesFrom_subset_Icc_y_xA_of_primePi_bound hy hyx hcount p hp
  exact mem_primesInIcc_iff.mpr ⟨hIcc.1, hIcc.2, mem_firstPrimesFrom_prime hp⟩

/--
Structural domination of `UBm y m` by the total interval product over primes in
`[y, xA y]`, in the paper-facing prime-count form.
-/
theorem UBm_le_intervalPrimeProd_of_primePi_bound
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ primePi (xA y) - primePi y + 1) :
    UBm y m ≤ intervalPrimeProd y := by
  classical
  rw [UBm_eq_firstPrimesFrom_prod, intervalPrimeProd]
  exact Finset.prod_le_prod_of_subset_of_one_le
    (firstPrimesFrom_subset_primesInIcc_of_primePi_bound hy hyx hcount)
    (by
      intro p hp hpnot
      exact one_le_pivotFactor_of_prime (prime_of_mem_primesInIcc hp))

/--
Equivalent structural domination form using the interval cardinal explicitly.
-/
theorem UBm_le_intervalPrimeProd_of_card_primesInIcc
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ (primesInIcc y (xA y)).card) :
    UBm y m ≤ intervalPrimeProd y := by
  have hcount' : m ≤ primePi (xA y) - primePi y + 1 := by
    rw [card_primesInIcc_eq_primePi_sub_primePi_add_one hy hyx] at hcount
    exact hcount
  exact UBm_le_intervalPrimeProd_of_primePi_bound hy hyx hcount'

/--
Conditional Appendix A consequence:
if one additionally knows that the total interval product is at most `2`, then
`UBm y m ≤ 2`.
-/
theorem UBm_le_two_of_intervalPrimeProd_le_two
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ primePi (xA y) - primePi y + 1)
    (htwo : intervalPrimeProd y ≤ 2) :
    UBm y m ≤ 2 := by
  exact le_trans
    (UBm_le_intervalPrimeProd_of_primePi_bound hy hyx hcount)
    htwo

/--
Real-cast form of the previous conditional theorem.
-/
theorem UBm_cast_le_two_of_intervalPrimeProd_le_two
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ primePi (xA y) - primePi y + 1)
    (htwo : intervalPrimeProd y ≤ 2) :
    ((UBm y m : ℚ) : ℝ) ≤ 2 := by
  exact_mod_cast (UBm_le_two_of_intervalPrimeProd_le_two hy hyx hcount htwo)

end

end AppendixA
end Pivot
end Lehmer