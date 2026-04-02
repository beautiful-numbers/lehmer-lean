-- FILE: Lean/Lehmer/Pivot/AppendixA/UBmRangeProduct.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

noncomputable section

/-!
# Appendix A general `UBm` range-product form

This file contains only the final structural facts actually needed from the
general finite-product presentation of `UBm`.

Important scope:
* no interval indexing yet;
* no analytic estimates yet;
* no `mreq` yet.
-/

/-- Rational range product attached to the first `m` primes `≥ y`. -/
def ubmRangeProdQ (y m : ℕ) : ℚ :=
  ∏ k in Finset.range m, pivotFactor (nthPrimeFrom y k)

/-- Real-cast range product attached to the first `m` primes `≥ y`. -/
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
Recursive finite-product form of `UBm`.
-/
theorem UBm_eq_ubmRangeProdQ
    (y m : ℕ) :
    UBm y m = ubmRangeProdQ y m := by
  induction m generalizing y with
  | zero =>
      simp [UBm_zero, ubmRangeProdQ]
  | succ m ih =>
      rw [UBm_succ, ih]
      rw [ubmRangeProdQ, prod_range_succ_shift]
      simp [nthPrimeFrom_zero, nthPrimeFrom_succ]

/--
Real-cast finite-product form of `UBm`.
-/
theorem UBm_cast_eq_ubmRangeProdR
    (y m : ℕ) :
    (((UBm y m : ℚ) : ℝ)) = ubmRangeProdR y m := by
  rw [UBm_eq_ubmRangeProdQ]
  induction m with
  | zero =>
      simp [ubmRangeProdQ, ubmRangeProdR]
  | succ m ih =>
      simp [ubmRangeProdQ, ubmRangeProdR, Finset.prod_range_succ, ih]

/--
Membership in `firstPrimesFrom y m` is equivalent to being one of the indexed
values `nthPrimeFrom y k` with `k < m`.
-/
theorem mem_firstPrimesFrom_iff
    {y m p : ℕ} :
    p ∈ firstPrimesFrom y m ↔ ∃ k < m, nthPrimeFrom y k = p := by
  classical
  constructor
  · intro hp
    unfold firstPrimesFrom at hp
    rcases Finset.mem_image.mp hp with ⟨k, hk, hk'⟩
    exact ⟨k, Finset.mem_range.mp hk, hk'⟩
  · rintro ⟨k, hk, rfl⟩
    unfold firstPrimesFrom
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩

/--
Every member of `firstPrimesFrom y m` is prime and at least `y`.
-/
theorem mem_firstPrimesFrom_prime_ge
    {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    Nat.Prime p ∧ y ≤ p := by
  exact ⟨mem_firstPrimesFrom_prime hp, mem_firstPrimesFrom_ge hp⟩

/--
The rational range product is positive.
-/
theorem ubmRangeProdQ_pos
    (y m : ℕ) :
    0 < ubmRangeProdQ y m := by
  rw [← UBm_eq_ubmRangeProdQ]
  exact UBm_pos y m

end

end AppendixA
end Pivot
end Lehmer