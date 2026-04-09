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
# Appendix A finite-product form of `UBm`

This file isolates the paper-facing finite-product presentation of the pivot
envelope `UBm`.

Scope:
* finite products only;
* no interval bridge yet;
* no analytic estimates yet;
* no `mreq` yet.
-/

/-- Rational finite product attached to the first `m` primes `≥ y`. -/
def ubmRangeProdQ (y m : ℕ) : ℚ :=
  ∏ k in Finset.range m, pivotFactor (py0 y k)

/-- Real-cast finite product attached to the first `m` primes `≥ y`. -/
def ubmRangeProdR (y m : ℕ) : ℝ :=
  ∏ k in Finset.range m, (((pivotFactor (py0 y k) : ℚ) : ℝ))

/--
`UBm` is exactly the rational finite product over the first `m` primes `≥ y`.
-/
theorem UBm_eq_ubmRangeProdQ
    (y m : ℕ) :
    UBm y m = ubmRangeProdQ y m := by
  rfl

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
Equivalent product formula using the finite set `firstPrimesFrom y m`.
-/
theorem UBm_eq_UB_firstPrimesFrom
    (y m : ℕ) :
    UBm y m = UB (firstPrimesFrom y m) := by
  exact Pivot.UBm_eq_UB_firstPrimesFrom y m

/--
Membership in `firstPrimesFrom y m` is equivalent to being one of the indexed
values `py0 y k` with `k < m`.
-/
theorem mem_firstPrimesFrom_iff
    {y m p : ℕ} :
    p ∈ firstPrimesFrom y m ↔ ∃ k < m, py0 y k = p := by
  exact Pivot.mem_firstPrimesFrom_iff

/--
Every member of `firstPrimesFrom y m` is prime and at least `y`.
-/
theorem mem_firstPrimesFrom_prime_ge
    {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    Nat.Prime p ∧ y ≤ p := by
  exact ⟨mem_firstPrimesFrom_prime hp, mem_firstPrimesFrom_ge hp⟩

/--
The rational finite product is positive.
-/
theorem ubmRangeProdQ_pos
    (y m : ℕ) :
    0 < ubmRangeProdQ y m := by
  rw [← UBm_eq_ubmRangeProdQ]
  exact UBm_pos y m

/--
The real finite product is positive.
-/
theorem ubmRangeProdR_pos
    (y m : ℕ) :
    0 < ubmRangeProdR y m := by
  have hq : 0 < ubmRangeProdQ y m := ubmRangeProdQ_pos y m
  rw [← UBm_cast_eq_ubmRangeProdR]
  exact_mod_cast hq

end

end AppendixA
end Pivot
end Lehmer