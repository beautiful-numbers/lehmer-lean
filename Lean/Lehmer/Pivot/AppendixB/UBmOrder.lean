-- FILE: Lean/Lehmer/Pivot/UBmOrder.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm

namespace Lehmer
namespace Pivot

open scoped BigOperators

/-
This file contains only the order/completeness interface for the paper-facing
prime enumeration underlying `UBm`.

Scope:
* no `mreq`;
* no crossing;
* no analytic Appendix A estimates;
* only the exact relationship between `firstPrimesFrom y m` and the ordered
  prime sequence `py0 y k`.
-/

/--
Any member of `firstPrimesFrom y (k+1)` is at most the last indexed prime
`py0 y k`.
-/
theorem le_py0_of_mem_firstPrimesFrom
    {y k p : ℕ}
    (hp : p ∈ firstPrimesFrom y (k + 1)) :
    p ≤ py0 y k := by
  classical
  rcases (mem_firstPrimesFrom_iff).mp hp with ⟨i, hi, rfl⟩
  have hik : i ≤ k := Nat.lt_succ_iff.mp hi
  exact (py0_strictMono y).monotone hik

/--
Base case of completeness of the prime enumeration:
a prime `p` with `y ≤ p ≤ py0 y 0` must equal `py0 y 0`.
-/
theorem prime_ge_le_py0_zero_eq
    {y p : ℕ}
    (hp : Nat.Prime p) (hy : y ≤ p) (hpy : p ≤ py0 y 0) :
    p = py0 y 0 := by
  have hmin : nextPrimeGe y ≤ p := nextPrimeGe_le_of_prime_ge hp hy
  have hlow : py0 y 0 ≤ p := by simpa [py0] using hmin
  exact le_antisymm hpy hlow

/--
Base membership result:
a prime `p` with `y ≤ p ≤ py0 y 0` belongs to the first prime block.
-/
theorem prime_ge_le_py0_zero_mem_firstPrimesFrom
    {y p : ℕ}
    (hp : Nat.Prime p) (hy : y ≤ p) (hpy : p ≤ py0 y 0) :
    p ∈ firstPrimesFrom y 1 := by
  have heq : p = py0 y 0 := prime_ge_le_py0_zero_eq hp hy hpy
  exact (mem_firstPrimesFrom_iff).mpr ⟨0, by simp, heq.symm⟩

/--
Completeness of the prime enumeration:
every prime `p` with `y ≤ p ≤ py0 y k` occurs among the first `k+1` primes
at least `y`.
-/
theorem prime_ge_le_py0_mem_firstPrimesFrom
    {y k p : ℕ}
    (hp : Nat.Prime p) (hy : y ≤ p) (hpy : p ≤ py0 y k) :
    p ∈ firstPrimesFrom y (k + 1) := by
  induction k generalizing y with
  | zero =>
      exact prime_ge_le_py0_zero_mem_firstPrimesFrom hp hy hpy
  | succ k ih =>
      by_cases hhead : p = py0 y 0
      · exact (mem_firstPrimesFrom_iff).mpr ⟨0, by simp, hhead.symm⟩
      · have hmin : py0 y 0 ≤ p := by
          simpa [py0] using nextPrimeGe_le_of_prime_ge hp hy
        have hlt : py0 y 0 < p := lt_of_le_of_ne hmin hhead
        have htail_lb : py0 y 0 + 1 ≤ p := Nat.succ_le_of_lt hlt
        have htail_ub : p ≤ py0 (py0 y 0 + 1) k := by
          simpa [py0, py0_succ] using hpy
        have htail_mem :
            p ∈ firstPrimesFrom (py0 y 0 + 1) (k + 1) := by
          exact ih hp htail_lb htail_ub
        rcases (mem_firstPrimesFrom_iff).mp htail_mem with ⟨i, hi, hip⟩
        refine (mem_firstPrimesFrom_iff).mpr ?_
        refine ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
        simpa [py0, py0_succ] using hip

/--
Paper-facing characterization of the first `k+1` primes at least `y`.
-/
theorem mem_firstPrimesFrom_iff_prime_ge_le_py0
    {y k p : ℕ} :
    p ∈ firstPrimesFrom y (k + 1) ↔ Nat.Prime p ∧ y ≤ p ∧ p ≤ py0 y k := by
  constructor
  · intro hp
    exact ⟨mem_firstPrimesFrom_prime hp, mem_firstPrimesFrom_ge hp,
      le_py0_of_mem_firstPrimesFrom hp⟩
  · rintro ⟨hp, hy, hpy⟩
    exact prime_ge_le_py0_mem_firstPrimesFrom hp hy hpy

end Pivot
end Lehmer