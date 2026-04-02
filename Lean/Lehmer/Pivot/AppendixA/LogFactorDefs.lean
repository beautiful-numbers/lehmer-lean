-- FILE: Lean/Lehmer/Pivot/AppendixA/LogFactorDefs.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Analysis.SpecialFunctions.Log.Basic : def thm
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixA.IntervalProduct : def thm
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lehmer.Prelude
import Lehmer.Pivot.AppendixA.IntervalProduct

open scoped BigOperators
open Finset
open Real

namespace Lehmer
namespace Pivot
namespace AppendixA

noncomputable section

/-!
# Appendix A log-factor definitions

This file contains only the structural log/product layer for the Appendix A
prime interval product.

Important scope:
* no analytic bound `≤ log 2` yet;
* no `mreq` yet;
* only the exact log-sum attached to `intervalPrimeProd`.
-/

/--
The Appendix A log-factor attached to a natural prime input `p`.
-/
def appendixALogFactor (p : ℕ) : ℝ :=
  Real.log ((p : ℝ) / ((p : ℝ) - 1))

/--
The log-sum over primes in the discrete Appendix A interval `[y, xA y]`.
-/
def intervalLogSum (y : ℕ) : ℝ :=
  ∑ p in primesInIcc y (xA y), appendixALogFactor p

@[simp] theorem appendixALogFactor_def (p : ℕ) :
    appendixALogFactor p = Real.log ((p : ℝ) / ((p : ℝ) - 1)) := rfl

@[simp] theorem intervalLogSum_def (y : ℕ) :
    intervalLogSum y =
      ∑ p in primesInIcc y (xA y), appendixALogFactor p := rfl

/--
For a prime `p`, the Appendix A log-factor is the log of the real-cast pivot
factor.
-/
theorem appendixALogFactor_eq_log_cast_pivotFactor
    {p : ℕ} (hp : Nat.Prime p) :
    appendixALogFactor p = Real.log (((pivotFactor p : ℚ) : ℝ)) := by
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp.two_le
  rw [appendixALogFactor, pivotFactor]
  norm_num [Nat.cast_sub hp1]

/--
For a prime `p`, the real-cast pivot factor is positive.
-/
theorem cast_pivotFactor_pos_of_prime
    {p : ℕ} (hp : Nat.Prime p) :
    0 < (((pivotFactor p : ℚ) : ℝ)) := by
  exact_mod_cast (pivotFactor_pos_of_prime hp)

/--
The Appendix A log-factor is well-defined on primes as the log of a positive
quantity.
-/
theorem appendixALogFactor_eq_log_pos
    {p : ℕ} (hp : Nat.Prime p) :
    appendixALogFactor p = Real.log (((pivotFactor p : ℚ) : ℝ)) ∧
      0 < (((pivotFactor p : ℚ) : ℝ)) := by
  exact ⟨appendixALogFactor_eq_log_cast_pivotFactor hp, cast_pivotFactor_pos_of_prime hp⟩

/--
The interval log-sum is the log-sum over real-cast pivot factors.
-/
theorem intervalLogSum_eq_sum_log_cast_pivotFactor
    (y : ℕ) :
    intervalLogSum y =
      ∑ p in primesInIcc y (xA y), Real.log (((pivotFactor p : ℚ) : ℝ)) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact appendixALogFactor_eq_log_cast_pivotFactor (prime_of_mem_primesInIcc hp)

/--
The total interval product is positive.
-/
theorem intervalPrimeProd_pos
    (y : ℕ) :
    0 < intervalPrimeProd y := by
  classical
  unfold intervalPrimeProd
  exact Finset.prod_pos (fun p hp => pivotFactor_pos_of_prime (prime_of_mem_primesInIcc hp))

/--
The log of the total interval product is the interval log-sum.
-/
theorem log_intervalPrimeProd_eq_intervalLogSum
    (y : ℕ) :
    Real.log (intervalPrimeProd y) = intervalLogSum y := by
  classical
  rw [intervalPrimeProd, intervalLogSum_eq_sum_log_cast_pivotFactor]
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    rw [appendixALogFactor_eq_log_cast_pivotFactor (prime_of_mem_primesInIcc hp)]
  · intro p hp
    exact cast_pivotFactor_pos_of_prime (prime_of_mem_primesInIcc hp)

/--
Equivalent rewritten form of the previous theorem.
-/
theorem intervalLogSum_eq_log_intervalPrimeProd
    (y : ℕ) :
    intervalLogSum y = Real.log (intervalPrimeProd y) := by
  symm
  exact log_intervalPrimeProd_eq_intervalLogSum y

/--
Exponentiating the interval log-sum recovers the total interval product.
-/
theorem exp_intervalLogSum_eq_intervalPrimeProd
    (y : ℕ) :
    Real.exp (intervalLogSum y) = intervalPrimeProd y := by
  rw [intervalLogSum_eq_log_intervalPrimeProd]
  exact Real.exp_log (intervalPrimeProd_pos y)

end

end AppendixA
end Pivot
end Lehmer