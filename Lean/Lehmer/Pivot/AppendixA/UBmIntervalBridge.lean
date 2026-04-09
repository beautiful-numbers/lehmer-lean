-- FILE: Lean/Lehmer/Pivot/AppendixA/UBmIntervalBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBmOrder : def thm
- Lehmer.Pivot.AppendixA.UBmRangeProduct : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBmOrder
import Lehmer.Pivot.AppendixA.UBmRangeProduct

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

noncomputable section

/-!
# Appendix A interval bridge for `UBm`

This file bridges the finite-product presentation of `UBm` with the paper-facing
prime-interval product indexed by the last prime `py y k`.

Scope:
* interval product bridge only;
* no analytic bounds yet;
* no `mreq` yet.
-/

/-- Rational interval prime product on `[y, x]`. -/
def intervalPrimeProdQ (y x : ℕ) : ℚ :=
  ∏ p in ((Finset.Icc y x).filter Nat.Prime), pivotFactor p

/-- Real-cast interval prime product on `[y, x]`. -/
def intervalPrimeProdR (y x : ℕ) : ℝ :=
  ∏ p in ((Finset.Icc y x).filter Nat.Prime), ((pivotFactor p : ℚ) : ℝ)

/--
Membership in the filtered prime interval `[y, py y k]`.
-/
theorem mem_intervalPrimeProdQ_iff
    {y k p : ℕ} :
    p ∈ ((Finset.Icc y (py y k)).filter Nat.Prime) ↔
      Nat.Prime p ∧ y ≤ p ∧ p ≤ py y k := by
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hpIcc, hpPrime⟩
    rw [Finset.mem_Icc] at hpIcc
    exact ⟨hpPrime, hpIcc.1, hpIcc.2⟩
  · rintro ⟨hpPrime, hpy, hpx⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpy, hpx⟩, hpPrime⟩

/--
The filtered prime interval `[y, py y k]` is exactly the finite set of the first
`k+1` primes at least `y`.
-/
theorem filter_Icc_eq_firstPrimesFrom
    (y k : ℕ) :
    ((Finset.Icc y (py y k)).filter Nat.Prime) = firstPrimesFrom y (k + 1) := by
  classical
  ext p
  rw [mem_intervalPrimeProdQ_iff, mem_firstPrimesFrom_iff_prime_ge_le_py]

/--
Rational interval-product form of `UBm` at the endpoint `py y k`.
-/
theorem UBm_eq_intervalPrimeProdQ_last
    (y k : ℕ) :
    UBm y (k + 1) = intervalPrimeProdQ y (py y k) := by
  rw [intervalPrimeProdQ, UBm_eq_UB_firstPrimesFrom]
  rw [filter_Icc_eq_firstPrimesFrom]

/--
Real-cast interval-product form of `UBm` at the endpoint `py y k`.
-/
theorem UBm_cast_eq_intervalPrimeProdR_last
    (y k : ℕ) :
    ((UBm y (k + 1) : ℚ) : ℝ) = intervalPrimeProdR y (py y k) := by
  rw [UBm_eq_intervalPrimeProdQ_last]
  induction h : ((Finset.Icc y (py y k)).filter Nat.Prime) using Finset.induction_on with
  | empty =>
      simp [intervalPrimeProdQ, intervalPrimeProdR]
  | @insert a s ha ih =>
      simp [intervalPrimeProdQ, intervalPrimeProdR, ha, ih]

/--
The interval product is positive.
-/
theorem intervalPrimeProdQ_pos
    (y x : ℕ) :
    0 < intervalPrimeProdQ y x := by
  unfold intervalPrimeProdQ
  classical
  induction ((Finset.Icc y x).filter Nat.Prime) using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have ha_prime : Nat.Prime a := by
        have : a ∈ (Finset.Icc y x).filter Nat.Prime := by simp [ha]
        exact (Finset.mem_filter.mp this).2
      rw [Finset.prod_insert ha]
      exact mul_pos (pivotFactor_pos_of_prime ha_prime) ih

/--
The real interval product is positive.
-/
theorem intervalPrimeProdR_pos
    (y x : ℕ) :
    0 < intervalPrimeProdR y x := by
  have hq : 0 < intervalPrimeProdQ y x := intervalPrimeProdQ_pos y x
  unfold intervalPrimeProdR intervalPrimeProdQ at *
  exact_mod_cast hq

end

end AppendixA
end Pivot
end Lehmer