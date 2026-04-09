-- FILE: Lean/Lehmer/Pivot/UBmGrowth.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.PrimeReciprocalTailBridge : thm

FILE ROLE
This file contains the intrinsic growth layer for `UBm` used before defining
`mreq`.

Paper-facing public API:
- for fixed `y`, `m ↦ UBm y m` is strictly increasing;
- for fixed `y`, `UBm y m` eventually exceeds `2`.
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.PrimeReciprocalTailBridge

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot

noncomputable section

/--
For a prime input, the pivot factor is strictly greater than `1`.
-/
theorem one_lt_pivotFactor_of_prime {p : ℕ} (hp : Nat.Prime p) :
    1 < pivotFactor p := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [pivotFactor_eq_one_add_inv hp2]
  have hden_pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by
    have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp2
    rw [Nat.cast_sub hp1]
    exact sub_pos.mpr (by exact_mod_cast hp2)
  have hinv_pos : (0 : ℚ) < 1 / (((p - 1 : ℕ) : ℚ)) := by
    exact one_div_pos.mpr hden_pos
  linarith

/--
For fixed `y`, the pivot envelope is strictly increasing in the index.
This is the body-text monotonicity used before defining `mreq`.
-/
theorem UBm_strictMono (y : ℕ) : StrictMono (UBm y) := by
  refine strictMono_nat_of_lt_succ ?_
  intro m
  have hfac : 1 < pivotFactor (py0 y m) := by
    exact one_lt_pivotFactor_of_prime (py0_prime y m)
  have hpos : 0 < UBm y m := UBm_pos y m
  have hmul : UBm y m * 1 < UBm y m * pivotFactor (py0 y m) := by
    exact mul_lt_mul_of_pos_left hfac hpos
  simpa [UBm_succ] using hmul

/--
The reciprocal-prime partial sum along `py0` is bounded above by `UBm`.
-/
theorem prime_harmonic_le_UBm
    (y m : ℕ) :
    ∑ k in Finset.range m, (1 : ℚ) / (py0 y k : ℚ) ≤ UBm y m := by
  induction m with
  | zero =>
      simp [UBm_zero]
  | succ m ih =>
      have hp : Nat.Prime (py0 y m) := py0_prime y m
      have hp2 : 2 ≤ py0 y m := hp.two_le
      have hUBm_one : (1 : ℚ) ≤ UBm y m := by
        have hmono : UBm y 0 ≤ UBm y m := by
          exact UBm_le_of_le (y := y) (m := 0) (n := m) (Nat.zero_le m)
        simpa [UBm_zero] using hmono
      have hden_pos : (0 : ℚ) < (((py0 y m - 1 : ℕ) : ℚ)) := by
        have hp1 : 1 ≤ py0 y m := le_trans (by decide : 1 ≤ 2) hp2
        rw [Nat.cast_sub hp1]
        exact sub_pos.mpr (by exact_mod_cast hp2)
      have hrecip :
          (1 : ℚ) / (py0 y m : ℚ) ≤ 1 / (((py0 y m - 1 : ℕ) : ℚ)) := by
        have hle : (((py0 y m - 1 : ℕ) : ℚ)) ≤ (py0 y m : ℚ) := by
          exact_mod_cast Nat.sub_le (py0 y m) 1
        exact one_div_le_one_div_of_le hden_pos hle
      have hmul :
          (1 : ℚ) / (py0 y m : ℚ) ≤
            UBm y m * (1 / (((py0 y m - 1 : ℕ) : ℚ))) := by
        have hnonneg : 0 ≤ (1 / (((py0 y m - 1 : ℕ) : ℚ))) := by
          exact le_of_lt (one_div_pos.mpr hden_pos)
        have hmul' :
            1 * (1 / (((py0 y m - 1 : ℕ) : ℚ))) ≤
              UBm y m * (1 / (((py0 y m - 1 : ℕ) : ℚ))) := by
          exact mul_le_mul_of_nonneg_right hUBm_one hnonneg
        exact le_trans (by simpa using hrecip) hmul'
      calc
        ∑ k in Finset.range (m + 1), (1 : ℚ) / (py0 y k : ℚ)
            = (∑ k in Finset.range m, (1 : ℚ) / (py0 y k : ℚ)) + (1 : ℚ) / (py0 y m : ℚ) := by
                rw [Finset.sum_range_succ]
        _ ≤ UBm y m + UBm y m * (1 / (((py0 y m - 1 : ℕ) : ℚ))) := by
              exact add_le_add ih hmul
        _ = UBm y m * (1 + 1 / (((py0 y m - 1 : ℕ) : ℚ))) := by ring
        _ = UBm y (m + 1) := by
              rw [UBm_succ, pivotFactor_eq_one_add_inv hp2]

/--
Cast bridge for the reciprocal-prime partial sums along `py0`.
-/
private theorem cast_sum_prime_harmonic
    (y m : ℕ) :
    (((∑ k in Finset.range m, (1 : ℚ) / (py0 y k : ℚ)) : ℚ) : ℝ) =
      ∑ k in Finset.range m, (1 : ℝ) / (py0 y k : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      simp [Finset.sum_range_succ, ih]

/--
Real-cast form of the harmonic lower bound on `UBm`.
-/
theorem prime_harmonic_le_cast_UBm
    (y m : ℕ) :
    ∑ k in Finset.range m, (1 : ℝ) / (py0 y k : ℝ) ≤ ((UBm y m : ℚ) : ℝ) := by
  have hq : ∑ k in Finset.range m, (1 : ℚ) / (py0 y k : ℚ) ≤ UBm y m :=
    prime_harmonic_le_UBm y m
  have hq' :
      (((∑ k in Finset.range m, (1 : ℚ) / (py0 y k : ℚ)) : ℚ) : ℝ) ≤
        ((UBm y m : ℚ) : ℝ) := by
    exact_mod_cast hq
  rw [cast_sum_prime_harmonic] at hq'
  exact hq'

/--
For fixed `y`, `UBm y m` is unbounded above along the index parameter.
-/
theorem UBm_unbounded
    (y : ℕ) :
    ∀ B : ℝ, ∃ m : ℕ, B ≤ ((UBm y m : ℚ) : ℝ) := by
  intro B
  rcases prime_harmonic_unbounded_from_y y B with ⟨m, hm⟩
  exact ⟨m, le_trans hm (prime_harmonic_le_cast_UBm y m)⟩

/--
For fixed `y`, the pivot envelope eventually exceeds `2`.

This is the intrinsic crossing-existence statement used to justify the
definition of `mreq`.
-/
theorem exists_UBm_gt_two
    (y : ℕ) :
    ∃ m : ℕ, (2 : ℚ) < UBm y m := by
  rcases UBm_unbounded y 3 with ⟨m, hm⟩
  have hreal : (2 : ℝ) < ((UBm y m : ℚ) : ℝ) := by
    exact lt_of_lt_of_le (by norm_num) hm
  have hq : (2 : ℚ) < UBm y m := by
    exact_mod_cast hreal
  exact ⟨m, hq⟩

end

end Pivot