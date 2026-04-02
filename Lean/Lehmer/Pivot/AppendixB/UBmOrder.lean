-- FILE: Lean/Lehmer/Pivot/UBmOrder.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.Mreq : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.Mreq

namespace Lehmer
namespace Pivot

/--
For a prime input, the pivot factor is at least `1`.
-/
theorem one_le_pivotFactor_of_prime {p : ℕ} (hp : Nat.Prime p) :
    1 ≤ pivotFactor p := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [pivotFactor_eq_one_add_inv hp2]
  have hden_pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by
    have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp2
    rw [Nat.cast_sub hp1]
    exact sub_pos.mpr (by exact_mod_cast hp2)
  have hinv_nonneg : (0 : ℚ) ≤ 1 / (((p - 1 : ℕ) : ℚ)) := by
    exact inv_nonneg.mpr (le_of_lt hden_pos)
  linarith

/--
Successor monotonicity of `UBm` in the index parameter.
-/
theorem UBm_le_succ (y m : ℕ) :
    UBm y m ≤ UBm y (m + 1) := by
  induction m generalizing y with
  | zero =>
      rw [UBm_zero, UBm_succ, UBm_zero]
      have hhead : 1 ≤ pivotFactor (nextPrimeGe y) := by
        exact one_le_pivotFactor_of_prime (nextPrimeGe_prime y)
      simpa
  | succ m ih =>
      rw [UBm_succ, UBm_succ]
      exact mul_le_mul_of_nonneg_left
        (ih (nextPrimeGe y + 1))
        (pivotFactor_nonneg_of_prime (nextPrimeGe_prime y))

/--
`UBm y` is monotone in the index parameter `m`.
-/
theorem UBm_monotone (y : ℕ) :
    Monotone (UBm y) := by
  refine monotone_nat_of_le_succ ?_
  intro m
  exact UBm_le_succ y m

/--
A convenient monotonicity re-export.
-/
theorem UBm_le_of_le {y m n : ℕ} (hmn : m ≤ n) :
    UBm y m ≤ UBm y n := by
  exact UBm_monotone y hmn

/--
If a crossing exists, then the defining threshold `mreq y` is itself a
crossing index.
-/
theorem UBm_crossing_at_mreq_of_exists {y : ℕ}
    (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    (2 : ℚ) < UBm y (mreq y) := by
  exact UBm_gt_two_at_mreq_of_exists h

/--
If `mreq y` is positive, then some crossing index exists.
-/
theorem UBm_crossing_of_mreq_pos {y : ℕ}
    (hm : 0 < mreq y) :
    ∃ m : ℕ, (2 : ℚ) < UBm y m := by
  by_contra hnot
  have hm0 : mreq y = 0 := mreq_eq_zero_of_not_exists hnot
  omega

/--
Crossing existence is equivalent to positivity of `mreq y`.
-/
theorem UBm_crossing_iff_mreq_pos (y : ℕ) :
    (∃ m : ℕ, (2 : ℚ) < UBm y m) ↔ 0 < mreq y := by
  constructor
  · intro h
    exact mreq_pos_of_exists h
  · intro hm
    exact UBm_crossing_of_mreq_pos hm

end Pivot
end Lehmer