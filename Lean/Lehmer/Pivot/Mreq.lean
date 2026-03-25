-- FILE: Lean/Lehmer/Pivot/Mreq.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm

namespace Lehmer
namespace Pivot

open Classical

/--
Conditional threshold definition.

If there exists some index `m` with `UBm y m > 2`, then `mreq y` is the least
such index. Otherwise, we set `mreq y = 0`.

This avoids any global analytic existence theorem at the definition level while
still recovering the exact minimal-threshold behavior whenever a witness exists.
-/
noncomputable def mreq (y : ℕ) : ℕ :=
  if h : ∃ m : ℕ, (2 : ℚ) < UBm y m then
    Nat.find h
  else
    0

/--
If the threshold-exceeding set is nonempty, `mreq y` is exactly its `Nat.find`.
-/
theorem mreq_eq_find_of_exists {y : ℕ} (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    mreq y = Nat.find h := by
  unfold mreq
  simp [h]

/--
If no index exceeds the threshold, then `mreq y = 0`.
-/
theorem mreq_eq_zero_of_not_exists {y : ℕ}
    (h : ¬ ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    mreq y = 0 := by
  unfold mreq
  simp [h]

/--
At the defining threshold, the envelope exceeds `2`, provided existence holds.
-/
theorem UBm_gt_two_at_mreq_of_exists {y : ℕ}
    (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    (2 : ℚ) < UBm y (mreq y) := by
  rw [mreq_eq_find_of_exists h]
  exact Nat.find_spec h

/--
Below the threshold, the envelope stays at or below `2`.
This is globally valid for the conditional definition.
-/
theorem UBm_le_two_before_mreq {y m : ℕ} (hm : m < mreq y) :
    UBm y m ≤ 2 := by
  by_cases h : ∃ k : ℕ, (2 : ℚ) < UBm y k
  · rw [mreq_eq_find_of_exists h] at hm
    exact le_of_not_gt (Nat.find_min h hm)
  · rw [mreq_eq_zero_of_not_exists h] at hm
    omega

/--
Equivalent negated-strict form below the threshold.
-/
theorem UBm_not_gt_two_before_mreq {y m : ℕ} (hm : m < mreq y) :
    ¬ (2 : ℚ) < UBm y m := by
  exact not_lt_of_ge (UBm_le_two_before_mreq hm)

/--
Minimality: any witness `m` with `UBm y m > 2` dominates `mreq y`.
-/
theorem mreq_le_of_UBm_gt_two {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    mreq y ≤ m := by
  have h : ∃ k : ℕ, (2 : ℚ) < UBm y k := ⟨m, hm⟩
  rw [mreq_eq_find_of_exists h]
  exact Nat.find_min' h hm

/--
Re-export of minimality under the same name.
-/
theorem mreq_minimal {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    mreq y ≤ m := by
  exact mreq_le_of_UBm_gt_two hm

/--
Bundled threshold characterization, assuming existence.
-/
theorem mreq_spec_of_exists {y : ℕ}
    (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    ((2 : ℚ) < UBm y (mreq y)) ∧
      (∀ m < mreq y, UBm y m ≤ 2) := by
  refine ⟨UBm_gt_two_at_mreq_of_exists h, ?_⟩
  intro m hm
  exact UBm_le_two_before_mreq hm

/--
Uniqueness from threshold attainment plus minimality below.
-/
theorem mreq_unique {y k : ℕ}
    (hk1 : (2 : ℚ) < UBm y k)
    (hk2 : ∀ m < k, UBm y m ≤ 2) :
    mreq y = k := by
  apply le_antisymm
  · exact mreq_le_of_UBm_gt_two hk1
  · by_contra hlt
    have hm : mreq y < k := Nat.lt_of_not_ge hlt
    have hle : UBm y (mreq y) ≤ 2 := hk2 (mreq y) hm
    have hgt : (2 : ℚ) < UBm y (mreq y) := by
      have hex : ∃ m : ℕ, (2 : ℚ) < UBm y m := ⟨k, hk1⟩
      exact UBm_gt_two_at_mreq_of_exists hex
    exact (not_lt_of_ge hle) hgt

/--
Convenient re-export of the below-threshold bound.
-/
theorem UBm_le_two_of_lt_mreq {y m : ℕ} (hm : m < mreq y) :
    UBm y m ≤ 2 := by
  exact UBm_le_two_before_mreq hm

/--
The threshold is nonnegative.
-/
theorem mreq_nonneg (y : ℕ) : 0 ≤ mreq y := by
  exact Nat.zero_le _

/--
If a threshold witness exists, then `mreq y` is positive.
-/
theorem mreq_pos_of_exists {y : ℕ}
    (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    0 < mreq y := by
  have hgt : (2 : ℚ) < UBm y (mreq y) := UBm_gt_two_at_mreq_of_exists h
  have hm0 : mreq y ≠ 0 := by
    intro hm
    rw [hm, UBm_zero] at hgt
    norm_num at hgt
  exact Nat.pos_iff_ne_zero.mpr hm0

end Pivot
end Lehmer