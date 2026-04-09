-- FILE: Lean/Lehmer/Pivot/Mreq.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.UBmGrowth : thm

FILE ROLE
This file is the minimal definitional home of the pivot quantity `mreq`.

Paper-facing note:
- In the paper, `mreq(y)` is defined intrinsically as the least index `m`
  such that `UBm y m > 2`.
- Accordingly, Lean defines `mreq` directly via `Nat.find`, using the
  intrinsic crossing-existence theorem from `UBmGrowth`.
- This file deliberately stays at that minimal level.
It does not expose any higher pivot-analytic facade such as lower bounds
on `mreq(y)` in terms of `y^2 / log y`; those belong in higher pivot / analytic
layers.
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.UBmGrowth

namespace Lehmer
namespace Pivot

open Classical

/--
Intrinsic threshold definition.

`mreq y` is the least index `m` such that `UBm y m > 2`.
-/
noncomputable def mreq (y : ℕ) : ℕ :=
  Nat.find (exists_UBm_gt_two y)

/--
`mreq y` is exactly the least witness of threshold exceedance.
-/
theorem mreq_eq_find (y : ℕ) :
    mreq y = Nat.find (exists_UBm_gt_two y) := by
  rfl

/--
At the defining threshold, the envelope exceeds `2`.
-/
theorem UBm_gt_two_at_mreq (y : ℕ) :
    (2 : ℚ) < UBm y (mreq y) := by
  rw [mreq_eq_find]
  exact Nat.find_spec (exists_UBm_gt_two y)

/--
Minimality: any witness `m` with `UBm y m > 2` dominates `mreq y`.
-/
theorem mreq_le_of_UBm_gt_two {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    mreq y ≤ m := by
  rw [mreq_eq_find]
  exact Nat.find_min' (exists_UBm_gt_two y) hm

/--
Re-export of minimality under the same name.
-/
theorem mreq_minimal {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    mreq y ≤ m := by
  exact mreq_le_of_UBm_gt_two hm

/--
Below the threshold, the envelope stays at or below `2`.
-/
theorem UBm_le_two_before_mreq {y m : ℕ} (hm : m < mreq y) :
    UBm y m ≤ 2 := by
  exact le_of_not_gt (by
    intro hgt
    have hle : mreq y ≤ m := mreq_le_of_UBm_gt_two hgt
    exact Nat.not_lt_of_ge hle hm)

/--
Equivalent negated-strict form below the threshold.
-/
theorem UBm_not_gt_two_before_mreq {y m : ℕ} (hm : m < mreq y) :
    ¬ (2 : ℚ) < UBm y m := by
  exact not_lt_of_ge (UBm_le_two_before_mreq hm)

/--
Bundled threshold characterization.
-/
theorem mreq_spec (y : ℕ) :
    ((2 : ℚ) < UBm y (mreq y)) ∧
      (∀ m < mreq y, UBm y m ≤ 2) := by
  refine ⟨UBm_gt_two_at_mreq y, ?_⟩
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
    have hgt : (2 : ℚ) < UBm y (mreq y) := UBm_gt_two_at_mreq y
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
The threshold is positive.
-/
theorem mreq_pos (y : ℕ) : 0 < mreq y := by
  have hgt : (2 : ℚ) < UBm y (mreq y) := UBm_gt_two_at_mreq y
  have hm0 : mreq y ≠ 0 := by
    intro hm
    rw [hm, UBm_zero] at hgt
    norm_num at hgt
  exact Nat.pos_iff_ne_zero.mpr hm0

/--
At the threshold, the envelope does not stay at or below `2`.
-/
theorem UBm_not_le_two_at_mreq (y : ℕ) :
    ¬ UBm y (mreq y) ≤ 2 := by
  exact not_le_of_gt (UBm_gt_two_at_mreq y)

/--
Any strict predecessor of the threshold fails to exceed `2`.
-/
theorem not_UBm_gt_two_of_lt_mreq {y m : ℕ} (hm : m < mreq y) :
    ¬ (2 : ℚ) < UBm y m := by
  exact UBm_not_gt_two_before_mreq hm

/--
Contradiction form:
if `m < mreq y`, then `m` cannot witness threshold exceedance.
-/
theorem false_of_lt_mreq_of_UBm_gt_two {y m : ℕ}
    (hm : m < mreq y) (hgt : (2 : ℚ) < UBm y m) :
    False := by
  exact (UBm_not_gt_two_before_mreq hm) hgt

end Pivot
end Lehmer