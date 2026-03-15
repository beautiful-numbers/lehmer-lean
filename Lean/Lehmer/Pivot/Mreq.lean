import Mathlib
import Lehmer.Pivot.UBm

namespace Lehmer
namespace Pivot

/--
`mreq y` is the least envelope length at which the pivot envelope exceeds `2`.

At the specification stage, we keep this as an abstract function together with
its defining API theorems, rather than committing immediately to a concrete
search implementation.
-/
opaque mreq (y : ℕ) : ℕ

/--
Defining threshold property: the pivot envelope at `mreq y` is strictly greater than `2`.
-/
axiom UBm_gt_two_at_mreq (y : ℕ) :
    (2 : ℚ) < UBm y (mreq y)

/--
Minimality property: every smaller envelope length stays at or below `2`.
-/
axiom UBm_le_two_before_mreq {y m : ℕ} :
    m < mreq y → UBm y m ≤ 2

/--
Equivalent packaged form of the minimality property.
-/
theorem UBm_not_gt_two_before_mreq {y m : ℕ} (hm : m < mreq y) :
    ¬ (2 : ℚ) < UBm y m := by
  exact not_lt_of_ge (UBm_le_two_before_mreq hm)

/--
At the threshold itself, the envelope is not at most `2`.
-/
theorem UBm_not_le_two_at_mreq (y : ℕ) :
    ¬ UBm y (mreq y) ≤ 2 := by
  exact not_le_of_lt (UBm_gt_two_at_mreq y)

/--
The threshold characterization of `mreq y`.
-/
theorem mreq_spec {y : ℕ} :
    ((2 : ℚ) < UBm y (mreq y)) ∧
      (∀ m < mreq y, UBm y m ≤ 2) := by
  refine ⟨UBm_gt_two_at_mreq y, ?_⟩
  intro m hm
  exact UBm_le_two_before_mreq hm

/--
No smaller index can satisfy the threshold inequality.
-/
theorem mreq_minimal {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    mreq y ≤ m := by
  by_contra h
  have hm' : m < mreq y := Nat.lt_of_not_ge h
  exact (not_lt_of_ge (UBm_le_two_before_mreq hm')) hm

/--
The threshold index is unique with its minimality property.
-/
theorem mreq_unique {y k : ℕ}
    (hk1 : (2 : ℚ) < UBm y k)
    (hk2 : ∀ m < k, UBm y m ≤ 2) :
    mreq y = k := by
  apply le_antisymm
  · exact mreq_minimal hk1
  · by_contra hlt
    have : UBm y (mreq y) ≤ 2 := hk2 (mreq y) (Nat.lt_of_not_ge hlt)
    exact (not_le_of_lt (UBm_gt_two_at_mreq y)) this

/--
If the envelope already exceeds `2` at index `m`, then the pivot threshold is at most `m`.
-/
theorem mreq_le_of_UBm_gt_two {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    mreq y ≤ m := by
  exact mreq_minimal hm

/--
If `m < mreq y`, then the envelope has not yet crossed the threshold `2`.
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
At index `0`, being below threshold forces `mreq y` to be positive.
-/
theorem mreq_pos_of_UBm_zero_le_two {y : ℕ} (h0 : UBm y 0 ≤ 2) :
    0 < mreq y := by
  by_contra h
  have hm : mreq y = 0 := Nat.eq_zero_of_not_pos h
  have : (2 : ℚ) < UBm y 0 := by simpa [hm] using UBm_gt_two_at_mreq y
  exact (not_lt_of_ge h0) this

/--
Since `UBm y 0 = 1`, the threshold is always positive.
-/
theorem mreq_pos (y : ℕ) : 0 < mreq y := by
  apply mreq_pos_of_UBm_zero_le_two
  simpa [UBm_zero y] using (show (UBm y 0 : ℚ) ≤ 2 by norm_num [UBm_zero y])

end Pivot
end Lehmer