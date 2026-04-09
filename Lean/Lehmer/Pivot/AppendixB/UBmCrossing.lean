-- FILE: Lean/Lehmer/Pivot/UBmCrossing.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.Mreq : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.Mreq

namespace Lehmer
namespace Pivot

/-!
# UBm crossing interface

This file packages the intrinsic crossing interface for `UBm` obtained from the
definition of `mreq`.

Since `mreq` is now defined intrinsically from the global crossing-existence
theorem, this file is only a thin re-export layer.
-/

/--
At the threshold `mreq y`, the envelope crosses `2`.
-/
theorem UBm_crossing_at_mreq
    (y : ℕ) :
    (2 : ℚ) < UBm y (mreq y) := by
  exact UBm_gt_two_at_mreq y

/--
Some crossing index always exists.
-/
theorem exists_UBm_crossing
    (y : ℕ) :
    ∃ m : ℕ, (2 : ℚ) < UBm y m := by
  exact exists_UBm_gt_two y

/--
The threshold `mreq y` is itself a crossing index.
-/
theorem exists_UBm_crossing_at_mreq
    (y : ℕ) :
    ∃ m : ℕ, (2 : ℚ) < UBm y m := by
  exact ⟨mreq y, UBm_crossing_at_mreq y⟩

/--
The threshold is positive.
-/
theorem mreq_pos_of_crossing
    (y : ℕ) :
    0 < mreq y := by
  exact mreq_pos y

/--
A witness crossing index dominates `mreq y`.
-/
theorem mreq_le_of_crossing
    {y m : ℕ}
    (h : (2 : ℚ) < UBm y m) :
    mreq y ≤ m := by
  exact mreq_le_of_UBm_gt_two h

/--
Below the threshold, no crossing occurs.
-/
theorem no_crossing_before_mreq
    {y m : ℕ}
    (hm : m < mreq y) :
    ¬ (2 : ℚ) < UBm y m := by
  exact not_UBm_gt_two_of_lt_mreq hm

end Pivot
end Lehmer