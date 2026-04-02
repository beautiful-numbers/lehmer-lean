-- FILE: Lean/Lehmer/Pivot/UBmCrossing.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBmOrder : def thm
- Lehmer.Pivot.Mreq : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBmOrder
import Lehmer.Pivot.Mreq

namespace Lehmer
namespace Pivot

/-!
# UBm crossing interface

This file packages the currently proved crossing-related interface for `UBm`.

Important scope:
* this file does **not** yet prove the global existence theorem
  `∃ k, (2 : ℚ) < UBm y k`;
* that theorem requires the analytic input from §3.2 of the paper
  (growth/divergence of `UBm(y,·)`), not yet internalized here;
* the present file only re-exports the crossing lemmas already derivable from
  the current intrinsic `mreq` theory.
-/

/--
At the threshold `mreq y`, the envelope crosses `2`, provided a crossing exists.
-/
theorem UBm_crossing_at_mreq_of_exists'
    {y : ℕ}
    (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    (2 : ℚ) < UBm y (mreq y) := by
  exact UBm_crossing_at_mreq_of_exists h

/--
If `mreq y` is positive, then some crossing index exists.
-/
theorem exists_UBm_crossing_of_mreq_pos
    {y : ℕ}
    (hm : 0 < mreq y) :
    ∃ m : ℕ, (2 : ℚ) < UBm y m := by
  exact UBm_crossing_of_mreq_pos hm

/--
Crossing existence is equivalent to positivity of `mreq y`.
-/
theorem exists_UBm_crossing_iff_mreq_pos
    (y : ℕ) :
    (∃ m : ℕ, (2 : ℚ) < UBm y m) ↔ 0 < mreq y := by
  exact UBm_crossing_iff_mreq_pos y

/--
If there is no crossing, then `mreq y = 0`.
-/
theorem mreq_eq_zero_of_no_crossing
    {y : ℕ}
    (h : ¬ ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    mreq y = 0 := by
  exact mreq_eq_zero_of_not_exists h

/--
If `mreq y = 0`, then there is no crossing.
-/
theorem no_crossing_of_mreq_eq_zero
    {y : ℕ}
    (hm : mreq y = 0) :
    ¬ ∃ m : ℕ, (2 : ℚ) < UBm y m := by
  intro h
  have hpos : 0 < mreq y := mreq_pos_of_exists h
  rw [hm] at hpos
  exact Nat.lt_irrefl 0 hpos

/--
Crossing nonexistence is equivalent to `mreq y = 0`.
-/
theorem no_crossing_iff_mreq_eq_zero
    (y : ℕ) :
    (¬ ∃ m : ℕ, (2 : ℚ) < UBm y m) ↔ mreq y = 0 := by
  constructor
  · intro h
    exact mreq_eq_zero_of_not_exists h
  · intro hm
    exact no_crossing_of_mreq_eq_zero hm

/--
If a crossing exists, then `mreq y` is positive.
-/
theorem mreq_pos_of_crossing
    {y : ℕ}
    (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    0 < mreq y := by
  exact mreq_pos_of_exists h

end Pivot
end Lehmer