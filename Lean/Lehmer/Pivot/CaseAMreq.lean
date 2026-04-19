-- FILE: Lean/Lehmer/Pivot/CaseAMreq.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm

FILE ROLE
Local Case A version of the pivot threshold.

This file defines a Case A-local pivot threshold from the UBm crossing set,
without depending on the removed global crossing-existence file `UBmGrowth`.

The definition is local and total:
- if there exists a witness `m` such that `UBm y m > 2`, then `caseAMreq y`
  is the least such witness;
- otherwise `caseAMreq y := 0`.

This is enough for the Case A-local minimality API:
any actual witness dominates `caseAMreq y`, and therefore every strict
predecessor of `caseAMreq y` stays at or below `2`.
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm

namespace Lehmer
namespace Pivot

open Classical

/--
Case A local intrinsic threshold.

`caseAMreq y` is the least index `m` such that `UBm y m > 2` when such a
witness exists, and `0` otherwise.
-/
noncomputable def caseAMreq (y : ℕ) : ℕ :=
  if h : ∃ m : ℕ, (2 : ℚ) < UBm y m then
    Nat.find h
  else
    0

/--
If a witness exists, `caseAMreq y` is exactly the corresponding `Nat.find`.
-/
theorem caseAMreq_eq_find_of_exists {y : ℕ}
    (h : ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    caseAMreq y = Nat.find h := by
  rw [caseAMreq, dif_pos h]

/--
If no witness exists, `caseAMreq y = 0`.
-/
theorem caseAMreq_eq_zero_of_not_exists {y : ℕ}
    (h : ¬ ∃ m : ℕ, (2 : ℚ) < UBm y m) :
    caseAMreq y = 0 := by
  rw [caseAMreq, dif_neg h]

/--
Minimality: any witness `m` with `UBm y m > 2` dominates `caseAMreq y`.
-/
theorem caseAMreq_le_of_UBm_gt_two {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    caseAMreq y ≤ m := by
  let h : ∃ k : ℕ, (2 : ℚ) < UBm y k := ⟨m, hm⟩
  rw [caseAMreq_eq_find_of_exists h]
  exact Nat.find_min' h hm

/--
Re-export of minimality under the same meaning.
-/
theorem caseAMreq_minimal {y m : ℕ} (hm : (2 : ℚ) < UBm y m) :
    caseAMreq y ≤ m := by
  exact caseAMreq_le_of_UBm_gt_two hm

/--
Below the threshold, the envelope stays at or below `2`.
-/
theorem UBm_le_two_before_caseAMreq {y m : ℕ} (hm : m < caseAMreq y) :
    UBm y m ≤ 2 := by
  exact le_of_not_gt (by
    intro hgt
    have hle : caseAMreq y ≤ m := caseAMreq_le_of_UBm_gt_two hgt
    exact Nat.not_lt_of_ge hle hm)

/--
Equivalent negated-strict form below the threshold.
-/
theorem UBm_not_gt_two_before_caseAMreq {y m : ℕ} (hm : m < caseAMreq y) :
    ¬ (2 : ℚ) < UBm y m := by
  exact not_lt_of_ge (UBm_le_two_before_caseAMreq hm)

/--
Convenient re-export of the below-threshold bound.
-/
theorem UBm_le_two_of_lt_caseAMreq {y m : ℕ} (hm : m < caseAMreq y) :
    UBm y m ≤ 2 := by
  exact UBm_le_two_before_caseAMreq hm

/--
The threshold is nonnegative.
-/
theorem caseAMreq_nonneg (y : ℕ) : 0 ≤ caseAMreq y := by
  exact Nat.zero_le _

/--
Any strict predecessor of the threshold fails to exceed `2`.
-/
theorem not_UBm_gt_two_of_lt_caseAMreq {y m : ℕ} (hm : m < caseAMreq y) :
    ¬ (2 : ℚ) < UBm y m := by
  exact UBm_not_gt_two_before_caseAMreq hm

/--
Contradiction form:
if `m < caseAMreq y`, then `m` cannot witness threshold exceedance.
-/
theorem false_of_lt_caseAMreq_of_UBm_gt_two {y m : ℕ}
    (hm : m < caseAMreq y) (hgt : (2 : ℚ) < UBm y m) :
    False := by
  exact (UBm_not_gt_two_before_caseAMreq hm) hgt

end Pivot
end Lehmer