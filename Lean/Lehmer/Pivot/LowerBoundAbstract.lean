-- FILE: Lean/Lehmer/Pivot/LowerBoundAbstract.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.LehmerBasic : thm
- Lehmer.Basic.Totient : def thm
- Lehmer.Pivot.Defs : def thm
- Lehmer.Pivot.SupportInterface : def thm
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.Mreq : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.LehmerBasic
import Lehmer.Basic.Totient
import Lehmer.Pivot.Defs
import Lehmer.Pivot.SupportInterface
import Lehmer.Pivot.UBm
import Lehmer.Pivot.Mreq

namespace Lehmer
namespace Pivot

open Lehmer.Basic

/--
Worst-case envelope theorem:

if `n` is squarefree and `y`-rough, then its totient index is bounded above by
the pivot envelope at support size `omega n`.

This is proved by rewriting `totientIndex n` as the product over the prime
support and then comparing that product to the canonical worst-case envelope
`UBm y (omega n)`.
-/
theorem totientIndex_le_UBm_of_yrough {y n : ℕ}
    (hsq : Squarefree n) (hy : YRough y n) :
    totientIndex n ≤ UBm y (omega n) := by
  rw [totientIndex_eq_prod_primeSupport_of_squarefree hsq]
  simpa [omega_def] using prod_primeSupport_le_UBm_of_yrough hy

/--
Abstract pivot lower bound:

if `n` is squarefree, `y`-rough, and `I(n) > 2`, then the support size of `n`
is at least `mreq y`.
-/
theorem pivot_lower_bound_abstract {y n : ℕ}
    (hsq : Squarefree n) (hy : YRough y n) (hI : (2 : ℚ) < totientIndex n) :
    mreq y ≤ omega n := by
  have hUB : (2 : ℚ) < UBm y (omega n) := by
    exact lt_of_lt_of_le hI (totientIndex_le_UBm_of_yrough hsq hy)
  exact mreq_le_of_UBm_gt_two hUB

/--
Equivalent reformulation of the abstract pivot lower bound.
-/
theorem omega_ge_mreq_of_yrough_and_gt_two {y n : ℕ}
    (hsq : Squarefree n) (hy : YRough y n) (hI : (2 : ℚ) < totientIndex n) :
    omega n ≥ mreq y := by
  exact pivot_lower_bound_abstract hsq hy hI

/--
Contrapositive form: if the support size is smaller than `mreq y`,
then a squarefree `y`-rough integer cannot have `I(n) > 2`.
-/
theorem not_totientIndex_gt_two_of_omega_lt_mreq {y n : ℕ}
    (hsq : Squarefree n) (hy : YRough y n) (hω : omega n < mreq y) :
    ¬ (2 : ℚ) < totientIndex n := by
  intro hI
  exact (not_lt_of_ge (pivot_lower_bound_abstract hsq hy hI)) hω

/--
Numerical upper-threshold form: if `omega n < mreq y`, then `I(n) ≤ 2`.
-/
theorem totientIndex_le_two_of_omega_lt_mreq {y n : ℕ}
    (hsq : Squarefree n) (hy : YRough y n) (hω : omega n < mreq y) :
    totientIndex n ≤ 2 := by
  by_contra h
  have h' : (2 : ℚ) < totientIndex n := lt_of_not_ge h
  exact (not_totientIndex_gt_two_of_omega_lt_mreq hsq hy hω) h'

/--
Lehmer-composite form of the abstract pivot lower bound at an arbitrary
roughness parameter `y`.
-/
theorem pivot_lower_bound_of_LehmerComposite {y n : ℕ}
    (hrough : YRough y n)
    (hL : LehmerComposite n) :
    mreq y ≤ omega n := by
  exact pivot_lower_bound_abstract hL.squarefree hrough
    (Lehmer.Basic.totientIndex_gt_two_of_LehmerComposite hL)

/--
Canonical roughness lemma at the pivot value.

For a Lehmer composite, every prime divisor of `n` is at least its canonical
pivot `pivotVal n = Nat.minFac n`.
-/
theorem yrough_at_pivotVal_of_LehmerComposite {n : ℕ}
    (_hL : LehmerComposite n) :
    YRough (pivotVal n) n := by
  intro p hp hpd
  simpa [pivotVal] using Nat.minFac_le_of_dvd hp.two_le hpd

/--
Pipeline-ready lower bound at the canonical pivot.

This is the exact statement needed to close Case A mathematically:
the canonical pivot demand `mreq (pivotVal n)` is bounded above by the true
support size `omega n`.
-/
theorem pivot_lower_bound_at_pivotVal_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    mreq (pivotVal n) ≤ omega n := by
  exact pivot_lower_bound_of_LehmerComposite
    (yrough_at_pivotVal_of_LehmerComposite hL) hL

end Pivot
end Lehmer