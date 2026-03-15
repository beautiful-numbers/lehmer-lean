import Mathlib
import Lehmer.Basic.Defs
import Lehmer.Pivot.UBm
import Lehmer.Pivot.Mreq

namespace Lehmer
namespace Pivot

/--
A natural number `n` is `y`-rough if every prime divisor of `n` is at least `y`.
This is the pivot-side roughness condition used throughout the paper.
-/
def YRough (y n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → y ≤ p

/--
Abstract support-cardinality interface.

At this stage we do not yet commit to a concrete implementation
of `ω(n)` in terms of the prime support; we only expose the symbol
that will later be connected to `primeSupport n`.
-/
opaque omega (n : ℕ) : ℕ

/--
Abstract worst-case envelope theorem:

if `n` is `y`-rough, then its totient index is bounded above by the
pivot envelope at support size `omega n`.
This is the key structural input behind the pivot lower bound.
-/
axiom totientIndex_le_UBm_of_yrough {y n : ℕ} :
    YRough y n → totientIndex n ≤ UBm y (omega n)

/--
Abstract pivot lower bound:

if `n` is `y`-rough and `I(n) > 2`, then the support size of `n`
is at least `mreq y`.
-/
theorem pivot_lower_bound_abstract {y n : ℕ}
    (hy : YRough y n) (hI : (2 : ℚ) < totientIndex n) :
    mreq y ≤ omega n := by
  have hUB : (2 : ℚ) < UBm y (omega n) := by
    exact lt_of_lt_of_le hI (totientIndex_le_UBm_of_yrough hy)
  exact mreq_le_of_UBm_gt_two hUB

/--
Equivalent reformulation of the abstract pivot lower bound.
-/
theorem omega_ge_mreq_of_yrough_and_gt_two {y n : ℕ}
    (hy : YRough y n) (hI : (2 : ℚ) < totientIndex n) :
    omega n ≥ mreq y := by
  exact pivot_lower_bound_abstract hy hI

/--
Contrapositive form: if the support size is smaller than `mreq y`,
then a `y`-rough integer cannot have `I(n) > 2`.
-/
theorem not_totientIndex_gt_two_of_omega_lt_mreq {y n : ℕ}
    (hy : YRough y n) (hω : omega n < mreq y) :
    ¬ (2 : ℚ) < totientIndex n := by
  intro hI
  exact (not_le_of_lt hω) (pivot_lower_bound_abstract hy hI)

/--
Numerical upper-threshold form: if `omega n < mreq y`, then `I(n) ≤ 2`.
-/
theorem totientIndex_le_two_of_omega_lt_mreq {y n : ℕ}
    (hy : YRough y n) (hω : omega n < mreq y) :
    totientIndex n ≤ 2 := by
  by_contra h
  have h' : (2 : ℚ) < totientIndex n := lt_of_not_ge h
  exact (not_totientIndex_gt_two_of_omega_lt_mreq hy hω) h'

/--
Lehmer-composite form of the abstract pivot lower bound.

This isolates the exact point where the arithmetic side of the paper
interfaces with the pivot method: a Lehmer composite satisfies `I(n) > 2`,
so once that fact is provided, the lower bound follows immediately.
-/
theorem pivot_lower_bound_of_LehmerComposite {y n : ℕ}
    (hrough : YRough y n)
    (hL : Lehmer.Basic.LehmerComposite n)
    (hI : (2 : ℚ) < totientIndex n) :
    mreq y ≤ omega n := by
  exact pivot_lower_bound_abstract hrough hI

end Pivot
end Lehmer