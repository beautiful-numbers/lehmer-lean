-- FILE: Lean/Lehmer/Pivot/AppendixA/MreqLowerBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
- Lehmer.Pivot.AppendixA.IntervalProduct : def thm
- Lehmer.Pivot.AppendixA.IntervalProductBound : thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.Mreq
import Lehmer.Pivot.AppendixA.PrimeCountDefs
import Lehmer.Pivot.AppendixA.IntervalProduct
import Lehmer.Pivot.AppendixA.IntervalProductBound

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A lower bound for `mreq`

This file assembles the first public lower bound on `mreq` obtained from the
Appendix A interval-product argument.

Core output:
* for prime `y` in the large-range regime, one has
  `primePi (xA y) - primePi y + 1 ≤ mreq y`.

This is the paper-facing consequence of the chain:
* `UBm y m ≤ intervalPrimeProd y`,
* `intervalPrimeProd y ≤ 2`,
* hence `UBm y m ≤ 2`,
* therefore `m` lies below the intrinsic crossing threshold `mreq y`.
-/

/--
Appendix A lower bound on `mreq` in the prime-counting form used in the paper.
-/
theorem mreq_ge_primePi_sub_primePi_add_one_of_ge_Y0
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y) :
    primePi (xA y) - primePi y + 1 ≤ mreq y := by
  let N : ℕ := primePi (xA y) - primePi y + 1
  have hUBN : UBm y N ≤ 2 := by
    apply UBm_le_two_of_intervalPrimeProd_le_two
      (y := y) (m := N) (hy := hy) (hyx := hyx)
    · simpa [N]
    · exact intervalPrimeProd_le_two_of_ge_Y0 y hy0
  by_contra hnot
  have hlt : mreq y < N := Nat.lt_of_not_ge hnot
  have hcross : (2 : ℚ) < UBm y (mreq y) := UBm_gt_two_at_mreq y
  have hmono : UBm y (mreq y) ≤ UBm y N := by
    exact UBm_le_of_le (y := y) (m := mreq y) (n := N) (Nat.le_of_lt hlt)
  have hgtN : (2 : ℚ) < UBm y N := lt_of_lt_of_le hcross hmono
  exact (not_lt_of_ge hUBN) hgtN

/--
Equivalent Appendix A lower bound written as the cardinality of the prime set
in the interval `[y, xA y]`.
-/
theorem mreq_ge_card_primesInIcc_of_ge_Y0
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y) :
    (primesInIcc y (xA y)).card ≤ mreq y := by
  rw [card_primesInIcc_eq_primePi_sub_primePi_add_one hy hyx]
  exact mreq_ge_primePi_sub_primePi_add_one_of_ge_Y0 hy0 hy hyx

end AppendixA
end Pivot
end Lehmer