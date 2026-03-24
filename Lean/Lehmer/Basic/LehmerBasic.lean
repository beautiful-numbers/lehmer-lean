-- FILE: Lean/Lehmer/Basic/LehmerBasic.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.Totient : thm
- Lehmer.Basic.OddSquarefree : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.Totient
import Lehmer.Basic.OddSquarefree

namespace Lehmer
namespace Basic

/-!
# Lehmer.Basic.LehmerBasic

Bridge layer from the structural Lehmer hypothesis to the first analytic input
needed by the pivot method.

Main output of this file:
`LehmerComposite n ⟹ 2 < totientIndex n`.
-/

/--
If the Lehmer quotient is `0`, then `n ≤ 1`.

This auxiliary contradiction is used to exclude the case `K(n)=0`
for a Lehmer composite.
-/
theorem le_one_of_lehmerQuotient_eq_zero {n : ℕ}
    (hK0 : lehmerQuotient n = 0) :
    n ≤ 1 := by
  by_cases hφ : Nat.totient n = 0
  · by_cases hn0 : n = 0
    · omega
    · have hφpos : 0 < Nat.totient n := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hn0)
      exact False.elim (hφ <| ne_of_gt hφpos)
  · have hφQ : totientQ n ≠ 0 := by
      rw [totientQ_def]
      exact_mod_cast hφ
    have hq : (((n - 1 : ℕ) : ℚ) / totientQ n) = 0 := by
      simpa [lehmerQuotient_def] using hK0
    have hnum_zero : (((n - 1 : ℕ) : ℚ)) = 0 := by
      rcases (div_eq_zero_iff hφQ).mp hq with hnum | hden
      · exact hnum
      · exact False.elim (hφQ hden)
    have hnat : n - 1 = 0 := by
      exact_mod_cast hnum_zero
    exact Nat.sub_eq_zero_iff_le.mp hnat

/--
If the Lehmer quotient is `1`, then `n` is prime.

This auxiliary contradiction is used to exclude the case `K(n)=1`
for a Lehmer composite.
-/
theorem prime_of_lehmerQuotient_eq_one {n : ℕ}
    (hn1 : 1 < n)
    (hK1 : lehmerQuotient n = 1) :
    Nat.Prime n := by
  have hφQ_pos : (0 : ℚ) < totientQ n := totientQ_pos_of_pos (lt_trans (by decide : 0 < 1) hn1)
  have hφQ_ne : totientQ n ≠ 0 := ne_of_gt hφQ_pos

  have hq : (((n - 1 : ℕ) : ℚ) / totientQ n) = 1 := by
    simpa [lehmerQuotient_def] using hK1

  have hphi_eq_q : (((n - 1 : ℕ) : ℚ)) = totientQ n := by
    have hmul : (((n - 1 : ℕ) : ℚ)) = 1 * totientQ n := by
      exact (div_eq_iff hφQ_ne).mp hq
    simpa [totientQ_def] using hmul

  have hphi_eq_nat : n - 1 = Nat.totient n := by
    exact_mod_cast hphi_eq_q

  exact (Nat.totient_eq_iff_prime hn1).mp hphi_eq_nat.symm

/--
Core analytic input for the pivot method:

a Lehmer composite has totient index strictly greater than `2`.
-/
theorem totientIndex_gt_two_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    (2 : ℚ) < totientIndex n := by
  rcases lehmerQuotient_exists_nat_of_LehmerComposite hL with ⟨k, hk⟩

  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hK0 : lehmerQuotient n = 0 := by simpa [hk0] using hk
    have hn_le_one : n ≤ 1 := le_one_of_lehmerQuotient_eq_zero hK0
    exact (not_le_of_gt hL.one_lt) hn_le_one

  have hk_ne_one : k ≠ 1 := by
    intro hk1
    have hK1 : lehmerQuotient n = 1 := by simpa [hk1] using hk
    have hprime : Nat.Prime n := prime_of_lehmerQuotient_eq_one hL.one_lt hK1
    exact hL.not_prime hprime

  have hk_ge_two : 2 ≤ k := by
    cases k with
    | zero =>
        exact False.elim (hk_ne_zero rfl)
    | succ k' =>
        cases k' with
        | zero =>
            exact False.elim (hk_ne_one rfl)
        | succ k'' =>
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k''))

  have hφpos : (0 : ℚ) < totientQ n := by
    exact totientQ_pos_of_pos hL.pos

  have hfrac_pos : (0 : ℚ) < 1 / totientQ n := by
    exact one_div_pos.mpr hφpos

  have hkq : (2 : ℚ) ≤ k := by
    exact_mod_cast hk_ge_two

  rw [totientIndex_eq_lehmerQuotient_add_inv n, hk]
  linarith

/--
Weak non-strict form of the main analytic input.
-/
theorem totientIndex_ge_two_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    (2 : ℚ) ≤ totientIndex n := by
  exact le_of_lt (totientIndex_gt_two_of_LehmerComposite hL)

/--
Equivalent contradiction form:
a Lehmer composite cannot satisfy `totientIndex n ≤ 2`.
-/
theorem not_totientIndex_le_two_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ totientIndex n ≤ 2 := by
  intro hle
  exact (not_lt_of_ge hle) (totientIndex_gt_two_of_LehmerComposite hL)

end Basic
end Lehmer