-- FILE: Lean/Lehmer/Support/PotentialP.lean
import Lehmer.Prelude
import Lehmer.Basic.SupportProd
import Lehmer.Basic.SupportLcm
import Lehmer.Basic.PrimeSupport
import Lehmer.Support.IncrementRatio

namespace Lehmer
namespace Support

open Lehmer.Basic

/-- The continuous support potential `P(S) = log L(S) / log n_S`. -/
noncomputable def supportPotential (S : Finset ℕ) : ℝ :=
  Real.log (supportLcm S) / Real.log (supportProd S)

@[simp] theorem supportPotential_def (S : Finset ℕ) :
    supportPotential S = Real.log (supportLcm S) / Real.log (supportProd S) := rfl

/-- If all elements of `S` are prime, then `supportProd S` is positive. -/
theorem supportProd_pos_of_all_prime {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    0 < supportProd S := by
  apply Basic.supportProd_pos
  intro p hp
  exact Nat.lt_of_lt_of_le (by decide : 0 < 2) (hS p hp).two_le

/-- If all elements of `S` are prime, then `supportProd S` is nonzero. -/
theorem supportProd_ne_zero_of_all_prime {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    supportProd S ≠ 0 := by
  exact Nat.ne_of_gt (supportProd_pos_of_all_prime hS)

/-- If all elements of `S` are prime, then `supportLcm S` is nonzero. -/
theorem supportLcm_ne_zero_of_all_prime {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    supportLcm S ≠ 0 := by
  exact Nat.ne_of_gt (supportLcm_pos_of_all_prime hS)

/-- If `p ∈ S` and all elements of `S` are prime, then `supportProd S > 1`. -/
theorem supportProd_gt_one_of_mem_of_all_prime {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    1 < supportProd S := by
  have hpos : 0 < supportProd S := supportProd_pos_of_all_prime hS
  have hpdvd : p ∣ supportProd S := dvd_supportProd_of_mem hp
  have hp2 : 2 ≤ p := (hS p hp).two_le
  have hple : p ≤ supportProd S := Nat.le_of_dvd (Nat.succ_le_of_lt hpos) hpdvd
  exact lt_of_lt_of_le (by decide : 1 < 2) (le_trans hp2 hple)

/-- If `S` is nonempty and all elements of `S` are prime, then `log(supportProd S)` is positive. -/
theorem log_supportProd_pos_of_nonempty_of_all_prime {S : Finset ℕ}
    (hne : S.Nonempty)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    0 < Real.log (supportProd S) := by
  rcases hne with ⟨p, hp⟩
  have hgt_nat : 1 < supportProd S := supportProd_gt_one_of_mem_of_all_prime hp hS
  have hgt_real : (1 : ℝ) < (supportProd S : ℝ) := by
    exact_mod_cast hgt_nat
  simpa using Real.log_pos hgt_real

/--
Logarithmic decomposition of the modular resource through the increment ratio.
-/
theorem log_supportLcm_eq_log_erase_add_log_increment
    {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    Real.log (supportLcm S) =
      Real.log (supportLcm (S.erase p)) + Real.log (incrementRatio S p) := by
  have hinc_pos : 0 < incrementRatio S p := incrementRatio_pos_of_all_prime hS
  have herase_pos : 0 < supportLcm (S.erase p) := supportLcm_erase_pos_of_all_prime hS
  have hEq : (supportLcm S : ℝ) =
      (incrementRatio S p : ℝ) * (supportLcm (S.erase p) : ℝ) := by
    exact_mod_cast supportLcm_eq_incrementRatio_mul_supportLcm_erase S p
  rw [hEq]
  rw [Real.log_mul
    (by exact_mod_cast (Nat.ne_of_gt hinc_pos))
    (by exact_mod_cast (Nat.ne_of_gt herase_pos))]
  ring

/--
Rewriting of the support potential by exposing the increment contribution in the
numerator.
-/
theorem supportPotential_eq_log_erase_add_log_increment_div_log_supportProd
    {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    supportPotential S =
      (Real.log (supportLcm (S.erase p)) + Real.log (incrementRatio S p)) /
        Real.log (supportProd S) := by
  rw [supportPotential_def, log_supportLcm_eq_log_erase_add_log_increment hS]

end Support
end Lehmer