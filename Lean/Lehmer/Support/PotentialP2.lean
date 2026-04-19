-- FILE: Lean/Lehmer/Support/PotentialP2.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Support.PotentialP : def thm
-/

import Lehmer.Prelude
import Lehmer.Support.PotentialP

namespace Lehmer
namespace Support

/-- Continuous saturation deficit: how far `supportPotential S` still lies below `1 - eps`. -/
noncomputable def potentialDeficit (eps : ℝ) (S : Finset ℕ) : ℝ :=
  max 0 ((1 - eps) - supportPotential S)

@[simp] theorem potentialDeficit_def (eps : ℝ) (S : Finset ℕ) :
    potentialDeficit eps S = max 0 ((1 - eps) - supportPotential S) := rfl

/-- Discrete saturation deficit obtained by measuring the continuous deficit in steps of size `delta`. -/
noncomputable def potentialP2 (eps delta : ℝ) (S : Finset ℕ) : ℕ :=
  Nat.ceil (potentialDeficit eps S / delta)

@[simp] theorem potentialP2_def (eps delta : ℝ) (S : Finset ℕ) :
    potentialP2 eps delta S = Nat.ceil (potentialDeficit eps S / delta) := rfl

/-- The continuous deficit is always nonnegative. -/
theorem potentialDeficit_nonneg (eps : ℝ) (S : Finset ℕ) :
    0 ≤ potentialDeficit eps S := by
  rw [potentialDeficit_def]
  exact le_max_left _ _

/-- If the support potential already reaches the saturation threshold, the continuous deficit vanishes. -/
theorem potentialDeficit_eq_zero_of_saturated
    {eps : ℝ} {S : Finset ℕ}
    (hsat : 1 - eps ≤ supportPotential S) :
    potentialDeficit eps S = 0 := by
  rw [potentialDeficit_def]
  apply max_eq_left
  linarith

/-- If the support potential already reaches the saturation threshold, the discrete deficit vanishes. -/
theorem potentialP2_eq_zero_of_saturated
    {eps delta : ℝ} {S : Finset ℕ}
    (_ : 0 < delta)
    (hsat : 1 - eps ≤ supportPotential S) :
    potentialP2 eps delta S = 0 := by
  rw [potentialP2_def, potentialDeficit_eq_zero_of_saturated hsat]
  have hzero : (0 : ℝ) / delta = 0 := zero_div delta
  rw [hzero]
  norm_num

/-- In the non-saturated regime, the continuous deficit simplifies to the raw difference. -/
theorem potentialDeficit_eq_sub_of_not_saturated
    {eps : ℝ} {S : Finset ℕ}
    (hnsat : supportPotential S < 1 - eps) :
    potentialDeficit eps S = (1 - eps) - supportPotential S := by
  rw [potentialDeficit_def]
  apply max_eq_right
  linarith

/-- Continuous deficit decreases by at least `delta`, up to truncation at `0`, under a controlled gain of size `delta`. -/
theorem potentialDeficit_le_max_sub_of_gain
    {eps delta : ℝ} {S S' : Finset ℕ}
    (hbase : supportPotential S ≤ 1 - eps)
    (hgain : supportPotential S' ≥ supportPotential S + delta) :
    potentialDeficit eps S' ≤ max 0 (potentialDeficit eps S - delta) := by
  have hdef :
      potentialDeficit eps S = (1 - eps) - supportPotential S := by
    rw [potentialDeficit_def]
    apply max_eq_right
    linarith
  have hraw :
      (1 - eps) - supportPotential S' ≤ potentialDeficit eps S - delta := by
    rw [hdef]
    linarith
  rw [potentialDeficit_def]
  exact max_le_max le_rfl hraw

/-- Discrete deficit drops by at least one step under a controlled gain of size `delta`. -/
theorem potentialP2_decrease_of_gain
    {eps delta : ℝ} {S S' : Finset ℕ}
    (hdelta : 0 < delta)
    (hbase : supportPotential S ≤ 1 - eps)
    (hgain : supportPotential S' ≥ supportPotential S + delta) :
    potentialP2 eps delta S' ≤ potentialP2 eps delta S - 1 := by
  let D : ℝ := potentialDeficit eps S
  let D' : ℝ := potentialDeficit eps S'

  have hD_nonneg : 0 ≤ D := potentialDeficit_nonneg eps S
  have hD'_nonneg : 0 ≤ D' := potentialDeficit_nonneg eps S'

  have hD'le : D' ≤ max 0 (D - delta) := by
    exact potentialDeficit_le_max_sub_of_gain hbase hgain

  rw [potentialP2_def, potentialP2_def]
  change Nat.ceil (D' / delta) ≤ Nat.ceil (D / delta) - 1

  by_cases hsmall : D < delta
  · have hmax : max 0 (D - delta) = 0 := by
      apply max_eq_left
      linarith
    have hD'_zero : D' = 0 := by
      have hle0 : D' ≤ 0 := by simpa [hmax] using hD'le
      linarith
    rw [hD'_zero]
    have hzero : (0 : ℝ) / delta = 0 := zero_div delta
    rw [hzero]
    norm_num
  · have hδleD : delta ≤ D := le_of_not_gt hsmall
    have hmax : max 0 (D - delta) = D - delta := by
      apply max_eq_right
      linarith
    have hD'le' : D' ≤ D - delta := by
      simpa [hmax] using hD'le
    have hquot : D' / delta ≤ D / delta - 1 := by
      have hdiv : D' / delta ≤ (D - delta) / delta := by
        exact div_le_div_of_nonneg_right hD'le' (le_of_lt hdelta)
      have hcalc : (D - delta) / delta = D / delta - 1 := by
        rw [sub_div, div_self hdelta.ne']
      exact hdiv.trans_eq hcalc
    have hcaseil :
        ((Nat.ceil (D' / delta) : ℕ) : ℝ) < D / delta := by
      have hlt1 : ((Nat.ceil (D' / delta) : ℕ) : ℝ) < D' / delta + 1 := by
        exact Nat.ceil_lt_add_one (div_nonneg hD'_nonneg (le_of_lt hdelta))
      have hle1 : D' / delta + 1 ≤ D / delta := by
        linarith
      exact lt_of_lt_of_le hlt1 hle1
    have hnatlt : Nat.ceil (D' / delta) < Nat.ceil (D / delta) := by
      have hceil : D / delta ≤ ((Nat.ceil (D / delta) : ℕ) : ℝ) := by
        exact Nat.le_ceil (D / delta)
      have hltceil :
          ((Nat.ceil (D' / delta) : ℕ) : ℝ) <
            ((Nat.ceil (D / delta) : ℕ) : ℝ) := by
        exact lt_of_lt_of_le hcaseil hceil
      exact_mod_cast hltceil
    exact Nat.le_pred_of_lt hnatlt

end Support
end Lehmer