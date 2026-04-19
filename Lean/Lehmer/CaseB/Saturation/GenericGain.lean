-- FILE: Lean/Lehmer/CaseB/Saturation/GenericGain.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.SupportProd : def thm
- Lehmer.Basic.PrimeSupport : def thm
- Lehmer.Support.GenericEntangled : def thm
- Lehmer.Support.PotentialP : def thm
- Lehmer.Support.PotentialP2 : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.SupportProd
import Lehmer.Basic.PrimeSupport
import Lehmer.Support.GenericEntangled
import Lehmer.Support.PotentialP
import Lehmer.Support.PotentialP2

namespace Lehmer
namespace CaseB
namespace Saturation

open Lehmer.Basic
open Lehmer.Support

/-- The inherited numerator-side potential, measured on the same denominator
    `log (supportProd S)`. -/
noncomputable def inheritedPotentialOnSameDenom (S : Finset ℕ) (p : ℕ) : ℝ :=
  Real.log (supportLcm (S.erase p)) / Real.log (supportProd S)

@[simp] theorem inheritedPotentialOnSameDenom_def (S : Finset ℕ) (p : ℕ) :
    inheritedPotentialOnSameDenom S p =
      Real.log (supportLcm (S.erase p)) / Real.log (supportProd S) := rfl

/-- Under `genericIn`, the logarithm of the threshold is bounded by the
    logarithm of the increment ratio. -/
theorem log_h_le_log_increment_of_generic
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hg : genericIn h S y p)
    (hh : 0 < h y)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    Real.log (h y) ≤ Real.log (incrementRatio S p) := by
  rw [genericIn_def] at hg
  have hhR : (0 : ℝ) < (h y : ℝ) := by
    exact_mod_cast hh
  have hincR : (0 : ℝ) < (incrementRatio S p : ℝ) := by
    exact_mod_cast incrementRatio_pos_of_all_prime hS
  have hltR : (h y : ℝ) < (incrementRatio S p : ℝ) := by
    exact_mod_cast hg
  exact le_of_lt (Real.strictMonoOn_log hhR hincR hltR)

/-- Decomposition of the support potential into the inherited term plus the
    normalized logarithmic increment contribution. -/
theorem supportPotential_eq_inherited_add_increment_term
    {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q)
    (_hlogprod : 0 < Real.log (supportProd S)) :
    supportPotential S =
      inheritedPotentialOnSameDenom S p +
        Real.log (incrementRatio S p) / Real.log (supportProd S) := by
  rw [supportPotential_def, inheritedPotentialOnSameDenom_def,
      log_supportLcm_eq_log_erase_add_log_increment hS]
  rw [add_div]

/-- Any lower bound on the normalized logarithmic increment gives a lower bound
    on the full support potential above the inherited same-denominator term. -/
theorem supportPotential_lower_bound_of_log_increment_lower_bound
    {S : Finset ℕ} {p : ℕ} {delta : ℝ}
    (hS : ∀ q ∈ S, Nat.Prime q)
    (hlogprod : 0 < Real.log (supportProd S))
    (hdelta : delta ≤ Real.log (incrementRatio S p) / Real.log (supportProd S)) :
    inheritedPotentialOnSameDenom S p + delta ≤ supportPotential S := by
  rw [supportPotential_eq_inherited_add_increment_term hS hlogprod]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hdelta (inheritedPotentialOnSameDenom S p)

/-- Abstract generic-gain lower bound on the support potential. -/
theorem supportPotential_lower_bound_of_generic
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ} {delta : ℝ}
    (hg : genericIn h S y p)
    (hh : 0 < h y)
    (hS : ∀ q ∈ S, Nat.Prime q)
    (hlogprod : 0 < Real.log (supportProd S))
    (hdelta : delta ≤ Real.log (h y) / Real.log (supportProd S)) :
    inheritedPotentialOnSameDenom S p + delta ≤ supportPotential S := by
  have hlog : Real.log (h y) ≤ Real.log (incrementRatio S p) :=
    log_h_le_log_increment_of_generic hg hh hS
  have hquot :
      Real.log (h y) / Real.log (supportProd S) ≤
        Real.log (incrementRatio S p) / Real.log (supportProd S) := by
    exact div_le_div_of_nonneg_right hlog (le_of_lt hlogprod)
  have hdelta' :
      delta ≤ Real.log (incrementRatio S p) / Real.log (supportProd S) :=
    le_trans hdelta hquot
  exact supportPotential_lower_bound_of_log_increment_lower_bound hS hlogprod hdelta'

/-- Continuous inherited saturation deficit on the fixed denominator
    `log (supportProd S)`. -/
noncomputable def inheritedPotentialDeficit (eps : ℝ) (S : Finset ℕ) (p : ℕ) : ℝ :=
  max 0 ((1 - eps) - inheritedPotentialOnSameDenom S p)

@[simp] theorem inheritedPotentialDeficit_def (eps : ℝ) (S : Finset ℕ) (p : ℕ) :
    inheritedPotentialDeficit eps S p =
      max 0 ((1 - eps) - inheritedPotentialOnSameDenom S p) := rfl

/-- Discretized inherited saturation deficit. -/
noncomputable def inheritedPotentialP2 (eps delta : ℝ) (S : Finset ℕ) (p : ℕ) : ℕ :=
  Nat.ceil (inheritedPotentialDeficit eps S p / delta)

@[simp] theorem inheritedPotentialP2_def (eps delta : ℝ) (S : Finset ℕ) (p : ℕ) :
    inheritedPotentialP2 eps delta S p =
      Nat.ceil (inheritedPotentialDeficit eps S p / delta) := rfl

/-- The inherited continuous deficit is always nonnegative. -/
theorem inheritedPotentialDeficit_nonneg (eps : ℝ) (S : Finset ℕ) (p : ℕ) :
    0 ≤ inheritedPotentialDeficit eps S p := by
  rw [inheritedPotentialDeficit_def]
  exact le_max_left _ _

/-- If the inherited same-denominator potential already reaches the threshold,
    the inherited continuous deficit vanishes. -/
theorem inheritedPotentialDeficit_eq_zero_of_saturated
    {eps : ℝ} {S : Finset ℕ} {p : ℕ}
    (hsat : 1 - eps ≤ inheritedPotentialOnSameDenom S p) :
    inheritedPotentialDeficit eps S p = 0 := by
  rw [inheritedPotentialDeficit_def]
  apply max_eq_left
  exact sub_nonpos.mpr hsat

/-- In the non-saturated inherited regime, the deficit is just the raw
    difference to the saturation threshold. -/
theorem inheritedPotentialDeficit_eq_sub_of_not_saturated
    {eps : ℝ} {S : Finset ℕ} {p : ℕ}
    (hnsat : inheritedPotentialOnSameDenom S p < 1 - eps) :
    inheritedPotentialDeficit eps S p = (1 - eps) - inheritedPotentialOnSameDenom S p := by
  rw [inheritedPotentialDeficit_def]
  apply max_eq_right
  exact le_of_lt (sub_pos.mpr hnsat)

/-- If the inherited same-denominator potential already reaches the threshold,
    the inherited discrete deficit vanishes. -/
theorem inheritedPotentialP2_eq_zero_of_saturated
    {eps delta : ℝ} {S : Finset ℕ} {p : ℕ}
    (_ : 0 < delta)
    (hsat : 1 - eps ≤ inheritedPotentialOnSameDenom S p) :
    inheritedPotentialP2 eps delta S p = 0 := by
  rw [inheritedPotentialP2_def,
      inheritedPotentialDeficit_eq_zero_of_saturated hsat]
  have hzero : (0 : ℝ) / delta = 0 := zero_div delta
  rw [hzero]
  norm_num

/-- Abstract discrete one-step decrease for two real potentials under a gain of
    size `delta`. -/
theorem realP2_decrease_of_gain
    {eps delta base current : ℝ}
    (hdelta : 0 < delta)
    (hbase : base ≤ 1 - eps)
    (hgain : current ≥ base + delta) :
    Nat.ceil (max 0 ((1 - eps) - current) / delta) ≤
      Nat.ceil (max 0 ((1 - eps) - base) / delta) - 1 := by
  let D : ℝ := max 0 ((1 - eps) - base)
  let D' : ℝ := max 0 ((1 - eps) - current)

  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact le_max_left _ _
  have hD'_nonneg : 0 ≤ D' := by
    dsimp [D']
    exact le_max_left _ _

  have hD_eq : D = (1 - eps) - base := by
    dsimp [D]
    apply max_eq_right
    exact sub_nonneg.mpr hbase

  have hcurr_sub_le : (1 - eps) - current ≤ ((1 - eps) - base) - delta := by
    linarith

  have hD'le : D' ≤ max 0 (D - delta) := by
    dsimp [D']
    have h1 : max 0 ((1 - eps) - current) ≤ max 0 (((1 - eps) - base) - delta) := by
      apply max_le_max le_rfl
      exact hcurr_sub_le
    have h2 : max 0 (((1 - eps) - base) - delta) = max 0 (D - delta) := by
      rw [hD_eq]
    exact h1.trans_eq h2

  change Nat.ceil (D' / delta) ≤ Nat.ceil (D / delta) - 1

  by_cases hsmall : D < delta
  · have hmax : max 0 (D - delta) = 0 := by
      apply max_eq_left
      linarith
    have hD'_zero : D' = 0 := by
      have hle0 : D' ≤ 0 := by
        simpa [hmax] using hD'le
      exact le_antisymm hle0 hD'_nonneg
    rw [hD'_zero]
    have hzero : (0 : ℝ) / delta = 0 := zero_div delta
    rw [hzero]
    by_cases hDzero : D = 0
    · have hceil_zero : Nat.ceil (D / delta) = 0 := by
        rw [hDzero, zero_div]
        norm_num
      rw [hceil_zero]
      norm_num
    · have hD_pos : 0 < D := by
        exact lt_of_le_of_ne hD_nonneg (Ne.symm hDzero)
      have hfrac_pos : 0 < D / delta := by
        exact div_pos hD_pos hdelta
      have hfrac_lt_one : D / delta < 1 := by
        have hlt : D / delta < delta / delta := by
          exact div_lt_div_of_pos_right hsmall hdelta
        simpa [hdelta.ne'] using hlt
      have hceil_ne_zero : Nat.ceil (D / delta) ≠ 0 := by
        intro hceil0
        have hle0 : D / delta ≤ 0 := by
          simpa [hceil0] using (Nat.le_ceil (D / delta))
        exact not_lt_of_ge hle0 hfrac_pos
      have hceil_lt_two :
          ((Nat.ceil (D / delta) : ℕ) : ℝ) < 2 := by
        have h1 : ((Nat.ceil (D / delta) : ℕ) : ℝ) < D / delta + 1 := by
          exact Nat.ceil_lt_add_one (le_of_lt hfrac_pos)
        have h2 : D / delta + 1 < 2 := by
          linarith
        exact lt_trans h1 h2
      have hceil_le_one : Nat.ceil (D / delta) ≤ 1 := by
        by_contra hnot
        have hge : 2 ≤ Nat.ceil (D / delta) := by omega
        have hgeR : (2 : ℝ) ≤ ((Nat.ceil (D / delta) : ℕ) : ℝ) := by
          exact_mod_cast hge
        exact (not_le_of_gt hceil_lt_two) hgeR
      have hceil_ge_one : 1 ≤ Nat.ceil (D / delta) := by
        omega
      have hceil_one : Nat.ceil (D / delta) = 1 := by
        omega
      rw [hceil_one]
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
    have hceil_lt : ((Nat.ceil (D' / delta) : ℕ) : ℝ) < D / delta := by
      have hlt1 : ((Nat.ceil (D' / delta) : ℕ) : ℝ) < D' / delta + 1 := by
        exact Nat.ceil_lt_add_one (div_nonneg hD'_nonneg (le_of_lt hdelta))
      have hle1 : D' / delta + 1 ≤ D / delta := by
        linarith
      exact lt_of_lt_of_le hlt1 hle1
    have hceil : D / delta ≤ ((Nat.ceil (D / delta) : ℕ) : ℝ) := by
      exact Nat.le_ceil (D / delta)
    have hltceil :
        ((Nat.ceil (D' / delta) : ℕ) : ℝ) <
          ((Nat.ceil (D / delta) : ℕ) : ℝ) := by
      exact lt_of_lt_of_le hceil_lt hceil
    have hnatlt : Nat.ceil (D' / delta) < Nat.ceil (D / delta) := by
      exact_mod_cast hltceil
    exact Nat.le_pred_of_lt hnatlt

/-- Final generic-to-discrete-drop bridge at fixed denominator. -/
theorem inheritedPotentialP2_decrease_of_generic
    {h : ℕ → ℕ} {eps delta : ℝ} {S : Finset ℕ} {y p : ℕ}
    (hg : genericIn h S y p)
    (hh : 0 < h y)
    (hS : ∀ q ∈ S, Nat.Prime q)
    (hlogprod : 0 < Real.log (supportProd S))
    (hdelta_pos : 0 < delta)
    (hdelta : delta ≤ Real.log (h y) / Real.log (supportProd S))
    (hbase : inheritedPotentialOnSameDenom S p ≤ 1 - eps) :
    potentialP2 eps delta S ≤ inheritedPotentialP2 eps delta S p - 1 := by
  have hgain :
      inheritedPotentialOnSameDenom S p + delta ≤ supportPotential S :=
    supportPotential_lower_bound_of_generic hg hh hS hlogprod hdelta
  rw [potentialP2_def, inheritedPotentialP2_def, inheritedPotentialDeficit_def]
  exact realP2_decrease_of_gain hdelta_pos hbase hgain

end Saturation
end CaseB
end Lehmer