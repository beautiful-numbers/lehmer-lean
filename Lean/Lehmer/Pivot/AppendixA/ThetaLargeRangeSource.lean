-- FILE: Lean/Lehmer/Pivot/AppendixA/ThetaLargeRangeSource.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.AppendixA.ThetaDefs : def
- Lehmer.Pivot.AppendixA.ThetaBroadbentK4Source : thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.AppendixA.ThetaDefs
import Lehmer.Pivot.AppendixA.ThetaBroadbentK4Source

namespace Lehmer
namespace Pivot
namespace AppendixA
namespace ThetaLargeRangeSource

open scoped Real

noncomputable def thetaLargeRangeSourceConstant : ℝ := 151.3

@[simp] theorem thetaLargeRangeSourceConstant_def :
    thetaLargeRangeSourceConstant = 151.3 := rfl

def thetaLargeRangeSourceThreshold : ℝ := (Y0 : ℝ)

@[simp] theorem thetaLargeRangeSourceThreshold_def :
    thetaLargeRangeSourceThreshold = (Y0 : ℝ) := rfl

noncomputable def thetaLargeRangeSourceError (x : ℝ) : ℝ :=
  thetaLargeRangeSourceConstant * x / (Real.log x)^4

@[simp] theorem thetaLargeRangeSourceError_def (x : ℝ) :
    thetaLargeRangeSourceError x =
      thetaLargeRangeSourceConstant * x / (Real.log x)^4 := rfl

private theorem Y0_real_pos : 0 < (Y0 : ℝ) := by
  norm_num [Y0_def]

private theorem Y0_real_gt_one : (1 : ℝ) < (Y0 : ℝ) := by
  norm_num [Y0_def]

private theorem x_pos_of_ge_threshold
    {x : ℝ}
    (hx : thetaLargeRangeSourceThreshold ≤ x) :
    0 < x := by
  have hY0 : (Y0 : ℝ) ≤ x := by
    simpa [thetaLargeRangeSourceThreshold_def] using hx
  linarith [Y0_real_pos]

private theorem x_nonneg_of_ge_threshold
    {x : ℝ}
    (hx : thetaLargeRangeSourceThreshold ≤ x) :
    0 ≤ x := le_of_lt (x_pos_of_ge_threshold hx)

private theorem x_ge_one_of_ge_threshold
    {x : ℝ}
    (hx : thetaLargeRangeSourceThreshold ≤ x) :
    (1 : ℝ) ≤ x := by
  have hY0 : (Y0 : ℝ) ≤ x := by
    simpa [thetaLargeRangeSourceThreshold_def] using hx
  linarith [Y0_real_gt_one]

private theorem log_pos_of_ge_threshold
    {x : ℝ}
    (hx : thetaLargeRangeSourceThreshold ≤ x) :
    0 < Real.log x := by
  have hx1 : (1 : ℝ) < x := by
    have hY0 : (Y0 : ℝ) ≤ x := by
      simpa [thetaLargeRangeSourceThreshold_def] using hx
    linarith [Y0_real_gt_one]
  exact Real.log_pos hx1

private theorem log_ne_zero_of_ge_threshold
    {x : ℝ}
    (hx : thetaLargeRangeSourceThreshold ≤ x) :
    Real.log x ≠ 0 := by
  have hlog : 0 < Real.log x := log_pos_of_ge_threshold hx
  linarith

private theorem log_pow4_pos_of_ge_threshold
    {x : ℝ}
    (hx : thetaLargeRangeSourceThreshold ≤ x) :
    0 < (Real.log x)^4 := by
  have hlog : 0 < Real.log x := log_pos_of_ge_threshold hx
  positivity

/--
Primitive large-range explicit source bound for `θ`.

Source:
Broadbent–Kadiri–Lumley–Ng–Wilk, Theorem 1 / Table 5,
case `k = 4`, with constant `151.3`.

Exported in the Lehmer-facing shape:
    |thetaUpTo x - x| ≤ thetaLargeRangeSourceError x
for x ≥ Y0.
-/
theorem theta_large_range_source
    {x : ℝ}
    (hx : thetaLargeRangeSourceThreshold ≤ x) :
    |thetaUpTo x - x| ≤ thetaLargeRangeSourceError x := by
  have hx1 : (1 : ℝ) ≤ x := x_ge_one_of_ge_threshold hx
  have hsrc :
      |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    exact ThetaBroadbentK4Source.theta_broadbent_k4_source hx1
  simpa [thetaLargeRangeSourceError_def, thetaLargeRangeSourceConstant_def] using hsrc

end ThetaLargeRangeSource
end AppendixA
end Pivot
end Lehmer