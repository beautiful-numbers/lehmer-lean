-- FILE: Lean/Lehmer/Pivot/AppendixA/ThetaExplicitBounds.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.AppendixA.ThetaDefs : def
- Lehmer.Pivot.AppendixA.ThetaExternalConstants : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.AppendixA.ThetaDefs
import Lehmer.Pivot.AppendixA.ThetaExternalConstants

namespace Lehmer
namespace Pivot
namespace AppendixA
namespace ThetaExplicitBounds

open scoped Real
open ThetaExternalConstants

noncomputable def sourceThetaError (x : ℝ) : ℝ :=
  (151.3 : ℝ) * x / (Real.log x)^4

@[simp] theorem sourceThetaError_def (x : ℝ) :
    sourceThetaError x = (151.3 : ℝ) * x / (Real.log x)^4 := rfl

private theorem exp_nine_le_Y0 : Real.exp (9 : ℝ) ≤ (Y0 : ℝ) := by
  have he : Real.exp (1 : ℝ) < 3 := by
    simpa [Real.exp_one] using Real.e_lt_three
  have hrew : Real.exp (9 : ℝ) = (Real.exp (1 : ℝ)) ^ (9 : ℕ) := by
    rw [show (9 : ℝ) = (9 : ℕ) by norm_num, Real.exp_nat_mul]
  have hlt : Real.exp (9 : ℝ) < (3 : ℝ) ^ (9 : ℕ) := by
    rw [hrew]
    exact pow_lt_pow_of_lt_left (by positivity) he 9
  have hpow : (3 : ℝ) ^ (9 : ℕ) = 19683 := by
    norm_num
  have hY0 : (19683 : ℝ) ≤ (Y0 : ℝ) := by
    norm_num [Y0_def]
  rw [hpow] at hlt
  linarith

private theorem log_Y0_ge_nine : (9 : ℝ) ≤ Real.log (Y0 : ℝ) := by
  have hpos : 0 < (Y0 : ℝ) := Y0_real_pos
  rw [Real.le_log_iff_exp_le hpos]
  exact exp_nine_le_Y0

private theorem log_ge_nine_of_ge_XTheta
    {x : ℝ}
    (hx : XTheta ≤ x) :
    (9 : ℝ) ≤ Real.log x := by
  have hmono :
      Real.log (Y0 : ℝ) ≤ Real.log x := by
    exact Real.monotone_log (le_of_lt Y0_real_pos) (by simpa [XTheta_def] using hx)
  linarith [log_Y0_ge_nine, hmono]

private theorem theta_broadbent_k4_bound_source
    {x : ℝ}
    (hx1 : (1 : ℝ) ≤ x) :
    |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
  /-
  SOURCE:
  Broadbent–Kadiri–Lumley–Ng–Wilk (2020), Theorem 1 / Table 5,
  case k = 4, X0 = X1 = 1, m4 = M4 = 151.3.

  Mathematical content used here:
      |θ(x) - x| ≤ 151.3 * x / log(x)^4    for all x ≥ 1.
  -/
  sorry

private theorem theta_dusart_bound
    {x : ℝ}
    (hx : XTheta ≤ x) :
    |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
  have hx1 : (1 : ℝ) ≤ x := x_ge_one_of_ge_XTheta hx
  exact theta_broadbent_k4_bound_source hx1

private theorem theta_error_source_base
    {x : ℝ}
    (hx : XTheta ≤ x) :
    |thetaUpTo x - x| ≤ sourceThetaError x := by
  have hsrc :
      |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    exact theta_dusart_bound hx
  simpa [sourceThetaError_def] using hsrc

private theorem log_Y0_sq_large :
    (151.3 : ℝ) ≤ 2 * (Real.log (Y0 : ℝ))^2 := by
  have h9 : (9 : ℝ) ≤ Real.log (Y0 : ℝ) := log_Y0_ge_nine
  nlinarith

private theorem log_sq_large_of_ge_XTheta
    {x : ℝ}
    (hx : XTheta ≤ x) :
    (151.3 : ℝ) ≤ 2 * (Real.log x)^2 := by
  have hmono :
      Real.log (Y0 : ℝ) ≤ Real.log x := by
    exact Real.monotone_log (le_of_lt Y0_real_pos) (by simpa [XTheta_def] using hx)
  have hbase : (151.3 : ℝ) ≤ 2 * (Real.log (Y0 : ℝ))^2 := log_Y0_sq_large
  nlinarith

private theorem sourceThetaError_le_target
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    sourceThetaError x ≤ 2 * x / (Real.log x)^2 := by
  have hx : XTheta ≤ x := by
    simpa [XTheta_def] using hx0
  have hxnonneg : 0 ≤ x := x_nonneg_of_ge_XTheta hx
  have hlog : 0 < Real.log x := log_pos_of_ge_XTheta hx
  have hlog4 : 0 < (Real.log x)^4 := by
    positivity
  have hlog_ne : Real.log x ≠ 0 := log_ne_zero_of_ge_XTheta hx
  have hmain : (151.3 : ℝ) ≤ 2 * (Real.log x)^2 := log_sq_large_of_ge_XTheta hx
  rw [sourceThetaError_def]
  have hscale_nonneg : 0 ≤ x / (Real.log x)^4 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_right hmain hscale_nonneg
  have hrew1 :
      (151.3 : ℝ) * (x / (Real.log x)^4) = (151.3 : ℝ) * x / (Real.log x)^4 := by
    ring
  have hrew2 :
      (2 * (Real.log x)^2) * (x / (Real.log x)^4) = 2 * x / (Real.log x)^2 := by
    field_simp [hlog_ne]
    ring
  simpa [hrew1, hrew2] using hscaled

private theorem theta_abs_explicit_core
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    |thetaUpTo x - x| ≤ 2 * x / (Real.log x)^2 := by
  have hx : XTheta ≤ x := by
    simpa [XTheta_def] using hx0
  exact le_trans (theta_error_source_base hx) (sourceThetaError_le_target hx0)

theorem theta_lower_explicit_of_ge_Y0
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    x - 2 * x / (Real.log x)^2 ≤ thetaUpTo x := by
  have habs :
      |thetaUpTo x - x| ≤ 2 * x / (Real.log x)^2 :=
    theta_abs_explicit_core hx0
  have hneg :
      -(2 * x / (Real.log x)^2) ≤ thetaUpTo x - x := by
    have h1 : -|thetaUpTo x - x| ≤ thetaUpTo x - x := by
      exact neg_abs_le (thetaUpTo x - x)
    linarith
  linarith

theorem theta_upper_explicit_of_ge_Y0
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    thetaUpTo x ≤ x + 2 * x / (Real.log x)^2 := by
  have habs :
      |thetaUpTo x - x| ≤ 2 * x / (Real.log x)^2 :=
    theta_abs_explicit_core hx0
  have hpos :
      thetaUpTo x - x ≤ 2 * x / (Real.log x)^2 := by
    have h1 : thetaUpTo x - x ≤ |thetaUpTo x - x| := by
      exact le_abs_self (thetaUpTo x - x)
    linarith
  linarith

end ThetaExplicitBounds
end AppendixA
end Pivot
end Lehmer