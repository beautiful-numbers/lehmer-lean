-- FILE: Lean/Lehmer/Pivot/AppendixA/ThetaExternalConstants.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants

namespace Lehmer
namespace Pivot
namespace AppendixA
namespace ThetaExternalConstants

open scoped Real

/-!
This file is now *only* the θ-side external calibration layer.

It deliberately contains:
- the explicit external error model `epsTheta`;
- domain lemmas on `[XTheta, +∞)`;
- nonnegativity / termwise calibration lemmas;
- the final bridge
    epsTheta x ≤ 2 / (log x)^2
  and
    epsTheta x * x ≤ 2 * x / (log x)^2.

It deliberately does *not* contain any ψ / prime-power / partial summation machinery.
That belongs to later files.
-/

/-! ------------------------------------------------------------------
  Block A — constants and explicit θ-error model
------------------------------------------------------------------ -/

/--
External threshold from which the θ-backend is used.

At this stage we align it with `Y0`. This matches the large-range analytic role of
Appendix A, while keeping the file independent of the later proof machinery.
-/
noncomputable def XTheta : ℝ := (Y0 : ℝ)

/--
Draft coefficient slot for the main `1 / log^2` term.

Replace these coefficients by the exact Axler-style constants once the external
θ-error formula is fixed.
-/
noncomputable def thetaC1 : ℝ := 1

/--
Draft coefficient slot for the smaller `1 / log^3` correction term.
-/
noncomputable def thetaC2 : ℝ := (1 : ℝ) / 2

/--
Third slot kept explicit even if currently zero.

This keeps the file shape stable for the near-final pass where the exact external
formula is substituted.
-/
noncomputable def thetaC3 : ℝ := 0

/-- Main term of the external θ-error model. -/
noncomputable def epsThetaTerm1 (x : ℝ) : ℝ :=
  thetaC1 / (Real.log x)^2

/-- Lower-order logarithmic correction term. -/
noncomputable def epsThetaTerm2 (x : ℝ) : ℝ :=
  thetaC2 / (Real.log x)^3

/-- Residual term slot. -/
noncomputable def epsThetaTerm3 (_x : ℝ) : ℝ :=
  thetaC3

/-- Full external θ-error model. -/
noncomputable def epsTheta (x : ℝ) : ℝ :=
  epsThetaTerm1 x + epsThetaTerm2 x + epsThetaTerm3 x

@[simp] theorem XTheta_def : XTheta = (Y0 : ℝ) := rfl

@[simp] theorem thetaC1_def : thetaC1 = 1 := rfl
@[simp] theorem thetaC2_def : thetaC2 = (1 : ℝ) / 2 := rfl
@[simp] theorem thetaC3_def : thetaC3 = 0 := rfl

@[simp] theorem epsThetaTerm1_def (x : ℝ) :
    epsThetaTerm1 x = thetaC1 / (Real.log x)^2 := rfl

@[simp] theorem epsThetaTerm2_def (x : ℝ) :
    epsThetaTerm2 x = thetaC2 / (Real.log x)^3 := rfl

@[simp] theorem epsThetaTerm3_def (x : ℝ) :
    epsThetaTerm3 x = thetaC3 := rfl

@[simp] theorem epsTheta_def (x : ℝ) :
    epsTheta x = epsThetaTerm1 x + epsThetaTerm2 x + epsThetaTerm3 x := rfl


/-! ------------------------------------------------------------------
  Block B — domain lemmas
------------------------------------------------------------------ -/

theorem Y0_real_pos : 0 < (Y0 : ℝ) := by
  norm_num [Y0_def]

theorem Y0_real_gt_one : (1 : ℝ) < (Y0 : ℝ) := by
  norm_num [Y0_def]

theorem XTheta_pos : 0 < XTheta := by
  simpa [XTheta_def] using Y0_real_pos

theorem XTheta_nonneg : 0 ≤ XTheta := le_of_lt XTheta_pos

private theorem log_two_pos : 0 < Real.log (2 : ℝ) := by
  have : (1 : ℝ) < (2 : ℝ) := by norm_num
  exact Real.log_pos this

private theorem log_two_nonzero : Real.log (2 : ℝ) ≠ 0 := by
  have h := log_two_pos
  linarith

theorem exp_two_le_Y0 : Real.exp (2 : ℝ) ≤ (Y0 : ℝ) := by
  have he : Real.exp (1 : ℝ) < 3 := by
    simpa [Real.exp_one] using Real.e_lt_three
  have hrew : Real.exp (2 : ℝ) = Real.exp (1 : ℝ) * Real.exp (1 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have hlt9 : Real.exp (2 : ℝ) < 9 := by
    rw [hrew]
    nlinarith
  have h9 : (9 : ℝ) ≤ (Y0 : ℝ) := by
    norm_num [Y0_def]
  linarith

theorem log_Y0_ge_two : (2 : ℝ) ≤ Real.log (Y0 : ℝ) := by
  have hpos : 0 < (Y0 : ℝ) := Y0_real_pos
  rw [Real.le_log_iff_exp_le hpos]
  exact exp_two_le_Y0

theorem log_Y0_pos : 0 < Real.log (Y0 : ℝ) := by
  have h : (2 : ℝ) ≤ Real.log (Y0 : ℝ) := log_Y0_ge_two
  linarith

theorem x_ge_Y0_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    (Y0 : ℝ) ≤ x := by
  simpa [XTheta_def] using hx

theorem x_pos_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    0 < x := by
  have hx' : (Y0 : ℝ) ≤ x := x_ge_Y0_of_ge_XTheta hx
  linarith [Y0_real_pos]

theorem x_nonneg_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    0 ≤ x := le_of_lt (x_pos_of_ge_XTheta hx)

theorem x_ge_one_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    (1 : ℝ) ≤ x := by
  have hx' : (Y0 : ℝ) ≤ x := x_ge_Y0_of_ge_XTheta hx
  linarith [Y0_real_gt_one]

theorem x_sub_one_pos_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    0 < x - 1 := by
  have hx1 : (1 : ℝ) < x := by
    have hx' : (Y0 : ℝ) ≤ x := x_ge_Y0_of_ge_XTheta hx
    linarith [Y0_real_gt_one]
  linarith

theorem log_ge_two_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    (2 : ℝ) ≤ Real.log x := by
  have hmono :
      Real.log (Y0 : ℝ) ≤ Real.log x := by
    exact Real.monotone_log (le_of_lt Y0_real_pos) (x_ge_Y0_of_ge_XTheta hx)
  exact le_trans log_Y0_ge_two hmono

theorem log_pos_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    0 < Real.log x := by
  have h : (2 : ℝ) ≤ Real.log x := log_ge_two_of_ge_XTheta hx
  linarith

theorem log_sq_pos_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    0 < (Real.log x)^2 := by
  have hlog : 0 < Real.log x := log_pos_of_ge_XTheta hx
  positivity

theorem log_ne_zero_of_ge_XTheta
    {x : ℝ} (hx : XTheta ≤ x) :
    Real.log x ≠ 0 := by
  have hlog : 0 < Real.log x := log_pos_of_ge_XTheta hx
  linarith


/-! ------------------------------------------------------------------
  Block C — elementary analysis of epsTheta
------------------------------------------------------------------ -/

theorem thetaC1_nonneg : 0 ≤ thetaC1 := by
  rw [thetaC1_def]
  positivity

theorem thetaC2_nonneg : 0 ≤ thetaC2 := by
  rw [thetaC2_def]
  positivity

theorem thetaC3_nonneg : 0 ≤ thetaC3 := by
  rw [thetaC3_def]

theorem epsThetaTerm1_nonneg
    {x : ℝ} (hx : XTheta ≤ x) :
    0 ≤ epsThetaTerm1 x := by
  rw [epsThetaTerm1_def]
  positivity

theorem epsThetaTerm2_nonneg
    {x : ℝ} (hx : XTheta ≤ x) :
    0 ≤ epsThetaTerm2 x := by
  rw [epsThetaTerm2_def]
  positivity

theorem epsThetaTerm3_nonneg
    {x : ℝ} (hx : XTheta ≤ x) :
    0 ≤ epsThetaTerm3 x := by
  rw [epsThetaTerm3_def, thetaC3_def]

theorem epsTheta_nonneg
    {x : ℝ} (hx : XTheta ≤ x) :
    0 ≤ epsTheta x := by
  rw [epsTheta_def]
  linarith [epsThetaTerm1_nonneg hx, epsThetaTerm2_nonneg hx, epsThetaTerm3_nonneg hx]

/-! ------------------------------------------------------------------
  Block D — termwise calibration toward 2 / log^2
------------------------------------------------------------------ -/

/--
Main term calibration: exact.
-/
theorem epsThetaTerm1_le_piece
    {x : ℝ} (hx : XTheta ≤ x) :
    epsThetaTerm1 x ≤ 1 / (Real.log x)^2 := by
  rw [epsThetaTerm1_def, thetaC1_def]

/--
Lower-order term calibration:
`(1/2)/log^3 ≤ (1/2)/log^2` because `log x ≥ 1` on the large range.
-/
theorem epsThetaTerm2_le_piece
    {x : ℝ} (hx : XTheta ≤ x) :
    epsThetaTerm2 x ≤ ((1 : ℝ) / 2) / (Real.log x)^2 := by
  rw [epsThetaTerm2_def, thetaC2_def]
  have hlog_ge_one : (1 : ℝ) ≤ Real.log x := by
    have hlog_ge_two : (2 : ℝ) ≤ Real.log x := log_ge_two_of_ge_XTheta hx
    linarith
  have hpow_pos : 0 < (Real.log x)^3 := by positivity
  have hmain :
      (1 : ℝ) / (Real.log x)^3 ≤ (1 : ℝ) / (Real.log x)^2 := by
    have h :=
      (div_le_iff hpow_pos).2 ?_
    · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    · field_simp [log_ne_zero_of_ge_XTheta hx]
      ring_nf
      exact hlog_ge_one
  linarith

/--
Residual term calibration: exact because the current slot is zero.
-/
theorem epsThetaTerm3_le_piece
    {x : ℝ} (hx : XTheta ≤ x) :
    epsThetaTerm3 x ≤ 0 := by
  rw [epsThetaTerm3_def, thetaC3_def]

theorem epsTheta_le_two_over_log_sq
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    epsTheta x ≤ 2 / (Real.log x)^2 := by
  have hx : XTheta ≤ x := by
    simpa [XTheta_def] using hx0
  rw [epsTheta_def]
  have h1 : epsThetaTerm1 x ≤ 1 / (Real.log x)^2 := epsThetaTerm1_le_piece hx
  have h2 : epsThetaTerm2 x ≤ ((1 : ℝ) / 2) / (Real.log x)^2 := epsThetaTerm2_le_piece hx
  have h3 : epsThetaTerm3 x ≤ 0 := epsThetaTerm3_le_piece hx
  have hlogsq_pos : 0 < (Real.log x)^2 := log_sq_pos_of_ge_XTheta hx
  have hsum :
      1 / (Real.log x)^2 + ((1 : ℝ) / 2) / (Real.log x)^2 + 0
        ≤ 2 / (Real.log x)^2 := by
    have hcoeff : (1 : ℝ) + (1 : ℝ) / 2 + 0 ≤ 2 := by norm_num
    have hrew :
        1 / (Real.log x)^2 + ((1 : ℝ) / 2) / (Real.log x)^2 + 0
          = ((1 : ℝ) + (1 : ℝ) / 2 + 0) / (Real.log x)^2 := by
      field_simp [hlogsq_pos.ne']
      ring
    rw [hrew]
    exact div_le_div_of_nonneg_right hcoeff (le_of_lt hlogsq_pos)
  linarith

theorem epsTheta_mul_le_two_x_over_log_sq
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    epsTheta x * x ≤ 2 * x / (Real.log x)^2 := by
  have hx : XTheta ≤ x := by
    simpa [XTheta_def] using hx0
  have hxpos : 0 < x := x_pos_of_ge_XTheta hx
  have hmain : epsTheta x ≤ 2 / (Real.log x)^2 := epsTheta_le_two_over_log_sq hx0
  have hmul := mul_le_mul_of_nonneg_right hmain (le_of_lt hxpos)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

end ThetaExternalConstants
end AppendixA
end Pivot
end Lehmer