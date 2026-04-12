-- FILE: Lean/Lehmer/Pivot/AppendixA/ThetaBroadbentTheorem1.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixA.ThetaDefs : def
-/

import Lehmer.Prelude
import Lehmer.Pivot.AppendixA.ThetaDefs

namespace Lehmer
namespace Pivot
namespace AppendixA
namespace ThetaBroadbentTheorem1

open scoped Real

noncomputable def broadbentK4Constant : ℝ := 151.3

@[simp] theorem broadbentK4Constant_def :
    broadbentK4Constant = 151.3 := rfl

noncomputable def broadbentK4Error (x : ℝ) : ℝ :=
  broadbentK4Constant * x / (Real.log x)^4

@[simp] theorem broadbentK4Error_def (x : ℝ) :
    broadbentK4Error x = broadbentK4Constant * x / (Real.log x)^4 := rfl

def table9TailThreshold : ℝ := Real.exp 6000

@[simp] theorem table9TailThreshold_def :
    table9TailThreshold = Real.exp 6000 := rfl

/--
Tail ψ-side placeholder constant.

This should later be replaced by the literal constant extracted from the chosen
Table 9 / tail ψ-route.
-/
noncomputable def cPsiTail : ℝ := 1

private theorem cPsiTail_le_target :
    cPsiTail ≤ (151.3 : ℝ) := by
  norm_num [cPsiTail]

/--
Placeholder ψ-side interface for the tail route.
-/
noncomputable def psiUpTo (x : ℝ) : ℝ := thetaUpTo x

@[simp] theorem psiUpTo_def (x : ℝ) :
    psiUpTo x = thetaUpTo x := rfl

private theorem x_pos_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 < x := by
  linarith

private theorem x_nonneg_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 ≤ x := by
  linarith

private theorem one_lt_of_two_le
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x) :
    (1 : ℝ) < x := by
  linarith

private theorem one_lt_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    (1 : ℝ) < x := by
  have hbase : (1 : ℝ) < Real.exp 20 := by
    have h20' : (0 : ℝ) < 20 := by
      norm_num
    simpa using Real.one_lt_exp h20'
  linarith

private theorem one_lt_of_pow19_le
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x) :
    (1 : ℝ) < x := by
  have hbase : (1 : ℝ) < (10 : ℝ)^19 := by
    norm_num
  linarith

private theorem one_lt_of_tail
    {x : ℝ}
    (ht : table9TailThreshold ≤ x) :
    (1 : ℝ) < x := by
  have hbase : (1 : ℝ) < table9TailThreshold := by
    rw [table9TailThreshold_def]
    have h6000 : (0 : ℝ) < 6000 := by
      norm_num
    simpa using Real.one_lt_exp h6000
  linarith

private theorem log_pos_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 < Real.log x := by
  exact Real.log_pos hx1

private theorem log_ne_zero_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    Real.log x ≠ 0 := by
  have hlog : 0 < Real.log x := log_pos_of_one_lt hx1
  linarith

private theorem log_pow4_pos_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 < (Real.log x)^4 := by
  have hlog : 0 < Real.log x := log_pos_of_one_lt hx1
  positivity

private theorem factor_nonneg_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 ≤ x / (Real.log x)^4 := by
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlog4 : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  positivity

private theorem thetaUpTo_eq_zero_of_one_lt_and_lt_two
    {x : ℝ}
    (hx1 : (1 : ℝ) < x)
    (hx2 : x < 2) :
    thetaUpTo x = 0 := by
  have hge : (1 : ℤ) ≤ ⌊x⌋ := by
    have htmp : (1 : ℤ) < ⌊x⌋ + 1 := by
      exact Int.lt_floor_add_one hx1
    linarith
  have hlt : ⌊x⌋ < (2 : ℤ) := by
    exact Int.floor_lt.2 hx2
  have hfloor : ⌊x⌋ = (1 : ℤ) := by
    linarith
  unfold thetaUpTo primesUpToFloor
  rw [hfloor]
  simp

private theorem theta_k4_abs_on_one_two
    {x : ℝ}
    (hx1 : (1 : ℝ) < x)
    (hx2 : x < 2) :
    |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
  have htheta : thetaUpTo x = 0 := thetaUpTo_eq_zero_of_one_lt_and_lt_two hx1 hx2
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_one_lt hx1
  have hloglt1 : Real.log x < 1 := by
    have hle : Real.log x ≤ x - 1 := by
      exact Real.log_le_sub_one_of_pos hxpos
    linarith
  have hlog4lt : (Real.log x)^4 < (151.3 : ℝ) := by
    nlinarith [hlogpos, hloglt1]
  have hfrac : (1 : ℝ) ≤ (151.3 : ℝ) / (Real.log x)^4 := by
    exact (one_le_div_iff (log_pow4_pos_of_one_lt hx1)).2 (le_of_lt hlog4lt)
  have hmul : x ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    have := mul_le_mul_of_nonneg_left hfrac hxnonneg
    simpa [one_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this
  rw [htheta]
  simpa [abs_of_nonneg hxnonneg] using hmul

/-
Source theorem:
direct specialization of the Table 13 small-range explicit computation
for k = 4 on `[2, exp 20)`, with maximal constant `151.2235`.

This theorem is intentionally kept as a raw source block:
no certificate plumbing, no downstream reformulation, no regime split.
-/
private theorem table13_k4_abs_source_raw
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  sorry

/--
Table 13 small-range absolute theorem:
`|θ(x) - x| ≤ 151.2235 * x / log(x)^4`
on `[2, exp 20)`, matching the maximal direct-computation value cited by
Broadbent for the k = 4 route.
-/
private theorem table13_k4_abs_source
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  exact table13_k4_abs_source_raw hx2 h20

/-
Source theorem:
direct specialization of Broadbent–Kadiri–Lumley–Ng–Wilk, Table 12,
entry `C_{20,4} = 13.475`, on `[exp 20, 10^19)`.

Keep the raw theorem in the normalized error form
`thetaUpTo x - x ≥ -...`.
Do not perform lower-side rewriting here; that is the job of the wrapper
theorems below.
-/
private theorem table12_k4_b20_source_raw
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 := by
  sorry

/--
Table 12 lower-side theorem:
`θ(x) - x > -C_{20,4} x / log(x)^4`
with `C_{20,4} = 13.475` on `[exp 20, 10^19)`.
-/
private theorem table12_k4_b20_source_core
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 := by
  exact table12_k4_b20_source_raw h20 h19

private theorem table12_k4_b20_source
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have hcore :
      thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_source_core h20 h19
  linarith

private theorem exp20_lt_pow10_19 : Real.exp 20 < (10 : ℝ)^19 := by
  have he : Real.exp (1 : ℝ) < 3 := by
    simpa [Real.exp_one] using Real.e_lt_three
  have hrew : Real.exp (20 : ℝ) = (Real.exp (1 : ℝ)) ^ (20 : ℕ) := by
    rw [show (20 : ℝ) = (20 : ℕ) by norm_num, Real.exp_nat_mul]
  have hlt : Real.exp (20 : ℝ) < (3 : ℝ) ^ (20 : ℕ) := by
    rw [hrew]
    exact pow_lt_pow_of_lt_left (by positivity) he 20
  have hpow : (3 : ℝ) ^ (20 : ℕ) < (10 : ℝ) ^ (19 : ℕ) := by
    norm_num
  exact lt_trans hlt (by simpa using hpow)

private theorem table11_regime_contains_current_large_range
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x)
    (h6000 : x < table9TailThreshold) :
    Real.exp 20 ≤ x ∧ x < Real.exp 25000 := by
  constructor
  · have h : Real.exp 20 < (10 : ℝ)^19 := exp20_lt_pow10_19
    linarith
  · rw [table9TailThreshold_def] at h6000
    have h6000_25000 : Real.exp 6000 < Real.exp 25000 := by
      apply Real.exp_lt_exp.mpr
      norm_num
    linarith

/-
Source theorem:
direct specialization of Broadbent–Kadiri–Lumley–Ng–Wilk, Table 11,
entry `B_4(20) = 57.184`, valid on `[exp 20, exp 25000)`.

Closure pattern:
1. keep this theorem on the full published regime;
2. do not mix it with the narrower Lehmer subrange;
3. let `table11_regime_contains_current_large_range` perform the domain
   reduction downstream.
-/
private theorem table11_k4_b20_source_on_full_regime
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h25000 : x < Real.exp 25000) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  sorry

private theorem table11_k4_b20_source
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x)
    (h6000 : x < table9TailThreshold) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  rcases table11_regime_contains_current_large_range h19 h6000 with ⟨h20, h25000⟩
  exact table11_k4_b20_source_on_full_regime h20 h25000

/-
Source theorem:
specialize Büthe [4, Thm. 2, (1.7)] to the `thetaUpTo` interface
on `2 ≤ x < 10^19`, first in the natural form `thetaUpTo x < x`,
then normalize to `thetaUpTo x - x < 0` by `linarith`.

Do not mix this source closure with the downstream upper-bound theorem.
Its sole job is to provide negativity of `thetaUpTo x - x`.
-/
private theorem buthe_theta_lt_x_upto_1e19_source
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x < 0 := by
  have hsrc : thetaUpTo x < x := by
    sorry
  linarith

/--
Source consequence of Büthe [4, Theorem 2, (1.7)]:
for all `x < 10^19`, one has `θ(x) < x`.
-/
private theorem buthe_theta_lt_x_upto_1e19
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x < x := by
  have h : thetaUpTo x - x < 0 :=
    buthe_theta_lt_x_upto_1e19_source hx2 h19
  linarith

/--
Table 9 ψ-side tail source theorem placeholder.
-/
private theorem table9_psi_source_raw
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    |psiUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 := by
  sorry

private theorem theta_k4_abs_from_table9
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
  have hpsi :
      |psiUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 :=
    table9_psi_source_raw h6000
  have hpsi' :
      |thetaUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 := by
    simpa [psiUpTo] using hpsi
  have hx1 : (1 : ℝ) < x := one_lt_of_tail h6000
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_one_lt hx1
  have hc : cPsiTail ≤ (151.3 : ℝ) := cPsiTail_le_target
  have hscale :
      cPsiTail * x / (Real.log x)^4 ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    nlinarith
  exact le_trans hpsi' hscale

private theorem theta_k4_lower_from_one_two
    {x : ℝ}
    (hx1 : (1 : ℝ) < x)
    (hx2 : x < 2) :
    x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have habs :
      |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 :=
    theta_k4_abs_on_one_two hx1 hx2
  have hleft :
      -((151.3 : ℝ) * x / (Real.log x)^4) ≤ thetaUpTo x - x := by
    exact (abs_le.mp habs).1
  linarith

private theorem theta_k4_upper_from_one_two
    {x : ℝ}
    (hx1 : (1 : ℝ) < x)
    (hx2 : x < 2) :
    thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 := by
  have habs :
      |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 :=
    theta_k4_abs_on_one_two hx1 hx2
  have hright :
      thetaUpTo x - x ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    exact (abs_le.mp habs).2
  linarith

private theorem theta_k4_lower_from_table13
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have habs :
      |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 :=
    table13_k4_abs_source hx2 h20
  have hleft :
      -((151.2235 : ℝ) * x / (Real.log x)^4) ≤ thetaUpTo x - x := by
    exact (abs_le.mp habs).1
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_one_lt hx1
  have hscale :
      (151.2235 : ℝ) * x / (Real.log x)^4 ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    nlinarith
  linarith

private theorem theta_k4_upper_from_table13
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 := by
  have habs :
      |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 :=
    table13_k4_abs_source hx2 h20
  have hright :
      thetaUpTo x - x ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
    exact (abs_le.mp habs).2
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_one_lt hx1
  have hscale :
      (151.2235 : ℝ) * x / (Real.log x)^4 ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    nlinarith
  linarith

private theorem theta_k4_lower_from_table12
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have htab :
      x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x :=
    table12_k4_b20_source h20 h19
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_one_lt hx1
  have hscale :
      (13.475 : ℝ) * x / (Real.log x)^4 ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    nlinarith
  linarith

private theorem theta_k4_lower_from_table11
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x)
    (h6000 : x < table9TailThreshold) :
    x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have habs :
      |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 :=
    table11_k4_b20_source h19 h6000
  have hleft :
      -((57.184 : ℝ) * x / (Real.log x)^4) ≤ thetaUpTo x - x := by
    exact (abs_le.mp habs).1
  have hx1 : (1 : ℝ) < x := one_lt_of_pow19_le h19
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_one_lt hx1
  have hscale :
      (57.184 : ℝ) * x / (Real.log x)^4 ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    nlinarith
  linarith

private theorem theta_k4_lower_from_table9
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have habs :
      |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 :=
    theta_k4_abs_from_table9 h6000
  have hleft :
      -((151.3 : ℝ) * x / (Real.log x)^4) ≤ thetaUpTo x - x := by
    exact (abs_le.mp habs).1
  linarith

private theorem theta_k4_upper_upto_1e19
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 := by
  have hbuthe : thetaUpTo x < x := by
    exact buthe_theta_lt_x_upto_1e19 hx2 h19
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hfac : 0 ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    have hxnonneg : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_one_lt hx1
    positivity
  linarith

private theorem theta_k4_upper_from_table11
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x)
    (h6000 : x < table9TailThreshold) :
    thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 := by
  have habs :
      |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 :=
    table11_k4_b20_source h19 h6000
  have hright :
      thetaUpTo x - x ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
    exact (abs_le.mp habs).2
  have hx1 : (1 : ℝ) < x := one_lt_of_pow19_le h19
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_one_lt hx1
  have hscale :
      (57.184 : ℝ) * x / (Real.log x)^4 ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    nlinarith
  linarith

private theorem theta_k4_upper_from_table9
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 := by
  have habs :
      |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 :=
    theta_k4_abs_from_table9 h6000
  have hright :
      thetaUpTo x - x ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
    exact (abs_le.mp habs).2
  linarith

private theorem theta_k4_lower_source
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  by_cases hx2 : x < 2
  · exact theta_k4_lower_from_one_two hx1 hx2
  · have hx2' : (2 : ℝ) ≤ x := le_of_not_gt hx2
    by_cases h19 : x < (10 : ℝ)^19
    · by_cases h20 : x < Real.exp 20
      · exact theta_k4_lower_from_table13 hx2' h20
      · exact theta_k4_lower_from_table12 (le_of_not_gt h20) h19
    · by_cases h6000 : x < table9TailThreshold
      · exact theta_k4_lower_from_table11 (le_of_not_gt h19) h6000
      · exact theta_k4_lower_from_table9 (le_of_not_gt h6000)

private theorem theta_k4_upper_source
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 := by
  by_cases hx2 : x < 2
  · exact theta_k4_upper_from_one_two hx1 hx2
  · have hx2' : (2 : ℝ) ≤ x := le_of_not_gt hx2
    by_cases h19 : x < (10 : ℝ)^19
    · by_cases h20 : x < Real.exp 20
      · exact theta_k4_upper_from_table13 hx2' h20
      · exact theta_k4_upper_upto_1e19 hx2' h19
    · by_cases h6000 : x < table9TailThreshold
      · exact theta_k4_upper_from_table11 (le_of_not_gt h19) h6000
      · exact theta_k4_upper_from_table9 (le_of_not_gt h6000)

private theorem theta_k4_case_X0_eq_one_lower
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    x * (1 - (151.3 : ℝ) / (Real.log x)^4) ≤ thetaUpTo x := by
  have hlower :
      x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x :=
    theta_k4_lower_source hx1
  have hrew :
      x * (1 - (151.3 : ℝ) / (Real.log x)^4)
        = x - (151.3 : ℝ) * x / (Real.log x)^4 := by
    ring
  rw [hrew]
  exact hlower

private theorem theta_k4_case_X1_eq_one_upper
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    thetaUpTo x ≤ x * (1 + (151.3 : ℝ) / (Real.log x)^4) := by
  have hupper :
      thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 :=
    theta_k4_upper_source hx1
  have hrew :
      x * (1 + (151.3 : ℝ) / (Real.log x)^4)
        = x + (151.3 : ℝ) * x / (Real.log x)^4 := by
    ring
  rw [hrew]
  exact hupper

theorem theta_k4_case_X0_X1_eq_one
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    |thetaUpTo x - x| ≤ (151.3 : ℝ) * x / (Real.log x)^4 := by
  have hlower :
      x - (151.3 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x :=
    theta_k4_lower_source hx1
  have hupper :
      thetaUpTo x ≤ x + (151.3 : ℝ) * x / (Real.log x)^4 :=
    theta_k4_upper_source hx1
  exact abs_le.mpr (by linarith)

end ThetaBroadbentTheorem1
end AppendixA
end Pivot
end Lehmer