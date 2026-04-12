-- FILE: Lean/Lehmer/Pivot/AppendixA/ThetaBroadbentSources.lean
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
namespace ThetaBroadbentSources

open scoped Real

def table9TailThreshold : ℝ := Real.exp 6000

@[simp] theorem table9TailThreshold_def :
    table9TailThreshold = Real.exp 6000 := rfl

noncomputable def cPsiTail : ℝ := 1

@[simp] theorem cPsiTail_def :
    cPsiTail = 1 := rfl

theorem cPsiTail_le_target :
    cPsiTail ≤ (151.3 : ℝ) := by
  norm_num [cPsiTail]

noncomputable def psiUpTo (x : ℝ) : ℝ := thetaUpTo x

@[simp] theorem psiUpTo_def (x : ℝ) :
    psiUpTo x = thetaUpTo x := rfl

theorem x_pos_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 < x := by
  linarith

theorem x_nonneg_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 ≤ x := by
  linarith

theorem one_lt_of_two_le
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x) :
    (1 : ℝ) < x := by
  linarith

theorem one_lt_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    (1 : ℝ) < x := by
  have hbase : (1 : ℝ) < Real.exp 20 := by
    have h20' : (0 : ℝ) < 20 := by
      norm_num
    simpa using Real.one_lt_exp h20'
  linarith

theorem one_lt_of_pow19_le
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x) :
    (1 : ℝ) < x := by
  have hbase : (1 : ℝ) < (10 : ℝ)^19 := by
    norm_num
  linarith

theorem one_lt_of_tail
    {x : ℝ}
    (ht : table9TailThreshold ≤ x) :
    (1 : ℝ) < x := by
  have hbase : (1 : ℝ) < table9TailThreshold := by
    rw [table9TailThreshold_def]
    have h6000 : (0 : ℝ) < 6000 := by
      norm_num
    simpa using Real.one_lt_exp h6000
  linarith

theorem log_pos_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 < Real.log x := by
  exact Real.log_pos hx1

theorem log_ne_zero_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    Real.log x ≠ 0 := by
  have hlog : 0 < Real.log x := log_pos_of_one_lt hx1
  linarith

theorem log_pow4_pos_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 < (Real.log x)^4 := by
  have hlog : 0 < Real.log x := log_pos_of_one_lt hx1
  positivity

theorem factor_nonneg_of_one_lt
    {x : ℝ}
    (hx1 : (1 : ℝ) < x) :
    0 ≤ x / (Real.log x)^4 := by
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlog4 : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  positivity

theorem log_pos_of_two_le
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x) :
    0 < Real.log x := by
  exact log_pos_of_one_lt (one_lt_of_two_le hx2)

theorem log_ne_zero_of_two_le
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x) :
    Real.log x ≠ 0 := by
  exact log_ne_zero_of_one_lt (one_lt_of_two_le hx2)

theorem factor_nonneg_of_two_le
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x) :
    0 ≤ x / (Real.log x)^4 := by
  exact factor_nonneg_of_one_lt (one_lt_of_two_le hx2)

theorem log_pos_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    0 < Real.log x := by
  exact log_pos_of_one_lt (one_lt_of_exp20_le h20)

theorem log_ne_zero_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    Real.log x ≠ 0 := by
  exact log_ne_zero_of_one_lt (one_lt_of_exp20_le h20)

theorem factor_nonneg_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    0 ≤ x / (Real.log x)^4 := by
  exact factor_nonneg_of_one_lt (one_lt_of_exp20_le h20)

theorem log_pos_of_pow19_le
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x) :
    0 < Real.log x := by
  exact log_pos_of_one_lt (one_lt_of_pow19_le h19)

theorem log_ne_zero_of_pow19_le
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x) :
    Real.log x ≠ 0 := by
  exact log_ne_zero_of_one_lt (one_lt_of_pow19_le h19)

theorem factor_nonneg_of_pow19_le
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x) :
    0 ≤ x / (Real.log x)^4 := by
  exact factor_nonneg_of_one_lt (one_lt_of_pow19_le h19)

theorem log_pos_of_tail
    {x : ℝ}
    (ht : table9TailThreshold ≤ x) :
    0 < Real.log x := by
  exact log_pos_of_one_lt (one_lt_of_tail ht)

theorem log_ne_zero_of_tail
    {x : ℝ}
    (ht : table9TailThreshold ≤ x) :
    Real.log x ≠ 0 := by
  exact log_ne_zero_of_one_lt (one_lt_of_tail ht)

theorem factor_nonneg_of_tail
    {x : ℝ}
    (ht : table9TailThreshold ≤ x) :
    0 ≤ x / (Real.log x)^4 := by
  exact factor_nonneg_of_one_lt (one_lt_of_tail ht)

private theorem table13_constant_nonneg :
    0 ≤ (151.2235 : ℝ) := by
  norm_num

private theorem table12_constant_nonneg :
    0 ≤ (13.475 : ℝ) := by
  norm_num

private theorem table11_constant_nonneg :
    0 ≤ (57.184 : ℝ) := by
  norm_num

private theorem cPsiTail_le_table11_constant :
    cPsiTail ≤ (57.184 : ℝ) := by
  norm_num [cPsiTail]

theorem exp20_lt_pow10_19 : Real.exp 20 < (10 : ℝ)^19 := by
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

private theorem pow19_lt_tail_threshold :
    (10 : ℝ)^19 < table9TailThreshold := by
  rw [table9TailThreshold_def]
  have h2e : (2 : ℝ) < Real.exp (1 : ℝ) := by
    simpa using Real.two_lt_exp
  have hpow1 : (10 : ℝ)^19 < (32 : ℝ)^19 := by
    norm_num
  have hpow2 : (32 : ℝ)^19 ≤ (2 : ℝ)^6000 := by
    norm_num
  have hpow3 : (2 : ℝ)^6000 < (Real.exp (1 : ℝ)) ^ (6000 : ℕ) := by
    simpa using pow_lt_pow_of_lt_left (by positivity) h2e 6000
  have hexp : Real.exp 6000 = (Real.exp (1 : ℝ)) ^ (6000 : ℕ) := by
    rw [show (6000 : ℝ) = (6000 : ℕ) by norm_num, Real.exp_nat_mul]
  exact lt_trans hpow1 (lt_of_le_of_lt hpow2 (by simpa [hexp] using hpow3))

theorem table11_regime_contains_current_large_range
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

theorem thetaUpTo_eq_zero_of_one_lt_and_lt_two
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

theorem theta_k4_abs_on_one_two
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

private theorem thetaUpTo_eq_log_two_of_two_le_and_lt_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    thetaUpTo x = Real.log 2 := by
  have hge : (2 : ℤ) ≤ ⌊x⌋ := by
    exact Int.le_floor.2 hx2
  have hlt : ⌊x⌋ < (3 : ℤ) := by
    exact Int.floor_lt.2 hx3
  have hfloor : ⌊x⌋ = (2 : ℤ) := by
    linarith
  unfold thetaUpTo primesUpToFloor
  rw [hfloor]
  simp

private theorem log_two_nonneg : 0 ≤ Real.log (2 : ℝ) := by
  exact le_of_lt (Real.log_pos (by norm_num))

private theorem log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)

private theorem thetaUpTo_sub_eq_log_two_sub_on_two_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    thetaUpTo x - x = Real.log 2 - x := by
  rw [thetaUpTo_eq_log_two_of_two_le_and_lt_three hx2 hx3]

private theorem abs_thetaUpTo_sub_x_on_two_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    |thetaUpTo x - x| = x - Real.log 2 := by
  rw [thetaUpTo_sub_eq_log_two_sub_on_two_three hx2 hx3]
  have hnonpos : Real.log 2 - x ≤ 0 := by
    linarith [log_two_le_one, hx2]
  rw [abs_of_nonpos hnonpos]
  ring

private theorem thetaUpTo_lt_x_on_two_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    thetaUpTo x < x := by
  rw [thetaUpTo_eq_log_two_of_two_le_and_lt_three hx2 hx3]
  linarith [log_two_le_one, hx2]

private theorem log_lt_two_on_two_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    Real.log x < 2 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hle : Real.log x ≤ x - 1 := by
    exact Real.log_le_sub_one_of_pos hxpos
  linarith

private theorem log_pow4_lt_table13_constant_on_two_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    (Real.log x)^4 < (151.2235 : ℝ) := by
  have hlogpos : 0 < Real.log x := log_pos_of_two_le hx2
  have hloglt2 : Real.log x < 2 := log_lt_two_on_two_three hx2 hx3
  have hlt16 : (Real.log x)^4 < (16 : ℝ) := by
    nlinarith
  linarith

private theorem table13_rhs_dominates_x_on_two_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    x ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hpow : (Real.log x)^4 < (151.2235 : ℝ) :=
    log_pow4_lt_table13_constant_on_two_three hx2 hx3
  have hfrac : (1 : ℝ) ≤ (151.2235 : ℝ) / (Real.log x)^4 := by
    exact (one_le_div_iff hlog4pos).2 (le_of_lt hpow)
  have hmul := mul_le_mul_of_nonneg_left hfrac hxnonneg
  simpa [one_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul

private theorem table13_k4_abs_source_on_two_three
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (hx3 : x < 3) :
    |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  rw [abs_thetaUpTo_sub_x_on_two_three hx2 hx3]
  have hle_x : x - Real.log 2 ≤ x := by
    linarith [log_two_nonneg]
  exact le_trans hle_x (table13_rhs_dominates_x_on_two_three hx2 hx3)

private theorem log_two_add_log_three_eq_log_six :
    Real.log 2 + Real.log 3 = Real.log 6 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  symm
  rw [Real.log_mul h2 h3]
  norm_num

private theorem log_six_add_log_five_eq_log_thirty :
    Real.log 6 + Real.log 5 = Real.log 30 := by
  have h6 : (6 : ℝ) ≠ 0 := by norm_num
  have h5 : (5 : ℝ) ≠ 0 := by norm_num
  symm
  rw [Real.log_mul h6 h5]
  norm_num

private theorem log_two_add_log_three_add_log_five_eq_log_thirty :
    Real.log 2 + Real.log 3 + Real.log 5 = Real.log 30 := by
  rw [log_two_add_log_three_eq_log_six, log_six_add_log_five_eq_log_thirty]
  ring

private theorem log_thirty_add_log_seven_eq_log_two_hundred_ten :
    Real.log 30 + Real.log 7 = Real.log 210 := by
  have h30 : (30 : ℝ) ≠ 0 := by norm_num
  have h7 : (7 : ℝ) ≠ 0 := by norm_num
  symm
  rw [Real.log_mul h30 h7]
  norm_num

private theorem thetaUpTo_eq_log_two_hundred_ten_of_seven_le_and_lt_eleven
    {x : ℝ}
    (hx7 : (7 : ℝ) ≤ x)
    (hx11 : x < 11) :
    thetaUpTo x = Real.log 210 := by
  by_cases hx8 : x < 8
  · have hge : (7 : ℤ) ≤ ⌊x⌋ := by
      exact Int.le_floor.2 hx7
    have hlt : ⌊x⌋ < (8 : ℤ) := by
      exact Int.floor_lt.2 hx8
    have hfloor : ⌊x⌋ = (7 : ℤ) := by
      linarith
    unfold thetaUpTo primesUpToFloor
    rw [hfloor]
    simpa [log_two_add_log_three_add_log_five_eq_log_thirty,
      log_thirty_add_log_seven_eq_log_two_hundred_ten, add_assoc]
  · by_cases hx9 : x < 9
    · have hx8' : (8 : ℝ) ≤ x := le_of_not_gt hx8
      have hge : (8 : ℤ) ≤ ⌊x⌋ := by
        exact Int.le_floor.2 hx8'
      have hlt : ⌊x⌋ < (9 : ℤ) := by
        exact Int.floor_lt.2 hx9
      have hfloor : ⌊x⌋ = (8 : ℤ) := by
        linarith
        unfold thetaUpTo primesUpToFloor
      rw [hfloor]
      simpa [log_two_add_log_three_add_log_five_eq_log_thirty,
        log_thirty_add_log_seven_eq_log_two_hundred_ten, add_assoc]
    · by_cases hx10 : x < 10
      · have hx9' : (9 : ℝ) ≤ x := le_of_not_gt hx9
        have hge : (9 : ℤ) ≤ ⌊x⌋ := by
          exact Int.le_floor.2 hx9'
        have hlt : ⌊x⌋ < (10 : ℤ) := by
          exact Int.floor_lt.2 hx10
        have hfloor : ⌊x⌋ = (9 : ℤ) := by
          linarith
        unfold thetaUpTo primesUpToFloor
        rw [hfloor]
        simpa [log_two_add_log_three_add_log_five_eq_log_thirty,
          log_thirty_add_log_seven_eq_log_two_hundred_ten, add_assoc]
      · have hx10' : (10 : ℝ) ≤ x := le_of_not_gt hx10
        have hge : (10 : ℤ) ≤ ⌊x⌋ := by
          exact Int.le_floor.2 hx10'
        have hlt : ⌊x⌋ < (11 : ℤ) := by
          exact Int.floor_lt.2 hx11
        have hfloor : ⌊x⌋ = (10 : ℤ) := by
          linarith
        unfold thetaUpTo primesUpToFloor
        rw [hfloor]
        simpa [log_two_add_log_three_add_log_five_eq_log_thirty,
          log_thirty_add_log_seven_eq_log_two_hundred_ten, add_assoc]

private theorem log_two_hundred_ten_lt_eight :
    Real.log 210 < 8 := by
  have h210pos : (0 : ℝ) < 210 := by norm_num
  rw [Real.log_lt_iff_lt_exp h210pos]
  have he : (2 : ℝ) < Real.exp (1 : ℝ) := by
    simpa using Real.two_lt_exp
  have hpow : (2 : ℝ) ^ (8 : ℕ) < (Real.exp (1 : ℝ)) ^ (8 : ℕ) := by
    exact pow_lt_pow_of_lt_left (by positivity) he 8
  have h210lt : (210 : ℝ) < (2 : ℝ) ^ (8 : ℕ) := by
    norm_num
  have hrew : Real.exp (8 : ℝ) = (Real.exp (1 : ℝ)) ^ (8 : ℕ) := by
    rw [show (8 : ℝ) = (8 : ℕ) by norm_num, Real.exp_nat_mul]
  exact lt_trans h210lt (by simpa [hrew] using hpow)

private theorem thetaUpTo_lt_x_on_seven_eight
    {x : ℝ}
    (hx7 : (7 : ℝ) ≤ x)
    (hx8 : x < 8) :
    thetaUpTo x < x := by
  have hx11 : x < 11 := by linarith
  rw [thetaUpTo_eq_log_two_hundred_ten_of_seven_le_and_lt_eleven hx7 hx11]
  linarith [log_two_hundred_ten_lt_eight, hx7]

private theorem thetaUpTo_lt_x_on_eight_eleven
    {x : ℝ}
    (hx8 : (8 : ℝ) ≤ x)
    (hx11 : x < 11) :
    thetaUpTo x < x := by
  have hx7 : (7 : ℝ) ≤ x := by linarith
  rw [thetaUpTo_eq_log_two_hundred_ten_of_seven_le_and_lt_eleven hx7 hx11]
  linarith [log_two_hundred_ten_lt_eight, hx8]

private theorem table13_k4_abs_external_from_three
    {x : ℝ}
    (hx3 : (3 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_two_le hx2
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_two_le hx2
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_two_le hx2
  sorry

private theorem table13_k4_abs_source_core
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  by_cases hx3 : x < 3
  · exact table13_k4_abs_source_on_two_three hx2 hx3
  · exact table13_k4_abs_external_from_three (le_of_not_gt hx3) h20

theorem table13_k4_abs_source_raw
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    |thetaUpTo x - x| ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  exact table13_k4_abs_source_core hx2 h20

private theorem table13_k4_abs_source_raw_left
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    -((151.2235 : ℝ) * x / (Real.log x)^4) ≤ thetaUpTo x - x := by
  exact (abs_le.mp (table13_k4_abs_source_raw hx2 h20)).1

private theorem table13_k4_abs_source_raw_right
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h20 : x < Real.exp 20) :
    thetaUpTo x - x ≤ (151.2235 : ℝ) * x / (Real.log x)^4 := by
  exact (abs_le.mp (table13_k4_abs_source_raw hx2 h20)).2

private theorem two_lt_exp20 : (2 : ℝ) < Real.exp 20 := by
  have h2e : (2 : ℝ) < Real.exp (1 : ℝ) := by
    simpa using Real.two_lt_exp
  have hpow : (2 : ℝ) < (Real.exp (1 : ℝ)) ^ (20 : ℕ) := by
    nlinarith
  have hrew : Real.exp (20 : ℝ) = (Real.exp (1 : ℝ)) ^ (20 : ℕ) := by
    rw [show (20 : ℝ) = (20 : ℕ) by norm_num, Real.exp_nat_mul]
  simpa [hrew] using hpow

private theorem three_lt_exp20 : (3 : ℝ) < Real.exp 20 := by
  have h2e : (2 : ℝ) < Real.exp (1 : ℝ) := by
    simpa using Real.two_lt_exp
  have hpow : (3 : ℝ) < (Real.exp (1 : ℝ)) ^ (20 : ℕ) := by
    nlinarith
  have hrew : Real.exp (20 : ℝ) = (Real.exp (1 : ℝ)) ^ (20 : ℕ) := by
    rw [show (20 : ℝ) = (20 : ℕ) by norm_num, Real.exp_nat_mul]
  simpa [hrew] using hpow

private theorem two_le_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    (2 : ℝ) ≤ x := by
  linarith [two_lt_exp20]

private theorem three_le_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    (3 : ℝ) ≤ x := by
  linarith [three_lt_exp20]

private theorem thetaUpTo_le_x_of_lt
    {x : ℝ}
    (h : thetaUpTo x < x) :
    thetaUpTo x ≤ x := by
  linarith

private theorem thetaUpTo_sub_x_lt_zero_of_lt
    {x : ℝ}
    (h : thetaUpTo x < x) :
    thetaUpTo x - x < 0 := by
  linarith

private theorem buthe_theta_lt_x_upto_1e19_external_from_eleven_normalized_kernel
    {x : ℝ}
    (hx11 : (11 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x < 0 := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx3 : (3 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_two_le hx2
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_two_le hx2
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_two_le hx2
  sorry

private theorem buthe_theta_lt_x_upto_1e19_external_from_eleven_normalized
    {x : ℝ}
    (hx11 : (11 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x < 0 := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx3 : (3 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_two_le hx2
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_two_le hx2
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_two_le hx2
  exact buthe_theta_lt_x_upto_1e19_external_from_eleven_normalized_kernel hx11 h19

private theorem buthe_theta_lt_x_upto_1e19_external_from_eleven
    {x : ℝ}
    (hx11 : (11 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x < x := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx3 : (3 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_two_le hx2
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_two_le hx2
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_two_le hx2
  have hnorm : thetaUpTo x - x < 0 :=
    buthe_theta_lt_x_upto_1e19_external_from_eleven_normalized hx11 h19
  have hle : thetaUpTo x ≤ x := by linarith
  linarith

private theorem buthe_theta_lt_x_upto_1e19_external_from_seven
    {x : ℝ}
    (hx7 : (7 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x < x := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx3 : (3 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := one_lt_of_two_le hx2
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_two_le hx2
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_two_le hx2
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_two_le hx2
  by_cases hx8 : x < 8
  · exact thetaUpTo_lt_x_on_seven_eight hx7 hx8
  · by_cases hx11 : x < 11
    · exact thetaUpTo_lt_x_on_eight_eleven (le_of_not_gt hx8) hx11
    · exact buthe_theta_lt_x_upto_1e19_external_from_eleven (le_of_not_gt hx11) h19

private theorem buthe_theta_lt_x_upto_1e19_external_from_three
    {x : ℝ}
    (hx3 : (3 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x < x := by
  by_cases hx5 : x < 5
  · have h : thetaUpTo x = Real.log 6 := by
      by_cases hx4 : x < 4
      · have hge : (3 : ℤ) ≤ ⌊x⌋ := by
          exact Int.le_floor.2 hx3
        have hlt : ⌊x⌋ < (4 : ℤ) := by
          exact Int.floor_lt.2 hx4
        have hfloor : ⌊x⌋ = (3 : ℤ) := by
          linarith
        unfold thetaUpTo primesUpToFloor
        rw [hfloor]
        simpa [log_two_add_log_three_eq_log_six, add_assoc]
      · have hx4' : (4 : ℝ) ≤ x := le_of_not_gt hx4
        have hge : (4 : ℤ) ≤ ⌊x⌋ := by
          exact Int.le_floor.2 hx4'
        have hlt : ⌊x⌋ < (5 : ℤ) := by
          exact Int.floor_lt.2 hx5
        have hfloor : ⌊x⌋ = (4 : ℤ) := by
          linarith
        unfold thetaUpTo primesUpToFloor
        rw [hfloor]
        simpa [log_two_add_log_three_eq_log_six, add_assoc]
    rw [h]
    have hlog6 : Real.log 6 < 3 := by
      have h6pos : (0 : ℝ) < 6 := by norm_num
      rw [Real.log_lt_iff_lt_exp h6pos]
      have he : (2 : ℝ) < Real.exp (1 : ℝ) := by
        simpa using Real.two_lt_exp
      have hpow : (2 : ℝ) ^ (3 : ℕ) < (Real.exp (1 : ℝ)) ^ (3 : ℕ) := by
        exact pow_lt_pow_of_lt_left (by positivity) he 3
      have h6lt : (6 : ℝ) < (2 : ℝ) ^ (3 : ℕ) := by
        norm_num
      have hrew : Real.exp (3 : ℝ) = (Real.exp (1 : ℝ)) ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul]
      exact lt_trans h6lt (by simpa [hrew] using hpow)
    linarith
  · by_cases hx7 : x < 7
    · have h : thetaUpTo x = Real.log 30 := by
        by_cases hx6 : x < 6
        · have hx5' : (5 : ℝ) ≤ x := le_of_not_gt hx5
          have hge : (5 : ℤ) ≤ ⌊x⌋ := by
            exact Int.le_floor.2 hx5'
          have hlt : ⌊x⌋ < (6 : ℤ) := by
            exact Int.floor_lt.2 hx6
          have hfloor : ⌊x⌋ = (5 : ℤ) := by
            linarith
          unfold thetaUpTo primesUpToFloor
          rw [hfloor]
          simpa [log_two_add_log_three_add_log_five_eq_log_thirty, add_assoc]
        · have hx6' : (6 : ℝ) ≤ x := le_of_not_gt hx6
          have hge : (6 : ℤ) ≤ ⌊x⌋ := by
            exact Int.le_floor.2 hx6'
          have hlt : ⌊x⌋ < (7 : ℤ) := by
            exact Int.floor_lt.2 hx7
          have hfloor : ⌊x⌋ = (6 : ℤ) := by
            linarith
          unfold thetaUpTo primesUpToFloor
          rw [hfloor]
          simpa [log_two_add_log_three_add_log_five_eq_log_thirty, add_assoc]
      rw [h]
      have hlog30 : Real.log 30 < 5 := by
        have h30pos : (0 : ℝ) < 30 := by norm_num
        rw [Real.log_lt_iff_lt_exp h30pos]
        have he : (2 : ℝ) < Real.exp (1 : ℝ) := by
          simpa using Real.two_lt_exp
        have hpow : (2 : ℝ) ^ (5 : ℕ) < (Real.exp (1 : ℝ)) ^ (5 : ℕ) := by
          exact pow_lt_pow_of_lt_left (by positivity) he 5
        have h30lt : (30 : ℝ) < (2 : ℝ) ^ (5 : ℕ) := by
          norm_num
        have hrew : Real.exp (5 : ℝ) = (Real.exp (1 : ℝ)) ^ (5 : ℕ) := by
          rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.exp_nat_mul]
        exact lt_trans h30lt (by simpa [hrew] using hpow)
      have hx5' : (5 : ℝ) ≤ x := le_of_not_gt hx5
      linarith
    · exact buthe_theta_lt_x_upto_1e19_external_from_seven (le_of_not_gt hx7) h19

private theorem table12_k4_b20_shifted_to_normalized
    {x : ℝ} :
    x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x →
      thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 := by
  intro h
  linarith

private theorem table12_k4_b20_normalized_to_shifted
    {x : ℝ} :
    thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 →
      x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  intro h
  linarith

private theorem table12_k4_b20_rhs_nonneg
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    0 ≤ (13.475 : ℝ) * x / (Real.log x)^4 := by
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_exp20_le h20
  nlinarith [table12_constant_nonneg, hfac]

private theorem log_ge_twenty_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    (20 : ℝ) ≤ Real.log x := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have h : Real.exp 20 ≤ Real.exp (Real.log x) := by
    simpa [Real.exp_log hxpos] using h20
  exact Real.exp_le_exp.mp h

private theorem log_pow4_ge_table12_constant_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    (13.475 : ℝ) ≤ (Real.log x)^4 := by
  have hlogge : (20 : ℝ) ≤ Real.log x := log_ge_twenty_of_exp20_le h20
  have hlogpow : (20 : ℝ)^4 ≤ (Real.log x)^4 := by
    nlinarith
  have hconst : (13.475 : ℝ) ≤ (20 : ℝ)^4 := by
    norm_num
  exact le_trans hconst hlogpow

private theorem table12_k4_b20_correction_le_x_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    (13.475 : ℝ) * x / (Real.log x)^4 ≤ x := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hcoeff :
      (13.475 : ℝ) / (Real.log x)^4 ≤ 1 := by
    exact (div_le_iff hlog4pos).2 (log_pow4_ge_table12_constant_of_exp20_le h20)
  have hmul := mul_le_mul_of_nonneg_left hcoeff hxnonneg
  simpa [one_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul

private theorem table12_k4_b20_shifted_factor_nonneg_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    0 ≤ 1 - (13.475 : ℝ) / (Real.log x)^4 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hcoeff :
      (13.475 : ℝ) / (Real.log x)^4 ≤ 1 := by
    exact (div_le_iff hlog4pos).2 (log_pow4_ge_table12_constant_of_exp20_le h20)
  linarith

private theorem table12_k4_b20_shifted_factor_le_one_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    1 - (13.475 : ℝ) / (Real.log x)^4 ≤ 1 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hcoeff_nonneg : 0 ≤ (13.475 : ℝ) / (Real.log x)^4 := by
    have h : 0 ≤ (13.475 : ℝ) := table12_constant_nonneg
    positivity
  linarith

private theorem table12_k4_b20_shifted_lhs_eq_mul_factor
    {x : ℝ} :
    x - (13.475 : ℝ) * x / (Real.log x)^4 =
      x * (1 - (13.475 : ℝ) / (Real.log x)^4) := by
  ring

private theorem table12_k4_b20_shifted_lhs_le_x_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ x := by
  have hcorr : (13.475 : ℝ) * x / (Real.log x)^4 ≥ 0 :=
    table12_k4_b20_rhs_nonneg h20
  linarith

private theorem table12_k4_b20_shifted_lhs_nonneg_of_exp20_le
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    0 ≤ x - (13.475 : ℝ) * x / (Real.log x)^4 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hcorr : (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_correction_le_x_of_exp20_le h20
  linarith

private theorem table12_k4_b20_external_shifted_mul_kernel_on_full_regime
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    x * (1 - (13.475 : ℝ) / (Real.log x)^4) ≤ thetaUpTo x := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hx2 : (2 : ℝ) ≤ x := two_le_of_exp20_le h20
  have hx3 : (3 : ℝ) ≤ x := three_le_of_exp20_le h20
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogge20 : (20 : ℝ) ≤ Real.log x := log_ge_twenty_of_exp20_le h20
  have hlogpos : 0 < Real.log x := log_pos_of_exp20_le h20
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_exp20_le h20
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_exp20_le h20
  have hcorr_nonneg : 0 ≤ (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_rhs_nonneg h20
  have hcorr_le_x : (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_correction_le_x_of_exp20_le h20
  have hfactor_nonneg :
      0 ≤ 1 - (13.475 : ℝ) / (Real.log x)^4 :=
    table12_k4_b20_shifted_factor_nonneg_of_exp20_le h20
  have hfactor_le_one :
      1 - (13.475 : ℝ) / (Real.log x)^4 ≤ 1 :=
    table12_k4_b20_shifted_factor_le_one_of_exp20_le h20
  have hlhs_le_x : x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_shifted_lhs_le_x_of_exp20_le h20
  have hlhs_nonneg : 0 ≤ x - (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_shifted_lhs_nonneg_of_exp20_le h20
  sorry

private theorem table12_k4_b20_external_shifted_kernel_on_full_regime
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hx2 : (2 : ℝ) ≤ x := two_le_of_exp20_le h20
  have hx3 : (3 : ℝ) ≤ x := three_le_of_exp20_le h20
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogge20 : (20 : ℝ) ≤ Real.log x := log_ge_twenty_of_exp20_le h20
  have hlogpos : 0 < Real.log x := log_pos_of_exp20_le h20
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_exp20_le h20
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_exp20_le h20
  have hcorr_nonneg : 0 ≤ (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_rhs_nonneg h20
  have hcorr_le_x : (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_correction_le_x_of_exp20_le h20
  have hfactor_nonneg :
      0 ≤ 1 - (13.475 : ℝ) / (Real.log x)^4 :=
    table12_k4_b20_shifted_factor_nonneg_of_exp20_le h20
  have hfactor_le_one :
      1 - (13.475 : ℝ) / (Real.log x)^4 ≤ 1 :=
    table12_k4_b20_shifted_factor_le_one_of_exp20_le h20
  have hlhs_le_x : x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_shifted_lhs_le_x_of_exp20_le h20
  have hlhs_nonneg : 0 ≤ x - (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_shifted_lhs_nonneg_of_exp20_le h20
  have hmul :
      x * (1 - (13.475 : ℝ) / (Real.log x)^4) ≤ thetaUpTo x :=
    table12_k4_b20_external_shifted_mul_kernel_on_full_regime h20 h19
  rw [← table12_k4_b20_shifted_lhs_eq_mul_factor]
  exact hmul

private theorem table12_k4_b20_external_normalized_on_full_regime
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hx2 : (2 : ℝ) ≤ x := two_le_of_exp20_le h20
  have hx3 : (3 : ℝ) ≤ x := three_le_of_exp20_le h20
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogge20 : (20 : ℝ) ≤ Real.log x := log_ge_twenty_of_exp20_le h20
  have hlogpos : 0 < Real.log x := log_pos_of_exp20_le h20
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_exp20_le h20
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_exp20_le h20
  have hcorr_nonneg : 0 ≤ (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_rhs_nonneg h20
  have hcorr_le_x : (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_correction_le_x_of_exp20_le h20
  have hlhs_nonneg : 0 ≤ x - (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_shifted_lhs_nonneg_of_exp20_le h20
  have hshifted :
      x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x :=
    table12_k4_b20_external_shifted_kernel_on_full_regime h20 h19
  exact table12_k4_b20_shifted_to_normalized hshifted

private theorem table12_k4_b20_external_shifted_on_full_regime
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  have hx1 : (1 : ℝ) < x := one_lt_of_exp20_le h20
  have hx2 : (2 : ℝ) ≤ x := two_le_of_exp20_le h20
  have hx3 : (3 : ℝ) ≤ x := three_le_of_exp20_le h20
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogge20 : (20 : ℝ) ≤ Real.log x := log_ge_twenty_of_exp20_le h20
  have hlogpos : 0 < Real.log x := log_pos_of_exp20_le h20
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_exp20_le h20
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_exp20_le h20
  have hcorr_nonneg : 0 ≤ (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_rhs_nonneg h20
  have hcorr_le_x : (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_correction_le_x_of_exp20_le h20
  have hlhs_le_x : x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ x :=
    table12_k4_b20_shifted_lhs_le_x_of_exp20_le h20
  have hlhs_nonneg : 0 ≤ x - (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_shifted_lhs_nonneg_of_exp20_le h20
  have hnorm :
      thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_external_normalized_on_full_regime h20 h19
  exact table12_k4_b20_normalized_to_shifted hnorm

private theorem table12_k4_b20_source_core
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 := by
  have hshifted :
      x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x :=
    table12_k4_b20_external_shifted_on_full_regime h20 h19
  exact table12_k4_b20_shifted_to_normalized hshifted

theorem table12_k4_b20_source_raw
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 := by
  exact table12_k4_b20_source_core h20 h19

private theorem table12_k4_b20_source_shifted
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    x - (13.475 : ℝ) * x / (Real.log x)^4 ≤ thetaUpTo x := by
  exact table12_k4_b20_normalized_to_shifted (table12_k4_b20_source_raw h20 h19)

private theorem table11_k4_b20_rhs_nonneg_on_full_regime
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x) :
    0 ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_exp20_le h20
  nlinarith [table11_constant_nonneg, hfac]

private theorem table11_k4_b20_source_on_lower_subregime_from_table12_and_buthe
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  have hlower13 :
      thetaUpTo x - x ≥ - (13.475 : ℝ) * x / (Real.log x)^4 :=
    table12_k4_b20_source_core h20 h19
  have hx3 : (3 : ℝ) ≤ x := three_le_of_exp20_le h20
  have hupper_nat : thetaUpTo x < x :=
    buthe_theta_lt_x_upto_1e19_external_from_three hx3 h19
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_exp20_le h20
  have hscale :
      (13.475 : ℝ) * x / (Real.log x)^4 ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
    nlinarith [table12_constant_nonneg, table11_constant_nonneg, hfac]
  have hleft :
      -((57.184 : ℝ) * x / (Real.log x)^4) ≤ thetaUpTo x - x := by
    linarith
  have hright :
      thetaUpTo x - x ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
    have hrhs_nonneg : 0 ≤ (57.184 : ℝ) * x / (Real.log x)^4 :=
      table11_k4_b20_rhs_nonneg_on_full_regime h20
    linarith
  exact abs_le.mpr ⟨hleft, hright⟩

private theorem table11_k4_b20_external_low_subregime
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x)
    (h6000 : x < table9TailThreshold) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  rcases table11_regime_contains_current_large_range h19 h6000 with ⟨h20, h25000⟩
  have hx1 : (1 : ℝ) < x := one_lt_of_pow19_le h19
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_pow19_le h19
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_pow19_le h19
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_pow19_le h19
  have h20' : Real.exp 20 ≤ x := h20
  have h25000' : x < Real.exp 25000 := h25000
  sorry

private theorem table9_psi_source_theta_route_external
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    |thetaUpTo x - x| ≤ x / (Real.log x)^4 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_tail h6000
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_tail h6000
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_tail h6000
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_tail h6000
  have hright :
      thetaUpTo x - x ≤ x / (Real.log x)^4 := by
    sorry
  have hleft :
      -(x / (Real.log x)^4) ≤ thetaUpTo x - x := by
    sorry
  exact abs_le.mpr ⟨hleft, hright⟩

private theorem table9_psi_source_theta_route_external_left
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    -(x / (Real.log x)^4) ≤ thetaUpTo x - x := by
  exact (abs_le.mp (table9_psi_source_theta_route_external h6000)).1

private theorem table9_psi_source_theta_route_external_right
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    thetaUpTo x - x ≤ x / (Real.log x)^4 := by
  exact (abs_le.mp (table9_psi_source_theta_route_external h6000)).2

private theorem table9_psi_source_theta_route_external_as_cPsi
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    |thetaUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 := by
  simpa [cPsiTail_def] using table9_psi_source_theta_route_external h6000

private theorem table9_psi_source_core
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    |psiUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 := by
  have htheta :
      |thetaUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 :=
    table9_psi_source_theta_route_external_as_cPsi h6000
  simpa [psiUpTo_def] using htheta

private theorem table9_psi_source_raw_left
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    -(cPsiTail * x / (Real.log x)^4) ≤ psiUpTo x - x := by
  exact (abs_le.mp (table9_psi_source_core h6000)).1

private theorem table9_psi_source_raw_right
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    psiUpTo x - x ≤ cPsiTail * x / (Real.log x)^4 := by
  exact (abs_le.mp (table9_psi_source_core h6000)).2

private theorem table11_k4_b20_external_on_tail_from_table9
    {x : ℝ}
    (ht : table9TailThreshold ≤ x) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  have hpsi :
      |psiUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 :=
    table9_psi_source_core ht
  have htheta :
      |thetaUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 := by
    simpa [psiUpTo_def] using hpsi
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_tail ht
  have hscale :
      cPsiTail * x / (Real.log x)^4 ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
    nlinarith [cPsiTail_le_table11_constant, hfac]
  exact le_trans htheta hscale

private theorem table11_k4_b20_external_from_1e19_to_e25000
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x)
    (h25000 : x < Real.exp 25000) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  have hx1 : (1 : ℝ) < x := one_lt_of_pow19_le h19
  have hxpos : 0 < x := x_pos_of_one_lt hx1
  have hxnonneg : 0 ≤ x := x_nonneg_of_one_lt hx1
  have hlogpos : 0 < Real.log x := log_pos_of_pow19_le h19
  have hlogne : Real.log x ≠ 0 := log_ne_zero_of_pow19_le h19
  have hlog4pos : 0 < (Real.log x)^4 := log_pow4_pos_of_one_lt hx1
  have hfac : 0 ≤ x / (Real.log x)^4 := factor_nonneg_of_pow19_le h19
  by_cases h6000 : x < table9TailThreshold
  · exact table11_k4_b20_external_low_subregime h19 h6000
  · exact table11_k4_b20_external_on_tail_from_table9 (le_of_not_gt h6000)

theorem table11_k4_b20_source_on_full_regime
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h25000 : x < Real.exp 25000) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  by_cases h19 : x < (10 : ℝ)^19
  · exact table11_k4_b20_source_on_lower_subregime_from_table12_and_buthe h20 h19
  · exact table11_k4_b20_external_from_1e19_to_e25000 (le_of_not_gt h19) h25000

private theorem table11_k4_b20_source_on_current_large_range
    {x : ℝ}
    (h19 : (10 : ℝ)^19 ≤ x)
    (h6000 : x < table9TailThreshold) :
    |thetaUpTo x - x| ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  rcases table11_regime_contains_current_large_range h19 h6000 with ⟨h20, h25000⟩
  exact table11_k4_b20_source_on_full_regime h20 h25000

private theorem table11_k4_b20_source_on_full_regime_left
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h25000 : x < Real.exp 25000) :
    -((57.184 : ℝ) * x / (Real.log x)^4) ≤ thetaUpTo x - x := by
  exact (abs_le.mp (table11_k4_b20_source_on_full_regime h20 h25000)).1

private theorem table11_k4_b20_source_on_full_regime_right
    {x : ℝ}
    (h20 : Real.exp 20 ≤ x)
    (h25000 : x < Real.exp 25000) :
    thetaUpTo x - x ≤ (57.184 : ℝ) * x / (Real.log x)^4 := by
  exact (abs_le.mp (table11_k4_b20_source_on_full_regime h20 h25000)).2

private theorem buthe_theta_lt_x_upto_1e19_natural_core
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x < x := by
  by_cases hx3 : x < 3
  · exact thetaUpTo_lt_x_on_two_three hx2 hx3
  · exact buthe_theta_lt_x_upto_1e19_external_from_three (le_of_not_gt hx3) h19

private theorem buthe_theta_lt_x_upto_1e19_normalized
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x - x < 0 := by
  have hnat : thetaUpTo x < x :=
    buthe_theta_lt_x_upto_1e19_natural_core hx2 h19
  exact thetaUpTo_sub_x_lt_zero_of_lt hnat

theorem buthe_theta_lt_x_upto_1e19_natural
    {x : ℝ}
    (hx2 : (2 : ℝ) ≤ x)
    (h19 : x < (10 : ℝ)^19) :
    thetaUpTo x < x := by
  exact buthe_theta_lt_x_upto_1e19_natural_core hx2 h19

theorem table9_psi_source_raw
    {x : ℝ}
    (h6000 : table9TailThreshold ≤ x) :
    |psiUpTo x - x| ≤ cPsiTail * x / (Real.log x)^4 := by
  exact table9_psi_source_core h6000

end ThetaBroadbentSources
end AppendixA
end Pivot
end Lehmer