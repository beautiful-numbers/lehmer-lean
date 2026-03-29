-- FILE: Lean/Lehmer/CaseB/Dominance/AnalyticMhatBarrier.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Data.Real.Basic : def thm
- Mathlib.Analysis.SpecialFunctions.Log.Basic : def thm
- Mathlib.Analysis.SpecialFunctions.Pow.Real : def thm
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossing : def thm
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing

namespace Lehmer
namespace CaseB

open Real

theorem zero_lt_of_TB_le {t : ℝ} (ht : TB ≤ t) : 0 < t := by
  have hY0 : (Y0 : ℝ) ≤ t := le_trans Y0_le_TB ht
  have h0 : (0 : ℝ) < Y0 := by
    norm_num [Y0_def]
  exact lt_of_lt_of_le h0 hY0

theorem one_lt_of_TB_le {t : ℝ} (ht : TB ≤ t) : 1 < t := by
  have hY0 : (Y0 : ℝ) ≤ t := le_trans Y0_le_TB ht
  have h1 : (1 : ℝ) < Y0 := by
    norm_num [Y0_def]
  exact lt_of_lt_of_le h1 hY0

theorem one_le_of_TB_le {t : ℝ} (ht : TB ≤ t) : 1 ≤ t := by
  exact le_of_lt (one_lt_of_TB_le ht)

theorem log_pos_of_TB_le {t : ℝ} (ht : TB ≤ t) : 0 < Real.log t := by
  exact Real.log_pos (one_lt_of_TB_le ht)

theorem log_nonneg_of_TB_le {t : ℝ} (ht : TB ≤ t) : 0 ≤ Real.log t := by
  exact le_of_lt (log_pos_of_TB_le ht)

/--
Appendix A / Lemma 5.6 style estimate:
for `t ≥ TB`, one has `log t ≤ t^(1/6)`.
-/
theorem log_le_rpow_one_sixth_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    Real.log t ≤ t ^ (1 / 6 : ℝ) := by
  -- prove from Lemma 5.6 style monotone comparison beyond `exp 6`
  sorry

/--
Derived estimate:
`t / log t ≤ t^(5/6)`.
-/
theorem div_log_le_rpow_five_sixths_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    t / Real.log t ≤ t ^ (5 / 6 : ℝ) := by
  -- divide by positive `log t`
  sorry

/--
Derived estimate:
`(log t)^4 ≤ t^(2/3)`.
-/
theorem log_pow_four_le_rpow_two_thirds_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    (Real.log t) ^ 4 ≤ t ^ (2 / 3 : ℝ) := by
  -- raise `log t ≤ t^(1/6)` to the fourth power
  sorry

/--
Derived lower bound:
`t^(11/6) ≤ t^2 / log t`.
-/
theorem rpow_eleven_sixths_le_div_log_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    t ^ (11 / 6 : ℝ) ≤ t^2 / Real.log t := by
  -- combine `log t ≤ t^(1/6)` with positivity of `log t`
  sorry

/--
Compression of the paper majorant:
`Mhat t ≤ 12 * t^(5/6)`.
-/
theorem mhat_le_twelve_mul_rpow_five_sixths_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    Mhat t ≤ 12 * t ^ (5 / 6 : ℝ) := by
  -- combine the upper bounds on `t/log t` and `(log t)^4`
  sorry

/--
Coarse lower bound on the analytic barrier:
`10 * t^(5/6) ≤ analyticBarrier t`.
-/
theorem ten_mul_rpow_five_sixths_le_barrier_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    10 * t ^ (5 / 6 : ℝ) ≤ analyticBarrier t := by
  -- use `C1 = 10^-3`, `t ≥ 10 / C1`, and the lower bound on `t^2 / log t`
  sorry

/--
Strict endpoint gap from Appendix A.

This is the final strict inequality upgrading the coarse comparison to the
strict dominance needed in the Case B no-crossing pipeline.
-/
theorem appendixA_endpoint_strict_gap_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    12 * t ^ (5 / 6 : ℝ) < analyticBarrier t := by
  -- exact-arithmetic endpoint certificate from Appendix A
  sorry

/--
Appendix A analytic dominance theorem:
`Mhat t < analyticBarrier t` for all `t ≥ TB`.
-/
theorem appendixA_mhat_lt_barrier_of_TB_le
    {t : ℝ} (ht : TB ≤ t) :
    Mhat t < analyticBarrier t := by
  have h1 : Mhat t ≤ 12 * t ^ (5 / 6 : ℝ) :=
    mhat_le_twelve_mul_rpow_five_sixths_of_TB_le ht
  have h2 : 12 * t ^ (5 / 6 : ℝ) < analyticBarrier t :=
    appendixA_endpoint_strict_gap_of_TB_le ht
  exact lt_of_le_of_lt h1 h2

/--
Public wrapper consumed by the Case B no-crossing layer.
-/
theorem mhat_lt_barrier
    {t : ℝ} (ht : TB ≤ t) :
    Mhat t < analyticBarrier t := by
  exact appendixA_mhat_lt_barrier_of_TB_le ht

theorem mhat_lt_barrier_forall :
    ∀ t : ℝ, TB ≤ t → Mhat t < analyticBarrier t := by
  intro t ht
  exact mhat_lt_barrier ht

end CaseB
end Lehmer