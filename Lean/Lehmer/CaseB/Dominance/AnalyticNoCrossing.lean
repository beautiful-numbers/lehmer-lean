-- FILE: Lean/Lehmer/CaseB/Dominance/AnalyticMhatBarrier.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Data.Real.Basic : def thm
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossing : def thm
-/

import Mathlib.Data.Real.Basic
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
Continuous analytic comparison beyond `TB`.

This is the substantive large-`t` inequality needed by the Case B no-crossing
pipeline:
`Mhat t < analyticBarrier t`.
-/
theorem mhat_lt_barrier
    {t : ℝ} (ht : TB ≤ t) :
    Mhat t < analyticBarrier t := by
  admit

end CaseB
end Lehmer