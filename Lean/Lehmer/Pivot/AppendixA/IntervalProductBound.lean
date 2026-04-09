-- FILE: Lean/Lehmer/Pivot/AppendixA/IntervalProductBound.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Analysis.SpecialFunctions.Exp : thm
- Mathlib.Analysis.SpecialFunctions.Log.Basic : thm
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixA.LogFactorDefs : def thm
- Lehmer.Pivot.AppendixA.IntervalLogSumBound : thm
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lehmer.Prelude
import Lehmer.Pivot.AppendixA.LogFactorDefs
import Lehmer.Pivot.AppendixA.IntervalLogSumBound

open scoped BigOperators
open Real

namespace Lehmer
namespace Pivot
namespace AppendixA

noncomputable section

/-!
# Appendix A interval product bound

This file contains the final uniform Appendix A bridge from the logarithmic
interval sum to the interval prime product bound.

Core outputs:
* `intervalLogSum y ≤ log 2` for `y ≥ Y0`;
* `intervalPrimeProd y ≤ 2` for `y ≥ Y0`.

Scope:
* no `mreq` yet;
* no `UBm` comparison yet;
* only the uniform large-range bound at the level of the full interval product.
-/

/--
Uniform Appendix A logarithmic bound on the prime-interval layer.
-/
theorem intervalLogSum_le_log2_of_ge_Y0
    (y : ℕ)
    (hy : Y0 ≤ y) :
    intervalLogSum y ≤ Real.log 2 := by
  exact intervalLogSum_le_log2 y hy

/--
Uniform Appendix A product bound on the prime-interval layer.

This is the direct product-form consequence of the logarithmic bound.
-/
theorem intervalPrimeProd_le_two_of_ge_Y0
    (y : ℕ)
    (hy : Y0 ≤ y) :
    intervalPrimeProd y ≤ 2 := by
  have hlog : intervalLogSum y ≤ Real.log 2 :=
    intervalLogSum_le_log2_of_ge_Y0 y hy
  have hexp :
      Real.exp (intervalLogSum y) ≤ Real.exp (Real.log 2) := by
    exact Real.exp_le_exp.mpr hlog
  rw [exp_intervalLogSum_eq_intervalPrimeProd] at hexp
  have htwo_pos : (0 : ℝ) < 2 := by
    norm_num
  rw [Real.exp_log htwo_pos] at hexp
  exact_mod_cast hexp

/--
Real-cast form of the interval product bound.
-/
theorem intervalPrimeProd_cast_le_two_of_ge_Y0
    (y : ℕ)
    (hy : Y0 ≤ y) :
    ((intervalPrimeProd y : ℚ) : ℝ) ≤ 2 := by
  exact_mod_cast (intervalPrimeProd_le_two_of_ge_Y0 y hy)

end

end AppendixA
end Pivot
end Lehmer