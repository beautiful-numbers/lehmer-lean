-- FILE: Lean/Lehmer/Pivot/AnalyticConstants.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Data.Real.Basic : def thm
- Mathlib.Analysis.SpecialFunctions.Log.Basic : def thm
- Lehmer.Prelude : meta
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lehmer.Prelude

namespace Lehmer
namespace Pivot

noncomputable def C1 : ℝ := (1 / 1000 : ℝ)

def Y0 : ℕ := 30000

noncomputable def barrier (t : ℝ) : ℝ :=
  C1 * t^2 / Real.log t

@[simp] theorem C1_def : C1 = (1 / 1000 : ℝ) := by
  rfl

@[simp] theorem Y0_def : Y0 = 30000 := by
  rfl

@[simp] theorem barrier_def (t : ℝ) : barrier t = C1 * t^2 / Real.log t := by
  rfl

end Pivot
end Lehmer