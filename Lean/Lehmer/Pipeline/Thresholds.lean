-- FILE: Lean/Lehmer/Pipeline/Thresholds.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
-/

import Lehmer.Prelude

namespace Lehmer
namespace Pipeline

/--
Concrete thresholds for the range-based audit taxonomy.

These are pipeline/audit thresholds only.  They are fixed concrete values so the
pipeline layer carries no axioms of its own.
-/
def YA : ℕ := 3
def YC : ℕ := 4
def YB : ℕ := 5

@[simp] theorem YA_def : YA = 3 := rfl
@[simp] theorem YC_def : YC = 4 := rfl
@[simp] theorem YB_def : YB = 5 := rfl

@[simp] theorem three_le_YA : 3 ≤ YA := by
  simp [YA]

@[simp] theorem YA_le_YC : YA ≤ YC := by
  simp [YA, YC]

@[simp] theorem YC_le_YB : YC ≤ YB := by
  simp [YC, YB]

end Pipeline
end Lehmer