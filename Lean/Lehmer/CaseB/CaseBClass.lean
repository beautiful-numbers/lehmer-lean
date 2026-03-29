-- FILE: Lean/Lehmer/CaseB/CaseBClass.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Dominance.NoCrossing : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Dominance.NoCrossing

namespace Lehmer
namespace CaseB

open Lehmer.Pivot (pivotVal)

/-- Mathematical Case B class. -/
def InCaseB (n : ℕ) : Prop :=
  Ystar ≤ pivotVal n

@[simp] theorem InCaseB_def (n : ℕ) :
    InCaseB n = (Ystar ≤ pivotVal n) := rfl

/--
Audit-facing window for Case B.

At the current stage, this window is definitionally identical to the
mathematical Case B class.
-/
def WindowB (n : ℕ) : Prop :=
  InCaseB n

@[simp] theorem WindowB_def (n : ℕ) :
    WindowB n = InCaseB n := rfl

end CaseB
end Lehmer