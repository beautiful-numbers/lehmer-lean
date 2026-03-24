-- FILE: Lean/Lehmer/Pivot/CaseAContradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.Defs : def thm
- Lehmer.Pivot.SupportInterface : def thm
- Lehmer.Pivot.LowerBoundAbstract : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.Defs
import Lehmer.Pivot.SupportInterface
import Lehmer.Pivot.LowerBoundAbstract

namespace Lehmer
namespace Pivot

open Lehmer.Basic

/--
Mathematical Case A predicate.

At the pivot layer, Case A is the direct pivot contradiction:
the support size of `n` is strictly smaller than the pivot demand attached to
the canonical pivot value `pivotVal n`.
-/
def InCaseA (n : ℕ) : Prop :=
  omega n < mreq (pivotVal n)

@[simp] theorem InCaseA_def (n : ℕ) :
    InCaseA n = (omega n < mreq (pivotVal n)) := rfl

/--
Equivalent unfolded form of the Case A predicate.
-/
theorem inCaseA_iff (n : ℕ) :
    InCaseA n ↔ omega n < mreq (pivotVal n) := by
  rfl

/--
Core Case A contradiction.

A Lehmer composite cannot lie in mathematical Case A, because the canonical
pivot lower bound forces `mreq (pivotVal n) ≤ omega n`.
-/
theorem caseA_impossible {n : ℕ}
    (hL : LehmerComposite n)
    (hA : InCaseA n) :
    False := by
  have hdemand : mreq (pivotVal n) ≤ omega n :=
    pivot_lower_bound_at_pivotVal_of_LehmerComposite hL
  exact not_lt_of_ge hdemand hA

/--
Negated form of the Case A contradiction.
-/
theorem not_inCaseA_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ InCaseA n := by
  intro hA
  exact caseA_impossible hL hA

/--
Numerical non-strict consequence of the Case A contradiction:
for a Lehmer composite, the support size is at least the pivot demand.
-/
theorem mreq_le_omega_at_pivot_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    mreq (pivotVal n) ≤ omega n := by
  exact pivot_lower_bound_at_pivotVal_of_LehmerComposite hL

/--
Repackaged contradiction in raw inequality form.
-/
theorem omega_not_lt_mreq_at_pivot_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ (omega n < mreq (pivotVal n)) := by
  exact not_inCaseA_of_LehmerComposite hL

end Pivot
end Lehmer