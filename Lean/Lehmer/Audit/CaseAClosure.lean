-- FILE: Lean/Lehmer/Audit/CaseAClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Pipeline.CaseABridge : def thm
- Lehmer.Pipeline.Main : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Pipeline.CaseABridge
import Lehmer.Pipeline.Main

namespace Lehmer
namespace Audit

open Lehmer.Basic
open Lehmer.Pipeline

/--
Audit-facing local closure statement for the mathematical Case A branch.

This isolates the current completed fact that a Lehmer composite cannot lie in
the mathematical Case A branch of the pipeline.
-/
def CaseAClosedAudit : Prop :=
  ∀ n : ℕ, LehmerComposite n → InCaseA n → False

@[simp] theorem CaseAClosedAudit_def :
    CaseAClosedAudit = (∀ n : ℕ, LehmerComposite n → InCaseA n → False) := rfl

/--
Local audit theorem: mathematical Case A is closed.
-/
theorem caseA_audit_exhaustive :
    CaseAClosedAudit := by
  intro n hL hA
  exact pipeline_closes_caseA hL hA

/--
Equivalent audit theorem using the abstract global branch relation.
-/
theorem caseA_audit_exhaustive_of_falls
    {n : ℕ} (hL : LehmerComposite n)
    (hA : FallsInGlobalBranch n GlobalBranch.caseA) :
    False := by
  exact pipeline_closes_caseA_of_falls hL hA

/--
Negated formulation: no Lehmer composite lies in the pipeline Case A branch.
-/
theorem not_inCaseA_of_LehmerComposite
    {n : ℕ} (hL : LehmerComposite n) :
    ¬ InCaseA n := by
  intro hA
  exact caseA_audit_exhaustive n hL hA

end Audit
end Lehmer