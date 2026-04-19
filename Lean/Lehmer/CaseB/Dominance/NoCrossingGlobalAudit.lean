-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossingGlobalAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.CaseB.Dominance.NoCrossingGlobal : thm
-/

import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.NoCrossingGlobal

namespace Lehmer
namespace CaseB
namespace Dominance

abbrev NoCrossingBeyondYstarAudit (B : ClosedBudgetFunctions) : Prop :=
  NoCrossingGlobalCertificate B

@[simp] theorem NoCrossingBeyondYstarAudit_def (B : ClosedBudgetFunctions) :
    NoCrossingBeyondYstarAudit B = NoCrossingGlobalCertificate B := rfl

@[simp] theorem NoCrossingBeyondYstarAudit_iff (B : ClosedBudgetFunctions) :
    NoCrossingBeyondYstarAudit B ↔
      (∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt B y) := by
  rfl

theorem noCrossingBeyondYstarAudit_of_global
    {B : ClosedBudgetFunctions}
    (h : NoCrossingGlobalCertificate B) :
    NoCrossingBeyondYstarAudit B := by
  exact h

theorem noCrossingAt_of_NoCrossingBeyondYstarAudit
    {B : ClosedBudgetFunctions}
    (h : NoCrossingBeyondYstarAudit B)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt B y := by
  exact noCrossingAt_of_global h hy hp

theorem M_lt_caseAMreq_of_NoCrossingBeyondYstarAudit
    {B : ClosedBudgetFunctions}
    (h : NoCrossingBeyondYstarAudit B)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    M B y < (caseAMreq y : ℝ) := by
  exact noCrossing_ready_for_contradiction h hy hp

theorem noCrossing_ready_for_contradictionAudit
    {B : ClosedBudgetFunctions}
    (h : NoCrossingBeyondYstarAudit B)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt B y := by
  exact noCrossingAt_of_NoCrossingBeyondYstarAudit h hy hp

theorem noCrossing_no_hidden_dependency_audit
    (B : ClosedBudgetFunctions) :
    NoCrossingBeyondYstarAudit B = NoCrossingGlobalCertificate B := rfl

end Dominance
end CaseB
end Lehmer