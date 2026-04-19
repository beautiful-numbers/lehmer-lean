-- FILE: Lean/Lehmer/CaseB/CaseBContradictionAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossingGlobalAudit : def thm
- Lehmer.CaseB.CaseBContradiction : thm
-/

import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossingGlobalAudit
import Lehmer.CaseB.CaseBContradiction

namespace Lehmer
namespace CaseB

open Dominance

/--
Audit-facing alias for the terminal structural datum consumed by the new
Case B contradiction layer.
-/
abbrev CaseBContradictionAuditData (B : ClosedBudgetFunctions) : Type :=
  CaseBTerminalData B

/--
Audit-facing alias for the global no-crossing certificate consumed by the new
Case B contradiction layer.
-/
abbrev NoCrossingCertificateAudit (B : ClosedBudgetFunctions) : Prop :=
  NoCrossingBeyondYstarAudit B

@[simp] theorem CaseBContradictionAuditData_def (B : ClosedBudgetFunctions) :
    CaseBContradictionAuditData B = CaseBTerminalData B := rfl

@[simp] theorem NoCrossingCertificateAudit_def (B : ClosedBudgetFunctions) :
    NoCrossingCertificateAudit B = NoCrossingBeyondYstarAudit B := rfl

/--
Audit-facing pointwise terminal contradiction for the new Case B contradiction
layer.
-/
theorem false_of_caseB_terminal_dataAudit
    {B : ClosedBudgetFunctions}
    (D : CaseBContradictionAuditData B)
    (hno : NoCrossingCertificateAudit B) :
    False := by
  exact false_of_terminalData D hno

/--
Audit-facing pointwise contradiction, same content under the main theorem name.
-/
theorem caseB_impossibleAudit
    {B : ClosedBudgetFunctions}
    (D : CaseBContradictionAuditData B)
    (hno : NoCrossingCertificateAudit B) :
    False := by
  exact false_of_caseB_terminal_dataAudit D hno

/--
Local no-crossing extracted audit-facing from the global certificate at the
terminal level carried by the contradiction datum.
-/
theorem local_noCrossingAudit_of_terminal_data
    {B : ClosedBudgetFunctions}
    (D : CaseBContradictionAuditData B)
    (hno : NoCrossingCertificateAudit B) :
    NoCrossingAt B D.y := by
  exact noCrossingAt_of_NoCrossingBeyondYstarAudit hno D.hy D.hprime

/--
Expanded audit-facing contradiction using the local terminal no-crossing
statement.
-/
theorem false_of_caseB_terminal_dataAudit_local
    {B : ClosedBudgetFunctions}
    (D : CaseBContradictionAuditData B)
    (hlocal : NoCrossingAt B D.y) :
    False := by
  exact false_of_terminalData_and_local_noCrossing D hlocal

/--
Audit-facing semantic contradiction at the terminal level.
-/
theorem false_of_largePivotAudit
    {B : ClosedBudgetFunctions}
    (D : CaseBContradictionAuditData B)
    (hno : NoCrossingCertificateAudit B) :
    False := by
  exact false_of_caseB_terminal_dataAudit D hno

/--
Audit-facing contradiction-ready inequality extracted from the global
no-crossing certificate at the terminal level.
-/
theorem M_lt_caseAMreq_of_terminal_dataAudit
    {B : ClosedBudgetFunctions}
    (D : CaseBContradictionAuditData B)
    (hno : NoCrossingCertificateAudit B) :
    M B D.y < (caseAMreq D.y : ℝ) := by
  exact M_lt_caseAMreq_of_NoCrossingBeyondYstarAudit hno D.hy D.hprime

/--
No-hidden-dependency transparency for the audit-facing contradiction datum.
-/
theorem caseBContradictionAudit_no_hidden_dependency_data
    (B : ClosedBudgetFunctions) :
    CaseBContradictionAuditData B = CaseBTerminalData B := rfl

/--
No-hidden-dependency transparency for the audit-facing no-crossing
certificate.
-/
theorem caseBContradictionAudit_no_hidden_dependency_noCrossing
    (B : ClosedBudgetFunctions) :
    NoCrossingCertificateAudit B = NoCrossingBeyondYstarAudit B := rfl

end CaseB
end Lehmer