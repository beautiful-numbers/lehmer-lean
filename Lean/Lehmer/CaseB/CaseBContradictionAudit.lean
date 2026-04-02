-- FILE: Lean/Lehmer/CaseB/CaseBContradictionAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.CaseBClassAudit : def thm
- Lehmer.CaseB.TerminalBridgeAudit : def thm
- Lehmer.CaseB.Dominance.NoCrossingGlobalAudit : def thm
- Lehmer.CaseB.CaseBContradiction : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.CaseBClassAudit
import Lehmer.CaseB.TerminalBridgeAudit
import Lehmer.CaseB.Dominance.NoCrossingGlobalAudit
import Lehmer.CaseB.CaseBContradiction

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot (pivotVal)

/--
Audit-facing alias for the terminal structural datum consumed by the Case B
contradiction layer.
-/
abbrev CaseBContradictionAuditData (n : ℕ) : Prop :=
  CaseBTerminalDataAudit n

/--
Audit-facing alias for the global no-crossing certificate consumed by the
Case B contradiction layer.
-/
abbrev NoCrossingCertificateAudit : Prop :=
  NoCrossingBeyondYstarAudit

@[simp] theorem CaseBContradictionAuditData_def (n : ℕ) :
    CaseBContradictionAuditData n = CaseBTerminalDataAudit n := rfl

@[simp] theorem NoCrossingCertificateAudit_def :
    NoCrossingCertificateAudit = NoCrossingBeyondYstarAudit := rfl

/--
Audit-facing pointwise terminal contradiction for the Case B family.

This is the direct audit reading of the main contradiction theorem:
once a Lehmer candidate lies in the audited Case B class, and once both the
audited terminal datum and the audited global no-crossing certificate are
available, the candidate is impossible.
-/
theorem false_of_caseB_terminal_dataAudit
    {n : ℕ}
    (hL : LehmerComposite n)
    (hB : AuditCaseBClass n)
    (hD : CaseBContradictionAuditData n)
    (hno : NoCrossingCertificateAudit) :
    False := by
  exact false_of_caseB_terminal_data hL hB hD hno

/--
Audit-facing pointwise contradiction, same content under the main theorem name.
-/
theorem caseB_impossibleAudit
    {n : ℕ}
    (hL : LehmerComposite n)
    (hB : AuditCaseBClass n)
    (hD : CaseBContradictionAuditData n)
    (hno : NoCrossingCertificateAudit) :
    False := by
  exact false_of_caseB_terminal_dataAudit hL hB hD hno

/--
Audit-facing negative form:
once the audited terminal datum and the audited no-crossing certificate are
available, a Lehmer candidate cannot belong to the audited Case B family.
-/
theorem not_AuditCaseBClass_of_LehmerComposite
    {n : ℕ}
    (hL : LehmerComposite n)
    (hD : CaseBContradictionAuditData n)
    (hno : NoCrossingCertificateAudit) :
    ¬ AuditCaseBClass n := by
  intro hB
  exact false_of_caseB_terminal_dataAudit hL hB hD hno

/--
Semantic-window reformulation of the audit-facing contradiction:
once the audited terminal datum and the audited no-crossing certificate are
available, a Lehmer candidate cannot satisfy the large-pivot semantic window.
-/
theorem not_largePivotAudit_of_LehmerComposite
    {n : ℕ}
    (hL : LehmerComposite n)
    (hD : CaseBContradictionAuditData n)
    (hno : NoCrossingCertificateAudit) :
    ¬ Ystar ≤ pivotVal n := by
  intro hy
  have hB : AuditCaseBClass n := audit_windowB_complete hy
  exact not_AuditCaseBClass_of_LehmerComposite hL hD hno hB

/--
Audit-facing semantic-window contradiction, stated positively on the window
hypothesis and then discharged to `False`.
-/
theorem false_of_largePivotAudit
    {n : ℕ}
    (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hD : CaseBContradictionAuditData n)
    (hno : NoCrossingCertificateAudit) :
    False := by
  have hB : AuditCaseBClass n := audit_windowB_complete hy
  exact false_of_caseB_terminal_dataAudit hL hB hD hno

/--
Audit-facing elimination from the audited Case B class to the explicit semantic
window condition.
-/
theorem false_of_caseB_terminal_dataAudit_semantic
    {n : ℕ}
    (hL : LehmerComposite n)
    (hB : AuditCaseBClass n)
    (hD : CaseBContradictionAuditData n)
    (hno : NoCrossingCertificateAudit) :
    False := by
  have hy : Ystar ≤ pivotVal n := audit_windowB_sound hB
  exact false_of_largePivotAudit hL hy hD hno

end CaseB
end Lehmer