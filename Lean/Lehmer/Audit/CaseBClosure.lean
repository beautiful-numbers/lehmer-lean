-- FILE: Lean/Lehmer/Audit/CaseBClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.CaseBClassAudit : def thm
- Lehmer.CaseB.TerminalBridgeAudit : def thm
- Lehmer.CaseB.Dominance.NoCrossingGlobalAudit : def thm
- Lehmer.CaseB.CaseBContradictionAudit : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.CaseBClassAudit
import Lehmer.CaseB.TerminalBridgeAudit
import Lehmer.CaseB.Dominance.NoCrossingGlobalAudit
import Lehmer.CaseB.CaseBContradictionAudit

namespace Lehmer
namespace Audit

open Lehmer.Basic
open Lehmer.CaseB
open Lehmer.Pivot (pivotVal)

/--
Audit-facing candidate predicate.
-/
def AuditCandidate (n : ℕ) : Prop :=
  LehmerComposite n

@[simp] theorem AuditCandidate_def (n : ℕ) :
    AuditCandidate n = LehmerComposite n := rfl

/--
Audit-facing predicate expressing the missing bridge "every audited Case B
candidate reaches the audited terminal structural form".

This is kept explicit here because the bridge is not yet exported by the lower
layers as an unconditional theorem.
-/
def CaseBWindowCompleteAudit : Prop :=
  ∀ n : ℕ, AuditCandidate n → AuditCaseBClass n → CaseBTerminalDataAudit n

@[simp] theorem CaseBWindowCompleteAudit_def :
    CaseBWindowCompleteAudit =
      (∀ n : ℕ, AuditCandidate n → AuditCaseBClass n → CaseBTerminalDataAudit n) := rfl

/--
Coverage / exactness of the audited Case B window.

Re-exported from `CaseBClassAudit`.
-/
theorem audit_windowB_exact (n : ℕ) :
    AuditCaseBClass n ↔ Ystar ≤ pivotVal n := by
  exact Lehmer.CaseB.audit_windowB_semantic_exact n

/--
Coverage soundness: every audited Case B candidate satisfies the exact semantic
large-pivot window.
-/
theorem audit_windowB_sound
    {n : ℕ}
    (h : AuditCaseBClass n) :
    Ystar ≤ pivotVal n := by
  exact Lehmer.CaseB.audit_windowB_sound h

/--
Coverage completeness at the local window level: every candidate satisfying the
exact semantic large-pivot condition is captured by the audited Case B class.
-/
theorem audit_windowB_complete_local
    {n : ℕ}
    (h : Ystar ≤ pivotVal n) :
    AuditCaseBClass n := by
  exact Lehmer.CaseB.audit_windowB_complete h

/--
Conditional pointwise emptiness of the audited Case B window.

This is the honest final audit assembly currently available:
it requires both missing bridges explicitly:
1. terminalization completeness for audited Case B candidates,
2. the global audited no-crossing certificate.
-/
theorem caseB_window_empty
    (hcomplete : CaseBWindowCompleteAudit)
    (hno : NoCrossingBeyondYstarAudit)
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hB : AuditCaseBClass n) :
    False := by
  have hD : CaseBTerminalDataAudit n := hcomplete n hCand hB
  exact caseB_impossibleAudit hCand hB hD hno

/--
Paper-facing reformulation of the conditional pointwise emptiness theorem.
-/
theorem caseB_exhaustive_closure
    (hcomplete : CaseBWindowCompleteAudit)
    (hno : NoCrossingBeyondYstarAudit)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n) :
    False := by
  have hB : AuditCaseBClass n := audit_windowB_complete_local hy
  exact caseB_window_empty hcomplete hno hL hB

/--
Conditional existential elimination for the audited Case B family.
-/
theorem no_audit_candidate_in_caseB
    (hcomplete : CaseBWindowCompleteAudit)
    (hno : NoCrossingBeyondYstarAudit) :
    ¬ ∃ n : ℕ, AuditCandidate n ∧ AuditCaseBClass n := by
  intro h
  rcases h with ⟨n, hCand, hB⟩
  exact caseB_window_empty hcomplete hno hCand hB

/--
Paper-facing existential reformulation:
under the two explicit remaining bridges, no Lehmer composite can satisfy the
large-pivot Case B window.
-/
theorem no_LehmerComposite_with_largePivot
    (hcomplete : CaseBWindowCompleteAudit)
    (hno : NoCrossingBeyondYstarAudit) :
    ¬ ∃ n : ℕ, LehmerComposite n ∧ Ystar ≤ pivotVal n := by
  intro h
  rcases h with ⟨n, hL, hy⟩
  exact caseB_exhaustive_closure hcomplete hno hL hy

end Audit
end Lehmer