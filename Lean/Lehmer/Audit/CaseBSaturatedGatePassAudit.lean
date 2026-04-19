-- FILE: Lean/Lehmer/Audit/CaseBSaturatedGatePassAudit.lean
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
Audit-facing candidate predicate for the saturated gate-pass branch.
-/
def AuditCandidate (n : ℕ) : Prop :=
  LehmerComposite n

@[simp] theorem AuditCandidate_def (n : ℕ) :
    AuditCandidate n = LehmerComposite n := rfl

/--
Audit-facing saturated gate-pass state.

At the currently exported audit interface, the locally consumable gate-pass
branch is exactly the conjunction of:
- audited entry into the Case B window;
- audited terminal structural bridge data.

This is the minimal exact state already exposed by the main audit-side Case B
pipeline for the branch that is closed internally by the Case B structural
contradiction.
-/
def AuditCaseBSaturatedGatePassState (n : ℕ) : Prop :=
  AuditCaseBClass n ∧ CaseBTerminalDataAudit n

@[simp] theorem AuditCaseBSaturatedGatePassState_def (n : ℕ) :
    AuditCaseBSaturatedGatePassState n =
      (AuditCaseBClass n ∧ CaseBTerminalDataAudit n) := rfl

@[simp] theorem AuditCaseBSaturatedGatePassState_iff (n : ℕ) :
    AuditCaseBSaturatedGatePassState n ↔
      AuditCaseBClass n ∧ CaseBTerminalDataAudit n := by
  rfl

/--
Explicit reading of the audited saturated gate-pass state in terms of the exact
Case B window plus its audited terminal structural bridge.
-/
@[simp] theorem AuditCaseBSaturatedGatePassState_explicit (n : ℕ) :
    AuditCaseBSaturatedGatePassState n ↔
      Ystar ≤ pivotVal n ∧ CaseBTerminalDataAudit n := by
  constructor
  · intro h
    rcases h with ⟨hB, hT⟩
    exact ⟨Lehmer.CaseB.audit_windowB_sound hB, hT⟩
  · intro h
    rcases h with ⟨hy, hT⟩
    exact ⟨Lehmer.CaseB.audit_windowB_complete hy, hT⟩

/--
Audit-facing terminal structural data actually consumed by the saturated
gate-pass contradiction.
-/
abbrev CaseBSaturatedGatePassTerminalDataAudit (n : ℕ) : Prop :=
  CaseBTerminalDataAudit n

@[simp] theorem CaseBSaturatedGatePassTerminalDataAudit_def (n : ℕ) :
    CaseBSaturatedGatePassTerminalDataAudit n = CaseBTerminalDataAudit n := rfl

theorem CaseBSaturatedGatePassTerminalDataAudit_expand (n : ℕ) :
    CaseBSaturatedGatePassTerminalDataAudit n ↔ CaseBTerminalDataAudit n := by
  rfl

/--
Closed audit-facing no-crossing input actually consumed by the saturated
gate-pass contradiction.
-/
abbrev CaseBSaturatedGatePassNoCrossingAudit : Prop :=
  NoCrossingBeyondYstarAudit

@[simp] theorem CaseBSaturatedGatePassNoCrossingAudit_def :
    CaseBSaturatedGatePassNoCrossingAudit = NoCrossingBeyondYstarAudit := rfl

/--
Local terminal contradiction for the saturated gate-pass branch.
-/
theorem caseB_saturated_gatePass_terminal
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hstate : AuditCaseBSaturatedGatePassState n)
    (hNoCrossing : CaseBSaturatedGatePassNoCrossingAudit) :
    False := by
  rcases hstate with ⟨hB, hterminal⟩
  exact caseB_impossibleAudit hCand hB hterminal hNoCrossing

/--
Closed reformulation of the local terminal contradiction.
-/
theorem caseB_saturated_gatePass_terminal_closed
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hstate : AuditCaseBSaturatedGatePassState n)
    (hNoCrossing : CaseBSaturatedGatePassNoCrossingAudit) :
    False := by
  exact caseB_saturated_gatePass_terminal hCand hstate hNoCrossing

/--
Explicit paper-facing local closure theorem for the saturated gate-pass branch.
-/
theorem caseB_saturated_gatePass_terminal_explicit
    {n : ℕ}
    (hCand : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hterminal : CaseBTerminalDataAudit n)
    (hNoCrossing : NoCrossingBeyondYstarAudit) :
    False := by
  have hstate : AuditCaseBSaturatedGatePassState n := by
    exact ⟨Lehmer.CaseB.audit_windowB_complete hy, hterminal⟩
  exact caseB_saturated_gatePass_terminal hCand hstate hNoCrossing

/--
Strong local audit certificate for the saturated gate-pass branch.
-/
structure CaseBSaturatedGatePassCertificate (n : ℕ) where
  hstate : AuditCaseBSaturatedGatePassState n
  hterminal : CaseBSaturatedGatePassTerminalDataAudit n
  hNoCrossing : CaseBSaturatedGatePassNoCrossingAudit
  hclosed : False

/--
Canonical constructor of the strong local saturated gate-pass certificate.
-/
def mkCaseBSaturatedGatePassCertificate
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hstate : AuditCaseBSaturatedGatePassState n)
    (hNoCrossing : CaseBSaturatedGatePassNoCrossingAudit) :
    CaseBSaturatedGatePassCertificate n := by
  rcases hstate with ⟨hB, hterminal⟩
  exact
    { hstate := ⟨hB, hterminal⟩
      hterminal := hterminal
      hNoCrossing := hNoCrossing
      hclosed := caseB_impossibleAudit hCand hB hterminal hNoCrossing }

/--
Direct local consumption theorem for the saturated gate-pass branch.
-/
theorem caseB_saturated_gatePass_consumed
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hstate : AuditCaseBSaturatedGatePassState n)
    (hNoCrossing : CaseBSaturatedGatePassNoCrossingAudit) :
    CaseBSaturatedGatePassCertificate n :=
  mkCaseBSaturatedGatePassCertificate hCand hstate hNoCrossing

/--
Local sufficiency theorem: the explicitly listed tools suffice to close the
saturated gate-pass branch.
-/
theorem caseB_saturated_gatePass_sufficiency
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hstate : AuditCaseBSaturatedGatePassState n)
    (hNoCrossing : CaseBSaturatedGatePassNoCrossingAudit) :
    False := by
  exact (caseB_saturated_gatePass_consumed hCand hstate hNoCrossing).hclosed

/--
No hidden dependency at the state level.
-/
theorem caseB_saturated_gatePass_no_hidden_dependency_state (n : ℕ) :
    AuditCaseBSaturatedGatePassState n =
      (AuditCaseBClass n ∧ CaseBTerminalDataAudit n) := rfl

/--
No hidden dependency at the terminal-data level.
-/
theorem caseB_saturated_gatePass_no_hidden_dependency_terminal (n : ℕ) :
    CaseBSaturatedGatePassTerminalDataAudit n = CaseBTerminalDataAudit n := rfl

/--
No hidden dependency at the closure level: local closure is exactly the
terminal contradiction theorem consumed with the explicit audited inputs.
-/
theorem caseB_saturated_gatePass_no_hidden_dependency_closure
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hstate : AuditCaseBSaturatedGatePassState n)
    (hNoCrossing : CaseBSaturatedGatePassNoCrossingAudit) :
    False := by
  exact caseB_saturated_gatePass_terminal hCand hstate hNoCrossing

end Audit
end Lehmer