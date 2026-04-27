-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGatePassLockAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.GenericChains : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.GenericChains
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGatePassTraceAudit
import Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGatePassLockTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

structure CaseBGatePassLockRouting (C : Context) where
  trace : CaseBGatePassExhaustiveTrace C
  classification : CaseBGatePassExhaustiveTraceClassification C
  tag : CaseBGatePassLockTag C

def caseBGatePassLockRouting_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBGatePassLockRouting C :=
  { trace := CaseBGatePassExhaustiveTrace.gatePass C G
    classification := caseBGatePassExhaustiveTraceClassification_of_gatePass G
    tag := CaseBGatePassLockTag.gatePass G }

noncomputable def caseBGatePassLockRouting_of_classification
    (C : Context)
    (K : CaseBGatePassExhaustiveTraceClassification C) :
    CaseBGatePassLockRouting C := by
  cases K.tag with
  | gatePass G =>
      exact caseBGatePassLockRouting_of_gatePass G

noncomputable def caseBGatePassLockRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassLockRouting C :=
  caseBGatePassLockRouting_of_classification C
    (caseBGatePassExhaustiveTraceClassification_of_state C hC)

theorem CaseBGatePassLockRouting.is_gatePass
    {C : Context}
    (R : CaseBGatePassLockRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R.tag with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem caseBGatePassLockRouting_sound
    {C : Context}
    (R : CaseBGatePassLockRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R.tag with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem CaseBGatePassLockRouting.trace_preserves_level
    {C : Context} (R : CaseBGatePassLockRouting C) :
    (CaseBGatePassExhaustiveTrace.terminal R.trace).y = C.y := by
  exact CaseBGatePassExhaustiveTrace.preserves_level R.trace

theorem CaseBGatePassLockRouting.trace_length_eq_zero
    {C : Context} (R : CaseBGatePassLockRouting C) :
    CaseBGatePassExhaustiveTrace.length R.trace = 0 := by
  cases R.trace
  rfl

theorem CaseBGatePassLockRouting.trace_terminal_eq_start
    {C : Context} (R : CaseBGatePassLockRouting C) :
    CaseBGatePassExhaustiveTrace.terminal R.trace = C := by
  cases R.trace
  rfl

theorem CaseBGatePassLockRouting.trace_terminal_contextDescentLength_le
    {C : Context} (R : CaseBGatePassLockRouting C) :
    contextDescentLength (CaseBGatePassExhaustiveTrace.terminal R.trace) ≤
      contextDescentLength C := by
  exact CaseBGatePassExhaustiveTrace.terminal_contextDescentLength_le R.trace

theorem CaseBGatePassLockRouting.classification_sound
    {C : Context} (R : CaseBGatePassLockRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassExhaustiveTraceClassification_sound R.classification

theorem CaseBGatePassLockRouting.trace_is_exhaustive
    {C : Context} (R : CaseBGatePassLockRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact exhaustiveTrace_is_gatePass R.trace

theorem exists_caseBGatePassLockRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassLockRouting C, True := by
  exact ⟨caseBGatePassLockRouting_of_state C hC, trivial⟩

theorem exists_gatePass_lockRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassLockRouting_sound
    (caseBGatePassLockRouting_of_state C hC)

end CaseB
end Lehmer