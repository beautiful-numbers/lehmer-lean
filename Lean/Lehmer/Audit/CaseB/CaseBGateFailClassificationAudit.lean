-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGateFailClassificationAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTraceAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGateFailTraceAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Classical

inductive CaseBGateFailExhaustiveClassificationTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

inductive CaseBGateFailExhaustiveTraceClassification (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C) :
      CaseBGateFailExhaustiveTraceClassification C

namespace CaseBGateFailExhaustiveTraceClassification

def trace
    {C : Context} :
    CaseBGateFailExhaustiveTraceClassification C →
      CaseBGateFailExhaustiveTrace C
  | .gateFail G => CaseBGateFailExhaustiveTrace.gateFail C G

def tag
    {C : Context} :
    CaseBGateFailExhaustiveTraceClassification C →
      CaseBGateFailExhaustiveClassificationTag C
  | .gateFail G => CaseBGateFailExhaustiveClassificationTag.gateFail G

@[simp] theorem trace_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    trace (CaseBGateFailExhaustiveTraceClassification.gateFail G) =
      CaseBGateFailExhaustiveTrace.gateFail C G := rfl

@[simp] theorem tag_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    tag (CaseBGateFailExhaustiveTraceClassification.gateFail G) =
      CaseBGateFailExhaustiveClassificationTag.gateFail G := rfl

end CaseBGateFailExhaustiveTraceClassification

def caseBGateFailExhaustiveTraceClassification_of_data
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailExhaustiveTraceClassification C :=
  CaseBGateFailExhaustiveTraceClassification.gateFail G

noncomputable def caseBGateFailExhaustiveTraceClassification_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailExhaustiveTraceClassification C :=
  caseBGateFailExhaustiveTraceClassification_of_data
    (auditCaseBGateFailData_of_state C hC)

theorem CaseBGateFailExhaustiveTraceClassification.is_gateFail
    {C : Context}
    (K : CaseBGateFailExhaustiveTraceClassification C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases K with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem CaseBGateFailExhaustiveTraceClassification.trace_eq_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    (CaseBGateFailExhaustiveTraceClassification.trace
      (caseBGateFailExhaustiveTraceClassification_of_data G)) =
      CaseBGateFailExhaustiveTrace.gateFail C G := rfl

theorem CaseBGateFailExhaustiveTraceClassification.terminal_eq_start
    {C : Context}
    (K : CaseBGateFailExhaustiveTraceClassification C) :
    CaseBGateFailExhaustiveTrace.terminal
      (CaseBGateFailExhaustiveTraceClassification.trace K) = C := by
  cases K with
  | gateFail G =>
      rfl

theorem CaseBGateFailExhaustiveTraceClassification.length_eq_zero
    {C : Context}
    (K : CaseBGateFailExhaustiveTraceClassification C) :
    CaseBGateFailExhaustiveTrace.length
      (CaseBGateFailExhaustiveTraceClassification.trace K) = 0 := by
  cases K with
  | gateFail G =>
      rfl

theorem CaseBGateFailExhaustiveTraceClassification.preserves_level
    {C : Context}
    (K : CaseBGateFailExhaustiveTraceClassification C) :
    (CaseBGateFailExhaustiveTrace.terminal
      (CaseBGateFailExhaustiveTraceClassification.trace K)).y = C.y := by
  exact CaseBGateFailExhaustiveTrace.preserves_level
    (CaseBGateFailExhaustiveTraceClassification.trace K)

theorem CaseBGateFailExhaustiveTraceClassification.terminal_contextDescentLength_le
    {C : Context}
    (K : CaseBGateFailExhaustiveTraceClassification C) :
    contextDescentLength
        (CaseBGateFailExhaustiveTrace.terminal
          (CaseBGateFailExhaustiveTraceClassification.trace K)) ≤
      contextDescentLength C := by
  exact CaseBGateFailExhaustiveTrace.terminal_contextDescentLength_le
    (CaseBGateFailExhaustiveTraceClassification.trace K)

theorem caseBGateFailExhaustiveTraceClassification_sound
    {C : Context}
    (K : CaseBGateFailExhaustiveTraceClassification C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases K with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem exists_caseBGateFailExhaustiveTraceClassification_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailExhaustiveTraceClassification C, True := by
  exact ⟨caseBGateFailExhaustiveTraceClassification_of_state C hC, trivial⟩

structure CaseBGateFailTerminalTraceClassification (C : Context) where
  trace : CaseBGateFailTerminalTrace C

def caseBGateFailTerminalTraceClassification_of_state
    {C : Context}
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailTerminalTraceClassification C :=
  { trace := caseBGateFailTerminalTrace_of_state C hC }

@[simp] theorem caseBGateFailTerminalTraceClassification_of_state_trace
    {C : Context}
    (hC : AuditCaseBGateFailState C) :
    (caseBGateFailTerminalTraceClassification_of_state hC).trace =
      caseBGateFailTerminalTrace_of_state C hC := rfl

theorem caseBGateFailTerminalTraceClassification_terminal_eq
    {C : Context}
    (K : CaseBGateFailTerminalTraceClassification C) :
    CaseBGateFailTerminalTrace.terminal K.trace = C := by
  cases K with
  | mk trace =>
      cases trace
      rfl

theorem caseBGateFailTerminalTraceClassification_length_eq_zero
    {C : Context}
    (K : CaseBGateFailTerminalTraceClassification C) :
    CaseBGateFailTerminalTrace.length K.trace = 0 := by
  cases K with
  | mk trace =>
      cases trace
      rfl

theorem caseBGateFailTerminalTraceClassification_preserves_level
    {C : Context}
    (K : CaseBGateFailTerminalTraceClassification C) :
    (CaseBGateFailTerminalTrace.terminal K.trace).y = C.y := by
  exact CaseBGateFailTerminalTrace.preserves_level K.trace

theorem exists_caseBGateFailTerminalTraceClassification_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailTerminalTraceClassification C, True := by
  exact ⟨caseBGateFailTerminalTraceClassification_of_state hC, trivial⟩

end CaseB
end Lehmer