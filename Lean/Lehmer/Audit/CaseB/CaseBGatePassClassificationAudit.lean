-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGatePassClassificationAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassTraceAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGatePassTraceAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Classical

inductive CaseBGatePassExhaustiveClassificationTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

inductive CaseBGatePassExhaustiveTraceClassification (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C) :
      CaseBGatePassExhaustiveTraceClassification C

namespace CaseBGatePassExhaustiveTraceClassification

def trace
    {C : Context} :
    CaseBGatePassExhaustiveTraceClassification C →
      CaseBGatePassExhaustiveTrace C
  | .gatePass G => CaseBGatePassExhaustiveTrace.gatePass C G

def tag
    {C : Context} :
    CaseBGatePassExhaustiveTraceClassification C →
      CaseBGatePassExhaustiveClassificationTag C
  | .gatePass G => CaseBGatePassExhaustiveClassificationTag.gatePass G

@[simp] theorem trace_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    trace (CaseBGatePassExhaustiveTraceClassification.gatePass G) =
      CaseBGatePassExhaustiveTrace.gatePass C G := rfl

@[simp] theorem tag_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    tag (CaseBGatePassExhaustiveTraceClassification.gatePass G) =
      CaseBGatePassExhaustiveClassificationTag.gatePass G := rfl

end CaseBGatePassExhaustiveTraceClassification

def caseBGatePassExhaustiveTraceClassification_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBGatePassExhaustiveTraceClassification C :=
  CaseBGatePassExhaustiveTraceClassification.gatePass G

noncomputable def caseBGatePassExhaustiveTraceClassification_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassExhaustiveTraceClassification C := by
  classical
  exact caseBGatePassExhaustiveTraceClassification_of_gatePass
    (Classical.choose (exists_gatePass_of_state C hC))

theorem CaseBGatePassExhaustiveTraceClassification.is_gatePass
    {C : Context}
    (K : CaseBGatePassExhaustiveTraceClassification C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases K with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem CaseBGatePassExhaustiveTraceClassification.trace_eq_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    (CaseBGatePassExhaustiveTraceClassification.trace
      (caseBGatePassExhaustiveTraceClassification_of_gatePass G)) =
      CaseBGatePassExhaustiveTrace.gatePass C G := rfl

theorem CaseBGatePassExhaustiveTraceClassification.terminal_eq_start
    {C : Context}
    (K : CaseBGatePassExhaustiveTraceClassification C) :
    CaseBGatePassExhaustiveTrace.terminal
      (CaseBGatePassExhaustiveTraceClassification.trace K) = C := by
  cases K with
  | gatePass G =>
      rfl

theorem CaseBGatePassExhaustiveTraceClassification.length_eq_zero
    {C : Context}
    (K : CaseBGatePassExhaustiveTraceClassification C) :
    CaseBGatePassExhaustiveTrace.length
      (CaseBGatePassExhaustiveTraceClassification.trace K) = 0 := by
  cases K with
  | gatePass G =>
      rfl

theorem CaseBGatePassExhaustiveTraceClassification.preserves_level
    {C : Context}
    (K : CaseBGatePassExhaustiveTraceClassification C) :
    (CaseBGatePassExhaustiveTrace.terminal
      (CaseBGatePassExhaustiveTraceClassification.trace K)).y = C.y := by
  exact CaseBGatePassExhaustiveTrace.preserves_level
    (CaseBGatePassExhaustiveTraceClassification.trace K)

theorem CaseBGatePassExhaustiveTraceClassification.terminal_contextDescentLength_le
    {C : Context}
    (K : CaseBGatePassExhaustiveTraceClassification C) :
    contextDescentLength
        (CaseBGatePassExhaustiveTrace.terminal
          (CaseBGatePassExhaustiveTraceClassification.trace K)) ≤
      contextDescentLength C := by
  exact CaseBGatePassExhaustiveTrace.terminal_contextDescentLength_le
    (CaseBGatePassExhaustiveTraceClassification.trace K)

theorem caseBGatePassExhaustiveTraceClassification_sound
    {C : Context}
    (K : CaseBGatePassExhaustiveTraceClassification C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases K with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem exists_caseBGatePassExhaustiveTraceClassification_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassExhaustiveTraceClassification C, True := by
  exact ⟨caseBGatePassExhaustiveTraceClassification_of_state C hC, trivial⟩

end CaseB
end Lehmer