-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedClassificationAudit.lean
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
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedExhaustiveClassificationTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

structure CaseBNonSaturatedExhaustiveTraceClassification (C : Context) where
  trace : CaseBNonSaturatedExhaustiveTrace C
  tag : CaseBNonSaturatedExhaustiveClassificationTag C

def caseBNonSaturatedExhaustiveTraceClassification_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBNonSaturatedExhaustiveTraceClassification C :=
  { trace := CaseBNonSaturatedExhaustiveTrace.discharge C D
    tag := CaseBNonSaturatedExhaustiveClassificationTag.discharge D }

def caseBNonSaturatedExhaustiveTraceClassification_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBNonSaturatedExhaustiveTraceClassification C :=
  { trace := CaseBNonSaturatedExhaustiveTrace.entangled C E
    tag := CaseBNonSaturatedExhaustiveClassificationTag.entangled E }

noncomputable def caseBNonSaturatedExhaustiveTraceClassification_of_outcome
    (C : Context)
    (hO : AuditCaseBExhaustiveLocalOutcome C) :
    CaseBNonSaturatedExhaustiveTraceClassification C := by
  classical
  rcases hO with hD | hE
  · rcases hD with ⟨D, _⟩
    exact caseBNonSaturatedExhaustiveTraceClassification_of_discharge D
  · rcases hE with ⟨E, _⟩
    exact caseBNonSaturatedExhaustiveTraceClassification_of_entangled E

noncomputable def caseBNonSaturatedExhaustiveTraceClassification_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedExhaustiveTraceClassification C :=
  caseBNonSaturatedExhaustiveTraceClassification_of_outcome C
    (AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC)

theorem CaseBNonSaturatedExhaustiveTraceClassification.is_discharge
    {C : Context}
    (K : CaseBNonSaturatedExhaustiveTraceClassification C)
    (hnot : ¬ ∃ E : AuditCaseBEntangledStepData C, True) :
    ∃ D : AuditCaseBDischargeData C, True := by
  cases K.tag with
  | discharge D =>
      exact ⟨D, trivial⟩
  | entangled E =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem CaseBNonSaturatedExhaustiveTraceClassification.is_entangled
    {C : Context}
    (K : CaseBNonSaturatedExhaustiveTraceClassification C)
    (hnot : ¬ ∃ D : AuditCaseBDischargeData C, True) :
    ∃ E : AuditCaseBEntangledStepData C, True := by
  cases K.tag with
  | discharge D =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E =>
      exact ⟨E, trivial⟩

theorem CaseBNonSaturatedExhaustiveTraceClassification.trace_eq_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    (caseBNonSaturatedExhaustiveTraceClassification_of_discharge D).trace =
      CaseBNonSaturatedExhaustiveTrace.discharge C D := rfl

theorem CaseBNonSaturatedExhaustiveTraceClassification.trace_eq_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    (caseBNonSaturatedExhaustiveTraceClassification_of_entangled E).trace =
      CaseBNonSaturatedExhaustiveTrace.entangled C E := rfl

theorem CaseBNonSaturatedExhaustiveTraceClassification.terminal_eq_start
    {C : Context}
    (K : CaseBNonSaturatedExhaustiveTraceClassification C) :
    CaseBNonSaturatedExhaustiveTrace.terminal K.trace = C := by
  cases K.tag with
  | discharge D =>
      rfl
  | entangled E =>
      rfl

theorem CaseBNonSaturatedExhaustiveTraceClassification.length_eq_zero
    {C : Context}
    (K : CaseBNonSaturatedExhaustiveTraceClassification C) :
    CaseBNonSaturatedExhaustiveTrace.length K.trace = 0 := by
  cases K.tag with
  | discharge D =>
      rfl
  | entangled E =>
      rfl

theorem CaseBNonSaturatedExhaustiveTraceClassification.preserves_level
    {C : Context}
    (K : CaseBNonSaturatedExhaustiveTraceClassification C) :
    (CaseBNonSaturatedExhaustiveTrace.terminal K.trace).y = C.y := by
  exact CaseBNonSaturatedExhaustiveTrace.preserves_level K.trace

theorem CaseBNonSaturatedExhaustiveTraceClassification.terminal_contextDescentLength_le
    {C : Context}
    (K : CaseBNonSaturatedExhaustiveTraceClassification C) :
    contextDescentLength (CaseBNonSaturatedExhaustiveTrace.terminal K.trace) ≤
      contextDescentLength C := by
  exact CaseBNonSaturatedExhaustiveTrace.terminal_contextDescentLength_le K.trace

theorem caseBNonSaturatedExhaustiveTraceClassification_sound
    {C : Context}
    (K : CaseBNonSaturatedExhaustiveTraceClassification C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  cases K.tag with
  | discharge D =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E =>
      exact Or.inr ⟨E, trivial⟩

theorem exists_caseBNonSaturatedExhaustiveTraceClassification_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ K : CaseBNonSaturatedExhaustiveTraceClassification C, True := by
  exact ⟨caseBNonSaturatedExhaustiveTraceClassification_of_state C hC, trivial⟩

structure CaseBNonSaturatedCanonicalTraceClassification (C : Context) where
  branch : AuditCaseBNonSaturatedBranch C
  trace : CaseBNonSaturatedBackboneTrace C
  htrace : trace = caseBNonSaturatedBackboneTrace_of_branch branch
  hclassified : ContextGainCriterion C branch.backbone.p

def caseBNonSaturatedCanonicalTraceClassification_of_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    CaseBNonSaturatedCanonicalTraceClassification C :=
  { branch := B
    trace := caseBNonSaturatedBackboneTrace_of_branch B
    htrace := rfl
    hclassified := B.gain }

@[simp] theorem caseBNonSaturatedCanonicalTraceClassification_of_branch_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    (caseBNonSaturatedCanonicalTraceClassification_of_branch B).branch = B := rfl

@[simp] theorem caseBNonSaturatedCanonicalTraceClassification_of_branch_trace
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    (caseBNonSaturatedCanonicalTraceClassification_of_branch B).trace =
      caseBNonSaturatedBackboneTrace_of_branch B := rfl

structure CaseBNonSaturatedTraceClassificationProfile (C : Context) where
  branch : AuditCaseBNonSaturatedBranch C
  trace : CaseBNonSaturatedBackboneTrace C
  htrace : trace = caseBNonSaturatedBackboneTrace_of_branch branch
  hclassified : ContextGainCriterion C branch.backbone.p

def caseBNonSaturatedTraceClassificationProfile_of_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    CaseBNonSaturatedTraceClassificationProfile C :=
  { branch := B
    trace := caseBNonSaturatedBackboneTrace_of_branch B
    htrace := rfl
    hclassified := B.gain }

@[simp] theorem caseBNonSaturatedTraceClassificationProfile_of_branch_trace
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    (caseBNonSaturatedTraceClassificationProfile_of_branch B).trace =
      caseBNonSaturatedBackboneTrace_of_branch B := rfl

theorem canonical_trace_is_classified
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    ContextGainCriterion C B.backbone.p := by
  exact B.gain

theorem caseBNonSaturatedCanonicalTraceClassification_sound
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    (caseBNonSaturatedCanonicalTraceClassification_of_branch B).hclassified =
      B.gain := by
  rfl

theorem canonical_trace_classification_trace_eq
    {C : Context}
    (K : CaseBNonSaturatedCanonicalTraceClassification C) :
    K.trace = caseBNonSaturatedBackboneTrace_of_branch K.branch := by
  exact K.htrace

theorem canonical_trace_classification_gain
    {C : Context}
    (K : CaseBNonSaturatedCanonicalTraceClassification C) :
    ContextGainCriterion C K.branch.backbone.p := by
  exact K.hclassified

theorem canonical_trace_classification_terminal_eq
    {C : Context}
    (K : CaseBNonSaturatedCanonicalTraceClassification C) :
    CaseBNonSaturatedBackboneTrace.terminal K.trace =
      K.branch.backbone.C' := by
  rw [K.htrace]
  simp [caseBNonSaturatedBackboneTrace_of_branch_terminal]

theorem canonical_trace_classification_length_eq_one
    {C : Context}
    (K : CaseBNonSaturatedCanonicalTraceClassification C) :
    CaseBNonSaturatedBackboneTrace.length K.trace = 1 := by
  rw [K.htrace]
  simp [caseBNonSaturatedBackboneTrace_of_branch_length]

theorem canonical_trace_classification_preserves_level
    {C : Context}
    (K : CaseBNonSaturatedCanonicalTraceClassification C) :
    (CaseBNonSaturatedBackboneTrace.terminal K.trace).y = C.y := by
  rw [K.htrace]
  exact caseBNonSaturatedBackboneTrace_of_branch_preserves_level K.branch

theorem canonical_trace_classification_length_decrease
    {C : Context}
    (K : CaseBNonSaturatedCanonicalTraceClassification C) :
    contextDescentLength
      (CaseBNonSaturatedBackboneTrace.terminal K.trace) <
        contextDescentLength C := by
  rw [K.htrace]
  exact caseBNonSaturatedBackboneTrace_of_branch_measure_decreases K.branch

theorem caseBNonSaturatedTraceClassificationProfile_sound
    {C : Context}
    (P : CaseBNonSaturatedTraceClassificationProfile C) :
    ContextGainCriterion C P.branch.backbone.p := by
  exact P.hclassified

theorem caseBNonSaturatedTraceClassificationProfile_trace_eq
    {C : Context}
    (P : CaseBNonSaturatedTraceClassificationProfile C) :
    P.trace = caseBNonSaturatedBackboneTrace_of_branch P.branch := by
  exact P.htrace

theorem caseBNonSaturatedTraceClassificationProfile_terminal_eq
    {C : Context}
    (P : CaseBNonSaturatedTraceClassificationProfile C) :
    CaseBNonSaturatedBackboneTrace.terminal P.trace =
      P.branch.backbone.C' := by
  rw [P.htrace]
  simp [caseBNonSaturatedBackboneTrace_of_branch_terminal]

theorem caseBNonSaturatedTraceClassificationProfile_length_eq_one
    {C : Context}
    (P : CaseBNonSaturatedTraceClassificationProfile C) :
    CaseBNonSaturatedBackboneTrace.length P.trace = 1 := by
  rw [P.htrace]
  simp [caseBNonSaturatedBackboneTrace_of_branch_length]

theorem caseBNonSaturatedTraceClassificationProfile_length_decrease
    {C : Context}
    (P : CaseBNonSaturatedTraceClassificationProfile C) :
    contextDescentLength
      (CaseBNonSaturatedBackboneTrace.terminal P.trace) <
        contextDescentLength C := by
  rw [P.htrace]
  exact caseBNonSaturatedBackboneTrace_of_branch_measure_decreases P.branch

theorem exists_caseBNonSaturatedCanonicalTraceClassification_of_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    ∃ K : CaseBNonSaturatedCanonicalTraceClassification C, True := by
  exact ⟨caseBNonSaturatedCanonicalTraceClassification_of_branch B, trivial⟩

theorem exists_caseBNonSaturatedTraceClassificationProfile_of_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    ∃ P : CaseBNonSaturatedTraceClassificationProfile C, True := by
  exact ⟨caseBNonSaturatedTraceClassificationProfile_of_branch B, trivial⟩

end CaseB
end Lehmer