-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedProgressAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.LocalCompleteness : def thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.LocalCompleteness
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge

namespace Lehmer
namespace CaseB

open Lehmer.Basic

def AuditCaseBNonSaturatedState (C : Context) : Prop :=
  ContextNonSaturated C ∧ C.S.Nonempty

@[simp] theorem AuditCaseBNonSaturatedState_def (C : Context) :
    AuditCaseBNonSaturatedState C =
      (ContextNonSaturated C ∧ C.S.Nonempty) := rfl

theorem AuditCaseBNonSaturatedState.nonSaturated
    {C : Context} (hC : AuditCaseBNonSaturatedState C) :
    ContextNonSaturated C := by
  exact hC.1

theorem AuditCaseBNonSaturatedState.nonempty
    {C : Context} (hC : AuditCaseBNonSaturatedState C) :
    C.S.Nonempty := by
  exact hC.2

theorem AuditCaseBNonSaturatedState.descentEligible
    {C : Context} (hC : AuditCaseBNonSaturatedState C) :
    ContextDescentEligible C := by
  exact ⟨hC.1, hC.2⟩

def AuditCaseBLocalBoundaryData (C : Context) : Prop :=
  ContextPurelyGeneric C ∨ ∃ p : ℕ, EntangledPrime C.S p C.y

@[simp] theorem AuditCaseBLocalBoundaryData_def (C : Context) :
    AuditCaseBLocalBoundaryData C =
      (ContextPurelyGeneric C ∨ ∃ p : ℕ, EntangledPrime C.S p C.y) := rfl

theorem AuditCaseBLocalBoundaryData_of_nonSaturatedState
    {C : Context} (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBLocalBoundaryData C := by
  exact purelyGeneric_or_exists_entangledPrime_of_descentEligible C hC.descentEligible

abbrev AuditCaseBPurelyGenericBranch (C : Context) : Prop :=
  ContextPurelyGeneric C

structure AuditCaseBEntangledStepData (C : Context) where
  p : ℕ
  hent : EntangledPrime C.S p C.y

theorem AuditCaseBEntangledStepData.removable
    {C : Context} (E : AuditCaseBEntangledStepData C) :
    Removable C.S E.p := by
  exact E.hent.1

theorem AuditCaseBEntangledStepData.not_generic
    {C : Context} (E : AuditCaseBEntangledStepData C) :
    ¬ IncrementRatioGtH C.S E.p C.y := by
  exact E.hent.2

theorem AuditCaseBPurelyGenericBranch.of_boundary
    {C : Context} (hB : AuditCaseBLocalBoundaryData C)
    (h : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    AuditCaseBPurelyGenericBranch C := by
  rcases hB with hpg | hent
  · exact hpg
  · exact False.elim (h hent)

noncomputable def auditCaseBEntangledStepData_of_boundary
    (C : Context)
    (hB : AuditCaseBLocalBoundaryData C)
    (hnot : ¬ ContextPurelyGeneric C) :
    AuditCaseBEntangledStepData C := by
  classical
  rcases hB with hpg | hent
  · exact False.elim (hnot hpg)
  · rcases hent with ⟨p, hp⟩
    exact { p := p, hent := hp }

theorem auditCaseBEntangledStepData_of_boundary_spec
    (C : Context)
    (hB : AuditCaseBLocalBoundaryData C)
    (hnot : ¬ ContextPurelyGeneric C) :
    EntangledPrime C.S
      (auditCaseBEntangledStepData_of_boundary C hB hnot).p C.y := by
  exact (auditCaseBEntangledStepData_of_boundary C hB hnot).hent

def AuditCaseBExhaustiveLocalOutcome (C : Context) : Prop :=
  (∃ D : AuditCaseBDischargeData C, True) ∨
  (∃ E : AuditCaseBEntangledStepData C, True)

@[simp] theorem AuditCaseBExhaustiveLocalOutcome_def (C : Context) :
    AuditCaseBExhaustiveLocalOutcome C =
      ((∃ D : AuditCaseBDischargeData C, True) ∨
       (∃ E : AuditCaseBEntangledStepData C, True)) := rfl

theorem AuditCaseBExhaustiveLocalOutcome_of_boundary
    {C : Context} (hB : AuditCaseBLocalBoundaryData C) :
    AuditCaseBExhaustiveLocalOutcome C := by
  classical
  rcases hB with hpg | hent
  · exact Or.inl ⟨auditCaseBDischargeData_of_purelyGeneric hpg, trivial⟩
  · rcases hent with ⟨p, hp⟩
    exact Or.inr ⟨{ p := p, hent := hp }, trivial⟩

theorem AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState
    {C : Context} (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBExhaustiveLocalOutcome C := by
  exact AuditCaseBExhaustiveLocalOutcome_of_boundary
    (AuditCaseBLocalBoundaryData_of_nonSaturatedState hC)

theorem exists_discharge_or_entangled_of_nonSaturatedState
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC

theorem exists_discharge_of_purelyGeneric
    (C : Context)
    (hpg : AuditCaseBPurelyGenericBranch C) :
    ∃ D : AuditCaseBDischargeData C, True := by
  exact ⟨auditCaseBDischargeData_of_purelyGeneric hpg, trivial⟩

theorem exists_entangled_of_boundary_not_purelyGeneric
    (C : Context)
    (hB : AuditCaseBLocalBoundaryData C)
    (hnot : ¬ ContextPurelyGeneric C) :
    ∃ E : AuditCaseBEntangledStepData C, True := by
  exact ⟨auditCaseBEntangledStepData_of_boundary C hB hnot, trivial⟩

theorem AuditCaseBExhaustiveLocalOutcome.discharge
    {C : Context}
    (hO : AuditCaseBExhaustiveLocalOutcome C)
    (hnot : ¬ ∃ E : AuditCaseBEntangledStepData C, True) :
    ∃ D : AuditCaseBDischargeData C, True := by
  rcases hO with hD | hE
  · exact hD
  · exact False.elim (hnot hE)

theorem AuditCaseBExhaustiveLocalOutcome.entangled
    {C : Context}
    (hO : AuditCaseBExhaustiveLocalOutcome C)
    (hnot : ¬ ∃ D : AuditCaseBDischargeData C, True) :
    ∃ E : AuditCaseBEntangledStepData C, True := by
  rcases hO with hD | hE
  · exact False.elim (hnot hD)
  · exact hE

def AuditCaseBProgressBoundary (C : Context) : Prop :=
  AuditCaseBNonSaturatedState C ∨ SSLock C

@[simp] theorem AuditCaseBProgressBoundary_def (C : Context) :
    AuditCaseBProgressBoundary C =
      (AuditCaseBNonSaturatedState C ∨ SSLock C) := rfl

theorem AuditCaseBProgressBoundary_of_nonSaturated
    {C : Context} (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBProgressBoundary C := by
  exact Or.inl hC

theorem AuditCaseBProgressBoundary_of_lock
    {C : Context} (hlock : SSLock C) :
    AuditCaseBProgressBoundary C := by
  exact Or.inr hlock

theorem not_SSLock_of_AuditCaseBNonSaturatedState
    {C : Context} (hC : AuditCaseBNonSaturatedState C) :
    ¬ SSLock C := by
  intro hlock
  exact (not_ContextNonSaturated_of_SSLock C hlock) hC.1

def AuditCaseBGainProgressData (C : Context) : Prop :=
  ∃ p : ℕ, Removable C.S p ∧ ContextGainCriterion C p

@[simp] theorem AuditCaseBGainProgressData_def (C : Context) :
    AuditCaseBGainProgressData C =
      (∃ p : ℕ, Removable C.S p ∧ ContextGainCriterion C p) := rfl

theorem exists_pivot_of_AuditCaseBGainProgressData
    {C : Context} (hP : AuditCaseBGainProgressData C) :
    ∃ p : ℕ, Removable C.S p ∧ ContextGainCriterion C p := by
  exact hP

structure AuditCaseBBackboneStep (C : Context) where
  p : ℕ
  C' : Context
  hstep : ContextControlledRemoval C p C'
  hgain : ContextGainCriterion C p
  hdec : contextDescentLength C' < contextDescentLength C

theorem auditCaseBBackboneStep_contextDescentLength_decreases
    {C : Context} (B : AuditCaseBBackboneStep C) :
    contextDescentLength B.C' < contextDescentLength C := by
  exact B.hdec

theorem AuditCaseBBackboneStep.step
    {C : Context} (B : AuditCaseBBackboneStep C) :
    ContextControlledRemoval C B.p B.C' := by
  exact B.hstep

theorem AuditCaseBBackboneStep.gain
    {C : Context} (B : AuditCaseBBackboneStep C) :
    ContextGainCriterion C B.p := by
  exact B.hgain

theorem AuditCaseBBackboneStep.length_decrease
    {C : Context} (B : AuditCaseBBackboneStep C) :
    contextDescentLength B.C' < contextDescentLength C := by
  exact B.hdec

theorem AuditCaseBBackboneStep.preserves_level
    {C : Context} (B : AuditCaseBBackboneStep C) :
    B.C'.y = C.y := by
  exact ContextControlledRemoval_preserves_level B.hstep

theorem AuditCaseBBackboneStep.support_eq
    {C : Context} (B : AuditCaseBBackboneStep C) :
    B.C'.S = remove C.S B.p := by
  exact ContextControlledRemoval_support_eq B.hstep

noncomputable def auditCaseBBackboneStep_of_gainProgressData
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    AuditCaseBBackboneStep C := by
  classical
  rcases hP with ⟨p, hp, hgain⟩
  exact
    { p := p
      C' := nextContext C p
      hstep := contextControlledRemoval_canonical C p hp
      hgain := hgain
      hdec := contextDescentLength_strict_decrease_of_removable C p hp }

theorem contextDescentLength_decreases_of_AuditCaseBGainProgressData
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    let B := auditCaseBBackboneStep_of_gainProgressData C hP
    contextDescentLength B.C' < contextDescentLength C := by
  simp [auditCaseBBackboneStep_of_gainProgressData]

structure AuditCaseBNonSaturatedBranch (C : Context) where
  backbone : AuditCaseBBackboneStep C

theorem AuditCaseBNonSaturatedBranch.step
    {C : Context} (B : AuditCaseBNonSaturatedBranch C) :
    ContextControlledRemoval C B.backbone.p B.backbone.C' := by
  exact B.backbone.hstep

theorem AuditCaseBNonSaturatedBranch.gain
    {C : Context} (B : AuditCaseBNonSaturatedBranch C) :
    ContextGainCriterion C B.backbone.p := by
  exact B.backbone.hgain

theorem AuditCaseBNonSaturatedBranch.length_decrease
    {C : Context} (B : AuditCaseBNonSaturatedBranch C) :
    contextDescentLength B.backbone.C' < contextDescentLength C := by
  exact B.backbone.hdec

theorem AuditCaseBNonSaturatedBranch.preserves_level
    {C : Context} (B : AuditCaseBNonSaturatedBranch C) :
    B.backbone.C'.y = C.y := by
  exact ContextControlledRemoval_preserves_level B.backbone.hstep

theorem AuditCaseBNonSaturatedBranch.support_eq
    {C : Context} (B : AuditCaseBNonSaturatedBranch C) :
    B.backbone.C'.S = remove C.S B.backbone.p := by
  exact ContextControlledRemoval_support_eq B.backbone.hstep

noncomputable def auditCaseBNonSaturatedBranch_of_gainProgressData
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    AuditCaseBNonSaturatedBranch C :=
  { backbone := auditCaseBBackboneStep_of_gainProgressData C hP }

noncomputable def auditCaseBNonSaturatedBranch_of_state_and_gainProgress
    (C : Context)
    (_hC : AuditCaseBNonSaturatedState C)
    (hP : AuditCaseBGainProgressData C) :
    AuditCaseBNonSaturatedBranch C :=
  auditCaseBNonSaturatedBranch_of_gainProgressData C hP

theorem exists_AuditCaseBNonSaturatedBranch_of_gainProgressData
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    ∃ B : AuditCaseBNonSaturatedBranch C, True := by
  exact ⟨auditCaseBNonSaturatedBranch_of_gainProgressData C hP, trivial⟩

theorem exists_AuditCaseBNonSaturatedBranch_of_state_and_gainProgress
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hP : AuditCaseBGainProgressData C) :
    ∃ B : AuditCaseBNonSaturatedBranch C, True := by
  exact ⟨auditCaseBNonSaturatedBranch_of_state_and_gainProgress C hC hP, trivial⟩

theorem auditCaseBNonSaturatedBranch_contextDescentLength_decreases
    {C : Context} (B : AuditCaseBNonSaturatedBranch C) :
    contextDescentLength B.backbone.C' < contextDescentLength C := by
  exact B.backbone.hdec

theorem contextDescentLength_decreases_of_AuditCaseBNonSaturatedState_and_gainProgress
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hP : AuditCaseBGainProgressData C) :
    let B := auditCaseBNonSaturatedBranch_of_state_and_gainProgress C hC hP
    contextDescentLength B.backbone.C' < contextDescentLength C := by
  simp [auditCaseBNonSaturatedBranch_of_state_and_gainProgress,
    auditCaseBNonSaturatedBranch_of_gainProgressData,
    auditCaseBBackboneStep_of_gainProgressData]

end CaseB
end Lehmer