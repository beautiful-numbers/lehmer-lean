-- FILE: Lean/Lehmer/Audit/CaseB/CaseBSaturatedProgressAudit.lean
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

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Classical

def AuditCaseBSaturatedState (C : Context) : Prop :=
  SSLock C

@[simp] theorem AuditCaseBSaturatedState_def (C : Context) :
    AuditCaseBSaturatedState C = SSLock C := rfl

theorem AuditCaseBSaturatedState.locked
    {C : Context} (hC : AuditCaseBSaturatedState C) :
    SSLock C := by
  exact hC

theorem AuditCaseBSaturatedState.not_nonSaturated
    {C : Context} (hC : AuditCaseBSaturatedState C) :
    ¬ ContextNonSaturated C := by
  exact not_ContextNonSaturated_of_SSLock C hC

def AuditCaseBGatePassState (C : Context) : Prop :=
  AuditCaseBSaturatedState C ∧ supportCard C.S ≤ C.y

@[simp] theorem AuditCaseBGatePassState_def (C : Context) :
    AuditCaseBGatePassState C =
      (AuditCaseBSaturatedState C ∧ supportCard C.S ≤ C.y) := rfl

theorem AuditCaseBGatePassState.saturated
    {C : Context} (hC : AuditCaseBGatePassState C) :
    AuditCaseBSaturatedState C := by
  exact hC.1

theorem AuditCaseBGatePassState.gate
    {C : Context} (hC : AuditCaseBGatePassState C) :
    supportCard C.S ≤ C.y := by
  exact hC.2

def AuditCaseBGateFailState (C : Context) : Prop :=
  AuditCaseBSaturatedState C ∧ C.y < supportCard C.S

@[simp] theorem AuditCaseBGateFailState_def (C : Context) :
    AuditCaseBGateFailState C =
      (AuditCaseBSaturatedState C ∧ C.y < supportCard C.S) := rfl

theorem AuditCaseBGateFailState.saturated
    {C : Context} (hC : AuditCaseBGateFailState C) :
    AuditCaseBSaturatedState C := by
  exact hC.1

theorem AuditCaseBGateFailState.offGate
    {C : Context} (hC : AuditCaseBGateFailState C) :
    C.y < supportCard C.S := by
  exact hC.2

theorem AuditCaseBGatePassState.not_gateFail
    {C : Context} (hC : AuditCaseBGatePassState C) :
    ¬ AuditCaseBGateFailState C := by
  intro hF
  exact Nat.not_lt_of_ge hC.2 hF.2

theorem AuditCaseBGateFailState.not_gatePass
    {C : Context} (hC : AuditCaseBGateFailState C) :
    ¬ AuditCaseBGatePassState C := by
  intro hP
  exact Nat.not_lt_of_ge hP.2 hC.2

structure AuditCaseBGatePassData (C : Context) where
  hsaturated : AuditCaseBSaturatedState C
  hgate : supportCard C.S ≤ C.y

theorem AuditCaseBGatePassData.state
    {C : Context} (G : AuditCaseBGatePassData C) :
    AuditCaseBGatePassState C := by
  exact ⟨G.hsaturated, G.hgate⟩

structure AuditCaseBGateFailData (C : Context) where
  hsaturated : AuditCaseBSaturatedState C
  hoff : C.y < supportCard C.S

theorem AuditCaseBGateFailData.state
    {C : Context} (G : AuditCaseBGateFailData C) :
    AuditCaseBGateFailState C := by
  exact ⟨G.hsaturated, G.hoff⟩

def auditCaseBGatePassData_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    AuditCaseBGatePassData C :=
  { hsaturated := hC.1
    hgate := hC.2 }

def auditCaseBGateFailData_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    AuditCaseBGateFailData C :=
  { hsaturated := hC.1
    hoff := hC.2 }

def AuditCaseBSaturatedLocalOutcome (C : Context) : Prop :=
  (∃ _ : AuditCaseBGatePassData C, True) ∨
  (∃ _ : AuditCaseBGateFailData C, True)

@[simp] theorem AuditCaseBSaturatedLocalOutcome_def (C : Context) :
    AuditCaseBSaturatedLocalOutcome C =
      ((∃ _ : AuditCaseBGatePassData C, True) ∨
       (∃ _ : AuditCaseBGateFailData C, True)) := rfl

theorem AuditCaseBSaturatedLocalOutcome_of_gatePassState
    {C : Context} (hC : AuditCaseBGatePassState C) :
    AuditCaseBSaturatedLocalOutcome C := by
  exact Or.inl ⟨auditCaseBGatePassData_of_state C hC, trivial⟩

theorem AuditCaseBSaturatedLocalOutcome_of_gateFailState
    {C : Context} (hC : AuditCaseBGateFailState C) :
    AuditCaseBSaturatedLocalOutcome C := by
  exact Or.inr ⟨auditCaseBGateFailData_of_state C hC, trivial⟩

theorem AuditCaseBSaturatedLocalOutcome_of_saturatedState
    {C : Context} (hC : AuditCaseBSaturatedState C) :
    AuditCaseBSaturatedLocalOutcome C := by
  by_cases hgate : supportCard C.S ≤ C.y
  · exact AuditCaseBSaturatedLocalOutcome_of_gatePassState ⟨hC, hgate⟩
  · have hoff : C.y < supportCard C.S := by
      exact Nat.lt_of_not_ge hgate
    exact AuditCaseBSaturatedLocalOutcome_of_gateFailState ⟨hC, hoff⟩

theorem AuditCaseBSaturatedState.exhaustive_gateSplit
    {C : Context} (hC : AuditCaseBSaturatedState C) :
    AuditCaseBGatePassState C ∨ AuditCaseBGateFailState C := by
  by_cases hgate : supportCard C.S ≤ C.y
  · exact Or.inl ⟨hC, hgate⟩
  · exact Or.inr ⟨hC, Nat.lt_of_not_ge hgate⟩

theorem exists_gatePass_or_gateFail_of_saturatedState
    (C : Context)
    (hC : AuditCaseBSaturatedState C) :
    (∃ _ : AuditCaseBGatePassData C, True) ∨
    (∃ _ : AuditCaseBGateFailData C, True) := by
  exact AuditCaseBSaturatedLocalOutcome_of_saturatedState hC

theorem exists_gatePass_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact ⟨auditCaseBGatePassData_of_state C hC, trivial⟩

theorem exists_gateFail_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact ⟨auditCaseBGateFailData_of_state C hC, trivial⟩

theorem AuditCaseBSaturatedLocalOutcome.gatePass
    {C : Context}
    (hO : AuditCaseBSaturatedLocalOutcome C)
    (hnot : ¬ ∃ _ : AuditCaseBGateFailData C, True) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  rcases hO with hP | hF
  · exact hP
  · exact False.elim (hnot hF)

theorem AuditCaseBSaturatedLocalOutcome.gateFail
    {C : Context}
    (hO : AuditCaseBSaturatedLocalOutcome C)
    (hnot : ¬ ∃ _ : AuditCaseBGatePassData C, True) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  rcases hO with hP | hF
  · exact False.elim (hnot hP)
  · exact hF

def AuditCaseBSaturatedBoundary (C : Context) : Prop :=
  AuditCaseBGatePassState C ∨ AuditCaseBGateFailState C

@[simp] theorem AuditCaseBSaturatedBoundary_def (C : Context) :
    AuditCaseBSaturatedBoundary C =
      (AuditCaseBGatePassState C ∨ AuditCaseBGateFailState C) := rfl

theorem AuditCaseBSaturatedBoundary_of_gatePass
    {C : Context} (hC : AuditCaseBGatePassState C) :
    AuditCaseBSaturatedBoundary C := by
  exact Or.inl hC

theorem AuditCaseBSaturatedBoundary_of_gateFail
    {C : Context} (hC : AuditCaseBGateFailState C) :
    AuditCaseBSaturatedBoundary C := by
  exact Or.inr hC

theorem AuditCaseBSaturatedBoundary_of_saturated
    {C : Context} (hC : AuditCaseBSaturatedState C) :
    AuditCaseBSaturatedBoundary C := by
  exact AuditCaseBSaturatedState.exhaustive_gateSplit hC

end CaseB
end Lehmer