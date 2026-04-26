-- FILE: Lean/Lehmer/Audit/CaseC/ResidualClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.StateMachine.ResidualClosure : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Audit.CaseC.Params : def thm
- Lehmer.Audit.CaseC.ClosureData : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.StateMachine.ResidualClosure
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Audit.CaseC.Params
import Lehmer.Audit.CaseC.ClosureData

namespace Lehmer
namespace Audit
namespace CaseC

structure AuditCaseCResidualClosureData
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  residual : Lehmer.CaseC.StateMachine.ResidualState P D
  closure : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D

@[simp] theorem AuditCaseCResidualClosureData.residual_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    (AuditCaseCResidualClosureData.mk U X).residual = U := rfl

@[simp] theorem AuditCaseCResidualClosureData.closure_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    (AuditCaseCResidualClosureData.mk U X).closure = X := rfl

def auditCaseCResidualClosureOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage P D :=
  Lehmer.CaseC.StateMachine.residualClosurePackageOfState P D U

def auditCaseCResidualClosureDataOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    AuditCaseCResidualClosureData P D :=
  AuditCaseCResidualClosureData.mk U (auditCaseCResidualClosureOf P D U)

@[simp] theorem auditCaseCResidualClosureDataOf_residual
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureDataOf P D U).residual = U := rfl

@[simp] theorem auditCaseCResidualClosureDataOf_closure
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureDataOf P D U).closure = auditCaseCResidualClosureOf P D U := rfl

def AuditCaseCResidualClosureData.state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureData P D) :
    Lehmer.CaseC.StateMachine.ResidualState P D :=
  X.closure.state

@[simp] theorem AuditCaseCResidualClosureData.state_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureData P D) :
    X.state = X.closure.state := rfl

theorem AuditCaseCResidualClosureData.closed
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureData P D) :
    Lehmer.CaseC.StateMachine.ResidualClosed P D X.state := by
  simpa [AuditCaseCResidualClosureData.state_def] using X.closure.closed

@[simp] theorem auditCaseCResidualClosureOf_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureOf P D U).state = U := by
  exact Lehmer.CaseC.StateMachine.residualClosurePackageOfState_state P D U

@[simp] theorem auditCaseCResidualClosureOf_closed
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureOf P D U).closed =
      Lehmer.CaseC.StateMachine.residual_closed P D U := by
  exact Lehmer.CaseC.StateMachine.residualClosurePackageOfState_closed P D U

def auditCaseCResidualRoutingOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting P D :=
  Lehmer.CaseC.StateMachine.residualClosureRoutingOfState P D U

@[simp] theorem auditCaseCResidualRoutingOf_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D
      (auditCaseCResidualRoutingOf P D U) = U := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_state P D U

@[simp] theorem auditCaseCResidualRoutingOf_family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D
      (auditCaseCResidualRoutingOf P D U) =
        Lehmer.CaseC.StateMachine.residualFamily P D U := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_family P D U

def auditCaseCResidualMachineStateOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.State (auditCaseCParamsOf hC) :=
  Lehmer.CaseC.State.mk (∅ : Lehmer.CaseC.Support)

@[simp] theorem auditCaseCResidualMachineStateOf_support
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCResidualMachineStateOf hC).support = ∅ := rfl

theorem auditCaseCResidualMachineStateOf_inTruncatedDomain
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateInTruncatedDomain
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualMachineStateOf hC) := by
  constructor
  · intro p hp
    simp at hp
  · simp [Lehmer.CaseC.SupportWithinOmega, Lehmer.CaseC.supportCard]

def auditCaseCResidualDomainStateOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.DomainState
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  ⟨auditCaseCResidualMachineStateOf hC,
    auditCaseCResidualMachineStateOf_inTruncatedDomain hC⟩

@[simp] theorem auditCaseCResidualDomainStateOf_val
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCResidualDomainStateOf hC).val =
      auditCaseCResidualMachineStateOf hC := rfl

def auditCaseCResidualStateOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualState
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.StateMachine.ResidualState.mk
    (auditCaseCResidualDomainStateOf hC)
    Lehmer.CaseC.ResidualFamily.dis

@[simp] theorem auditCaseCResidualStateOf_val
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCResidualStateOf hC).val =
      auditCaseCResidualDomainStateOf hC := rfl

@[simp] theorem auditCaseCResidualStateOf_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.residualFamily
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualStateOf hC) =
        Lehmer.CaseC.ResidualFamily.dis := rfl

def auditCaseCResidualClosureOfInCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.StateMachine.residualClosurePackageOfState
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem auditCaseCResidualClosureOfInCaseC_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCResidualClosureOfInCaseC hC).state =
      auditCaseCResidualStateOf hC := by
  exact Lehmer.CaseC.StateMachine.residualClosurePackageOfState_state
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

theorem auditCaseCResidualClosureOfInCaseC_closed
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualClosureOfInCaseC hC).state := by
  exact (auditCaseCResidualClosureOfInCaseC hC).closed

def auditCaseCResidualRoutingOfInCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.StateMachine.residualClosureRoutingOfState
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem auditCaseCResidualRoutingOfInCaseC_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualRoutingOfInCaseC hC) =
        auditCaseCResidualStateOf hC := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_state
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem auditCaseCResidualRoutingOfInCaseC_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualRoutingOfInCaseC hC) =
        Lehmer.CaseC.StateMachine.residualFamily
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC)
          (auditCaseCResidualStateOf hC) := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_family
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem auditCaseCResidualRoutingOfInCaseC_family_dis
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualRoutingOfInCaseC hC) =
        Lehmer.CaseC.ResidualFamily.dis := by
  rw [auditCaseCResidualRoutingOfInCaseC_family]
  exact auditCaseCResidualStateOf_family hC

structure CaseCResidualAuditRouting
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  package :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage P D
  routing :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting P D
  hstate :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D routing =
      package.state

def CaseCResidualAuditRouting.state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    Lehmer.CaseC.StateMachine.ResidualState P D :=
  R.package.state

@[simp] theorem CaseCResidualAuditRouting.state_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    R.state = R.package.state := rfl

def CaseCResidualAuditRouting.family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    Lehmer.CaseC.ResidualFamily :=
  Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D R.routing

@[simp] theorem CaseCResidualAuditRouting.family_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    R.family =
      Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D R.routing := rfl

theorem CaseCResidualAuditRouting.closed
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    Lehmer.CaseC.StateMachine.ResidualClosed P D R.state := by
  simpa [CaseCResidualAuditRouting.state_def] using R.package.closed

def caseCResidualAuditRouting_of_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    CaseCResidualAuditRouting P D :=
  {
    package := X
    routing :=
      Lehmer.CaseC.StateMachine.residualClosureRoutingOfState P D X.state
    hstate := by
      exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_state P D X.state
  }

@[simp] theorem caseCResidualAuditRouting_of_package_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    (caseCResidualAuditRouting_of_package P D X).package = X := rfl

@[simp] theorem caseCResidualAuditRouting_of_package_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    (caseCResidualAuditRouting_of_package P D X).state = X.state := rfl

def caseCResidualAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCResidualAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  caseCResidualAuditRouting_of_package
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualClosureOfInCaseC hC)

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCResidualAuditRouting_of_inCaseC hC).package =
      auditCaseCResidualClosureOfInCaseC hC := rfl

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCResidualAuditRouting_of_inCaseC hC).state =
      auditCaseCResidualStateOf hC := by
  rfl

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCResidualAuditRouting_of_inCaseC hC).family =
      Lehmer.CaseC.ResidualFamily.dis := by
  simp [CaseCResidualAuditRouting.family_def, caseCResidualAuditRouting_of_inCaseC,
    caseCResidualAuditRouting_of_package, auditCaseCResidualClosureOfInCaseC]

theorem caseCResidualAuditRouting_of_inCaseC_closed
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (caseCResidualAuditRouting_of_inCaseC hC).state := by
  exact CaseCResidualAuditRouting.closed
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCResidualAuditRouting_of_inCaseC hC)

theorem caseCResidualAuditRouting_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    ∃ X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D, True := by
  exact ⟨R.package, trivial⟩

theorem exists_caseCResidualAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ R : CaseCResidualAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC), True := by
  exact ⟨caseCResidualAuditRouting_of_inCaseC hC, trivial⟩

theorem caseCResidualAuditRouting_branch_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    (∃ U : Lehmer.CaseC.StateMachine.DisResidualState P D, True) ∨
    (∃ U : Lehmer.CaseC.StateMachine.RemResidualState P D, True) := by
  cases R.routing with
  | dis U =>
      exact Or.inl ⟨U, trivial⟩
  | rem U =>
      exact Or.inr ⟨U, trivial⟩

theorem caseCResidualAuditRouting_of_inCaseC_branch_sound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (∃ U : Lehmer.CaseC.StateMachine.DisResidualState
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC), True) ∨
    (∃ U : Lehmer.CaseC.StateMachine.RemResidualState
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC), True) := by
  exact caseCResidualAuditRouting_branch_sound
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCResidualAuditRouting_of_inCaseC hC)

def CaseCResidualAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty
    (CaseCResidualAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

theorem caseCResidualAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCResidualAuditAvailable hC := by
  exact ⟨caseCResidualAuditRouting_of_inCaseC hC⟩

end CaseC
end Audit
end Lehmer