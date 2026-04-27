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

structure AuditCaseCResidualClosureReconstruction
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  residual : Lehmer.CaseC.StateMachine.ResidualState P D
  routing :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting P D
  routing_state :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D routing = residual
  closure :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage P D
  closure_state :
    closure.state = residual

@[simp] theorem AuditCaseCResidualClosureReconstruction.residual_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D)
    (R : Lehmer.CaseC.StateMachine.ResidualClosureRouting P D)
    (hR :
      Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D R = U)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D)
    (hX : X.state = U) :
    (AuditCaseCResidualClosureReconstruction.mk U R hR X hX).residual = U := rfl

@[simp] theorem AuditCaseCResidualClosureReconstruction.routing_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D)
    (R : Lehmer.CaseC.StateMachine.ResidualClosureRouting P D)
    (hR :
      Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D R = U)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D)
    (hX : X.state = U) :
    (AuditCaseCResidualClosureReconstruction.mk U R hR X hX).routing = R := rfl

@[simp] theorem AuditCaseCResidualClosureReconstruction.routing_state_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D)
    (R : Lehmer.CaseC.StateMachine.ResidualClosureRouting P D)
    (hR :
      Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D R = U)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D)
    (hX : X.state = U) :
    (AuditCaseCResidualClosureReconstruction.mk U R hR X hX).routing_state = hR := rfl

@[simp] theorem AuditCaseCResidualClosureReconstruction.closure_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D)
    (R : Lehmer.CaseC.StateMachine.ResidualClosureRouting P D)
    (hR :
      Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D R = U)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D)
    (hX : X.state = U) :
    (AuditCaseCResidualClosureReconstruction.mk U R hR X hX).closure = X := rfl

@[simp] theorem AuditCaseCResidualClosureReconstruction.closure_state_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D)
    (R : Lehmer.CaseC.StateMachine.ResidualClosureRouting P D)
    (hR :
      Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D R = U)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D)
    (hX : X.state = U) :
    (AuditCaseCResidualClosureReconstruction.mk U R hR X hX).closure_state = hX := rfl

def auditCaseCResidualClosureReconstructionOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    AuditCaseCResidualClosureReconstruction P D :=
  { residual := U
    routing := Lehmer.CaseC.StateMachine.residualClosureRoutingOfState P D U
    routing_state := by
      exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_state P D U
    closure := Lehmer.CaseC.StateMachine.residualClosurePackageOfState P D U
    closure_state := by
      exact Lehmer.CaseC.StateMachine.residualClosurePackageOfState_state P D U }

@[simp] theorem AuditCaseCResidualClosureReconstruction.residual_eq_ofState
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureReconstructionOf P D U).residual = U := rfl

@[simp] theorem AuditCaseCResidualClosureReconstruction.routing_eq_ofState
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureReconstructionOf P D U).routing =
      Lehmer.CaseC.StateMachine.residualClosureRoutingOfState P D U := rfl

@[simp] theorem AuditCaseCResidualClosureReconstruction.closure_eq_ofState
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureReconstructionOf P D U).closure =
      Lehmer.CaseC.StateMachine.residualClosurePackageOfState P D U := rfl

@[simp] theorem AuditCaseCResidualClosureReconstruction.routing_state_eq_residual
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D X.routing = X.residual :=
  X.routing_state

theorem AuditCaseCResidualClosureReconstruction.routing_state_eq_closure_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D X.routing =
      X.closure.state := by
  rw [X.routing_state, X.closure_state]

theorem AuditCaseCResidualClosureReconstruction.closed
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    Lehmer.CaseC.StateMachine.ResidualClosed P D X.residual := by
  rw [← X.closure_state]
  exact X.closure.closed

theorem AuditCaseCResidualClosureReconstruction.closed_of_routing
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    Lehmer.CaseC.StateMachine.ResidualClosed P D
      (Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D X.routing) := by
  rw [X.routing_state]
  exact AuditCaseCResidualClosureReconstruction.closed P D X

theorem AuditCaseCResidualClosureReconstruction.routing_family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D
      (auditCaseCResidualClosureReconstructionOf P D U).routing =
      Lehmer.CaseC.StateMachine.residualFamily P D U := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_family P D U

theorem AuditCaseCResidualClosureReconstruction.routing_family_eq_residualFamily
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D X.routing =
      Lehmer.CaseC.StateMachine.residualFamily P D X.residual := by
  have hState := X.routing_state
  cases hR : X.routing with
  | dis U =>
      have hDef :
          Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D
            (Lehmer.CaseC.StateMachine.ResidualClosureRouting.dis U) =
            Lehmer.CaseC.ResidualFamily.dis := rfl
      rw [hDef]
      rw [hR] at hState
      rw [← hState]
      exact U.isDis.symm
  | rem U =>
      have hDef :
          Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D
            (Lehmer.CaseC.StateMachine.ResidualClosureRouting.rem U) =
            Lehmer.CaseC.ResidualFamily.rem := rfl
      rw [hDef]
      rw [hR] at hState
      rw [← hState]
      exact U.isRem.symm

theorem AuditCaseCResidualClosureReconstruction.branch_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    (∃ U : Lehmer.CaseC.StateMachine.DisResidualState P D, X.routing = .dis U) ∨
    (∃ U : Lehmer.CaseC.StateMachine.RemResidualState P D, X.routing = .rem U) := by
  cases hR : X.routing with
  | dis U =>
      exact Or.inl ⟨U, rfl⟩
  | rem U =>
      exact Or.inr ⟨U, rfl⟩

@[simp] theorem auditCaseCResidualClosureReconstructionOf_closed
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosed P D
      (auditCaseCResidualClosureReconstructionOf P D U).residual := by
  exact AuditCaseCResidualClosureReconstruction.closed P D
    (auditCaseCResidualClosureReconstructionOf P D U)

def auditCaseCResidualClosureOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage P D :=
  (auditCaseCResidualClosureReconstructionOf P D U).closure

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
  (auditCaseCResidualClosureReconstructionOf P D U).routing

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

def auditCaseCResidualClosureDataOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    AuditCaseCResidualClosureData P D :=
  let X := auditCaseCResidualClosureReconstructionOf P D U
  AuditCaseCResidualClosureData.mk X.residual X.closure

@[simp] theorem auditCaseCResidualClosureDataOf_residual
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureDataOf P D U).residual = U := rfl

@[simp] theorem auditCaseCResidualClosureDataOf_closure
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureDataOf P D U).closure = auditCaseCResidualClosureOf P D U := rfl

@[simp] theorem auditCaseCResidualClosureDataOf_closure_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (auditCaseCResidualClosureDataOf P D U).closure.state = U := by
  rw [auditCaseCResidualClosureDataOf_closure]
  exact auditCaseCResidualClosureOf_state P D U

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
  rw [AuditCaseCResidualClosureData.state_def]
  exact X.closure.closed

theorem auditCaseCResidualClosureDataOf_closed
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Lehmer.CaseC.StateMachine.ResidualClosed P D
      (auditCaseCResidualClosureDataOf P D U).state := by
  exact AuditCaseCResidualClosureData.closed P D
    (auditCaseCResidualClosureDataOf P D U)

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
  rw [CaseCResidualAuditRouting.state_def]
  exact R.package.closed

theorem CaseCResidualAuditRouting.branch_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    (∃ U : Lehmer.CaseC.StateMachine.DisResidualState P D, R.routing = .dis U) ∨
    (∃ U : Lehmer.CaseC.StateMachine.RemResidualState P D, R.routing = .rem U) := by
  cases hR : R.routing with
  | dis U =>
      exact Or.inl ⟨U, rfl⟩
  | rem U =>
      exact Or.inr ⟨U, rfl⟩

def caseCResidualAuditRouting_of_reconstruction
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    CaseCResidualAuditRouting P D :=
  { package := X.closure
    routing := X.routing
    hstate := by
      rw [X.routing_state, X.closure_state] }

@[simp] theorem caseCResidualAuditRouting_of_reconstruction_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    (caseCResidualAuditRouting_of_reconstruction P D X).package = X.closure := rfl

@[simp] theorem caseCResidualAuditRouting_of_reconstruction_routing
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    (caseCResidualAuditRouting_of_reconstruction P D X).routing = X.routing := rfl

@[simp] theorem caseCResidualAuditRouting_of_reconstruction_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    (caseCResidualAuditRouting_of_reconstruction P D X).state = X.residual := by
  change X.closure.state = X.residual
  exact X.closure_state

@[simp] theorem caseCResidualAuditRouting_of_reconstruction_family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    (caseCResidualAuditRouting_of_reconstruction P D X).family =
      Lehmer.CaseC.StateMachine.ResidualClosureRouting.family P D X.routing := by
  rfl

theorem caseCResidualAuditRouting_of_reconstruction_closed
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCResidualClosureReconstruction P D) :
    Lehmer.CaseC.StateMachine.ResidualClosed P D
      (caseCResidualAuditRouting_of_reconstruction P D X).state := by
  exact CaseCResidualAuditRouting.closed P D
    (caseCResidualAuditRouting_of_reconstruction P D X)

def caseCResidualAuditRouting_of_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    CaseCResidualAuditRouting P D :=
  caseCResidualAuditRouting_of_reconstruction P D
    (auditCaseCResidualClosureReconstructionOf P D U)

def caseCResidualAuditRouting_of_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    CaseCResidualAuditRouting P D :=
  caseCResidualAuditRouting_of_state P D X.state

@[simp] theorem caseCResidualAuditRouting_of_package_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    (caseCResidualAuditRouting_of_package P D X).state = X.state := by
  rfl

@[simp] theorem caseCResidualAuditRouting_of_package_routing_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state P D
      (caseCResidualAuditRouting_of_package P D X).routing = X.state := by
  exact auditCaseCResidualRoutingOf_state P D X.state

@[simp] theorem caseCResidualAuditRouting_of_package_family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D) :
    (caseCResidualAuditRouting_of_package P D X).family =
      Lehmer.CaseC.StateMachine.residualFamily P D X.state := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_family P D X.state

@[simp] theorem caseCResidualAuditRouting_of_state_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (caseCResidualAuditRouting_of_state P D U).state = U := rfl

@[simp] theorem caseCResidualAuditRouting_of_state_family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    (caseCResidualAuditRouting_of_state P D U).family =
      Lehmer.CaseC.StateMachine.residualFamily P D U := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_family P D U

def AuditCaseCResidualClosureReconstructible
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) : Prop :=
  ∀ U : Lehmer.CaseC.StateMachine.ResidualState P D,
    Nonempty
      { X : AuditCaseCResidualClosureReconstruction P D // X.residual = U }

@[simp] theorem AuditCaseCResidualClosureReconstructible_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) :
    AuditCaseCResidualClosureReconstructible P D =
      (∀ U : Lehmer.CaseC.StateMachine.ResidualState P D,
        Nonempty
          { X : AuditCaseCResidualClosureReconstruction P D // X.residual = U }) := rfl

theorem auditCaseCResidualClosureReconstruction_nonempty_of_state
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (U : Lehmer.CaseC.StateMachine.ResidualState P D) :
    Nonempty
      { X : AuditCaseCResidualClosureReconstruction P D // X.residual = U } := by
  refine ⟨⟨auditCaseCResidualClosureReconstructionOf P D U, rfl⟩⟩

theorem auditCaseCResidualClosureReconstructible
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) :
    AuditCaseCResidualClosureReconstructible P D := by
  intro U
  exact auditCaseCResidualClosureReconstruction_nonempty_of_state P D U

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
  auditCaseCResidualClosureOf
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem auditCaseCResidualClosureOfInCaseC_eq_of_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    auditCaseCResidualClosureOfInCaseC hC =
      auditCaseCResidualClosureOf
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCResidualStateOf hC) := rfl

@[simp] theorem auditCaseCResidualClosureOfInCaseC_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCResidualClosureOfInCaseC hC).state =
      auditCaseCResidualStateOf hC := by
  exact Lehmer.CaseC.StateMachine.residualClosurePackageOfState_state
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem auditCaseCResidualClosureOfInCaseC_closed
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
  auditCaseCResidualRoutingOf
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem auditCaseCResidualRoutingOfInCaseC_eq_of_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    auditCaseCResidualRoutingOfInCaseC hC =
      auditCaseCResidualRoutingOf
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCResidualStateOf hC) := rfl

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

theorem auditCaseCResidualClosureReconstructionOf_inCaseC_family_dis
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualClosureReconstructionOf
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCResidualStateOf hC)).routing =
      Lehmer.CaseC.ResidualFamily.dis := by
  exact auditCaseCResidualRoutingOfInCaseC_family_dis hC

theorem auditCaseCResidualRoutingOfInCaseC_is_dis
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ U : Lehmer.CaseC.StateMachine.DisResidualState
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC),
      auditCaseCResidualRoutingOfInCaseC hC = .dis U := by
  cases hR : auditCaseCResidualRoutingOfInCaseC hC with
  | dis U =>
      exact ⟨U, rfl⟩
  | rem U =>
      have hFam := auditCaseCResidualRoutingOfInCaseC_family_dis hC
      have hDef : Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC)
          (Lehmer.CaseC.StateMachine.ResidualClosureRouting.rem U) = Lehmer.CaseC.ResidualFamily.rem := rfl
      rw [hR] at hFam
      rw [hDef] at hFam
      contradiction

def caseCResidualAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCResidualAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  caseCResidualAuditRouting_of_state
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCResidualStateOf hC)

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_eq_of_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCResidualAuditRouting_of_inCaseC hC =
      caseCResidualAuditRouting_of_state
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCResidualStateOf hC) := rfl

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCResidualAuditRouting_of_inCaseC hC).package =
      auditCaseCResidualClosureOfInCaseC hC := rfl

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_routing
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCResidualAuditRouting_of_inCaseC hC).routing =
      auditCaseCResidualRoutingOfInCaseC hC := rfl

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_hstate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (caseCResidualAuditRouting_of_inCaseC hC).routing =
      (caseCResidualAuditRouting_of_inCaseC hC).package.state := by
  exact (caseCResidualAuditRouting_of_inCaseC hC).hstate

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_state
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCResidualAuditRouting_of_inCaseC hC).state =
      auditCaseCResidualStateOf hC := rfl

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCResidualAuditRouting_of_inCaseC hC).family =
      Lehmer.CaseC.ResidualFamily.dis := by
  show
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCResidualRoutingOfInCaseC hC) =
      Lehmer.CaseC.ResidualFamily.dis
  exact auditCaseCResidualRoutingOfInCaseC_family_dis hC

theorem caseCResidualAuditRouting_of_inCaseC_routing_family_dis
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (caseCResidualAuditRouting_of_inCaseC hC).routing =
      Lehmer.CaseC.ResidualFamily.dis := by
  exact caseCResidualAuditRouting_of_inCaseC_family hC

theorem caseCResidualAuditRouting_of_inCaseC_is_dis
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ U : Lehmer.CaseC.StateMachine.DisResidualState
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC),
      (caseCResidualAuditRouting_of_inCaseC hC).routing = .dis U := by
  cases hR : (caseCResidualAuditRouting_of_inCaseC hC).routing with
  | dis U =>
      exact ⟨U, rfl⟩
  | rem U =>
      have hFam := caseCResidualAuditRouting_of_inCaseC_routing_family_dis hC
      have hDef : Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC)
          (Lehmer.CaseC.StateMachine.ResidualClosureRouting.rem U) = Lehmer.CaseC.ResidualFamily.rem := rfl
      rw [hR] at hFam
      rw [hDef] at hFam
      contradiction

@[simp] theorem caseCResidualAuditRouting_of_inCaseC_closed
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
    ∃ _X : Lehmer.CaseC.StateMachine.ResidualClosurePackage P D, True := by
  exact ⟨R.package, trivial⟩

theorem exists_caseCResidualAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ _R : CaseCResidualAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC), True := by
  exact ⟨caseCResidualAuditRouting_of_inCaseC hC, trivial⟩

theorem caseCResidualAuditRouting_branch_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCResidualAuditRouting P D) :
    (∃ _U : Lehmer.CaseC.StateMachine.DisResidualState P D, True) ∨
    (∃ _U : Lehmer.CaseC.StateMachine.RemResidualState P D, True) := by
  rcases CaseCResidualAuditRouting.branch_sound P D R with ⟨U, _⟩ | ⟨U, _⟩
  · exact Or.inl ⟨U, trivial⟩
  · exact Or.inr ⟨U, trivial⟩

theorem caseCResidualAuditRouting_of_inCaseC_branch_sound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (∃ _U : Lehmer.CaseC.StateMachine.DisResidualState
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC), True) ∨
    (∃ _U : Lehmer.CaseC.StateMachine.RemResidualState
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

@[simp] theorem CaseCResidualAuditAvailable_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCResidualAuditAvailable hC =
      Nonempty
        (CaseCResidualAuditRouting
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC)) := rfl

theorem caseCResidualAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCResidualAuditAvailable hC := by
  exact ⟨caseCResidualAuditRouting_of_inCaseC hC⟩

end CaseC
end Audit
end Lehmer