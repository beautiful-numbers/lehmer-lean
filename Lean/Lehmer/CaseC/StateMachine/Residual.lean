-- FILE: Lean/Lehmer/CaseC/StateMachine/Residual.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.StateMachine.Actions : def thm
- Lehmer.CaseC.StateMachine.State : def thm
- Lehmer.CaseC.StateMachine.Domain : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.StateMachine.Actions
import Lehmer.CaseC.StateMachine.State
import Lehmer.CaseC.StateMachine.Domain

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

structure ResidualState (P : Params) (D : ClosureData P) where
  val : DomainState P D
  family : ResidualFamily

@[simp] theorem ResidualState.val_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) (f : ResidualFamily) :
    (ResidualState.mk U f).val = U := rfl

@[simp] theorem ResidualState.family_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) (f : ResidualFamily) :
    (ResidualState.mk U f).family = f := rfl

def residualVal (P : Params) (D : ClosureData P) (U : ResidualState P D) : DomainState P D :=
  U.val

@[simp] theorem residualVal_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualVal P D U = U.val := rfl

def residualFamily (P : Params) (D : ClosureData P) (U : ResidualState P D) : ResidualFamily :=
  U.family

@[simp] theorem residualFamily_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualFamily P D U = U.family := rfl

def residualState (P : Params) (D : ClosureData P) (U : ResidualState P D) : MachineState P :=
  U.val.val

@[simp] theorem residualState_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualState P D U = U.val.val := rfl

def residualSupport (P : Params) (D : ClosureData P) (U : ResidualState P D) : Support :=
  stateSupport P (residualState P D U)

@[simp] theorem residualSupport_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualSupport P D U = stateSupport P (residualState P D U) := rfl

def residualCard (P : Params) (D : ClosureData P) (U : ResidualState P D) : ℕ :=
  stateCard P (residualState P D U)

@[simp] theorem residualCard_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualCard P D U = stateCard P (residualState P D U) := rfl

def IsDisResidual (P : Params) (D : ClosureData P) (U : ResidualState P D) : Prop :=
  residualFamily P D U = ResidualFamily.dis

def IsRemResidual (P : Params) (D : ClosureData P) (U : ResidualState P D) : Prop :=
  residualFamily P D U = ResidualFamily.rem

@[simp] theorem IsDisResidual_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsDisResidual P D U = (residualFamily P D U = ResidualFamily.dis) := rfl

@[simp] theorem IsRemResidual_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsRemResidual P D U = (residualFamily P D U = ResidualFamily.rem) := rfl

@[simp] theorem residualSupport_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) (f : ResidualFamily) :
    residualSupport P D (ResidualState.mk U f) = stateSupport P U.val := rfl

@[simp] theorem residualCard_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) (f : ResidualFamily) :
    residualCard P D (ResidualState.mk U f) = stateCard P U.val := rfl

@[simp] theorem IsDisResidual_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) (f : ResidualFamily) :
    IsDisResidual P D (ResidualState.mk U f) = (f = ResidualFamily.dis) := rfl

@[simp] theorem IsRemResidual_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) (f : ResidualFamily) :
    IsRemResidual P D (ResidualState.mk U f) = (f = ResidualFamily.rem) := rfl

theorem residualState_family_exhaustive (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsDisResidual P D U ∨ IsRemResidual P D U := by
  cases U with
  | mk val family =>
      cases family with
      | dis =>
          left
          rfl
      | rem =>
          right
          rfl

theorem IsDisResidual.not_rem (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsDisResidual P D U → ¬ IsRemResidual P D U := by
  intro hDis hRem
  have h : ResidualFamily.dis = ResidualFamily.rem := by
    calc
      ResidualFamily.dis = residualFamily P D U := hDis.symm
      _ = ResidualFamily.rem := hRem
  exact ResidualFamily.dis_ne_rem h

theorem IsRemResidual.not_dis (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsRemResidual P D U → ¬ IsDisResidual P D U := by
  intro hRem hDis
  exact (IsDisResidual.not_rem P D U hDis) hRem

theorem residualFamily_eq_of_IsDisResidual (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsDisResidual P D U → residualFamily P D U = ResidualFamily.dis := by
  intro h
  exact h

theorem residualFamily_eq_of_IsRemResidual (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsRemResidual P D U → residualFamily P D U = ResidualFamily.rem := by
  intro h
  exact h

theorem residual_underlying_inDomain (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    InDomain P D (residualState P D U) := by
  exact U.val.property

theorem residual_support_below (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    SupportBelow D.N (residualSupport P D U) := by
  exact domainState_support_below P D U.val

theorem residual_support_within_omega (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    SupportWithinOmega D.omegaHat (residualSupport P D U) := by
  exact domainState_support_within_omega P D U.val

inductive ResidualRouting (P : Params) (D : ClosureData P) where
  | dis (U : DomainState P D)
  | rem (U : DomainState P D)

def residualRoutingOfState (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    ResidualRouting P D :=
  match U.family with
  | ResidualFamily.dis => ResidualRouting.dis U.val
  | ResidualFamily.rem => ResidualRouting.rem U.val

def ResidualRouting.state (P : Params) (D : ClosureData P) :
    ResidualRouting P D → DomainState P D
  | .dis U => U
  | .rem U => U

def ResidualRouting.family (P : Params) (D : ClosureData P) :
    ResidualRouting P D → ResidualFamily
  | .dis _ => ResidualFamily.dis
  | .rem _ => ResidualFamily.rem

@[simp] theorem ResidualRouting.state_dis (P : Params) (D : ClosureData P) (U : DomainState P D) :
    ResidualRouting.state P D (.dis U) = U := rfl

@[simp] theorem ResidualRouting.state_rem (P : Params) (D : ClosureData P) (U : DomainState P D) :
    ResidualRouting.state P D (.rem U) = U := rfl

@[simp] theorem ResidualRouting.family_dis (P : Params) (D : ClosureData P) (U : DomainState P D) :
    ResidualRouting.family P D (.dis U) = ResidualFamily.dis := rfl

@[simp] theorem ResidualRouting.family_rem (P : Params) (D : ClosureData P) (U : DomainState P D) :
    ResidualRouting.family P D (.rem U) = ResidualFamily.rem := rfl

@[simp] theorem residualRoutingOfState_dis (P : Params) (D : ClosureData P)
    (U : DomainState P D) :
    residualRoutingOfState P D (ResidualState.mk U ResidualFamily.dis) =
      ResidualRouting.dis U := rfl

@[simp] theorem residualRoutingOfState_rem (P : Params) (D : ClosureData P)
    (U : DomainState P D) :
    residualRoutingOfState P D (ResidualState.mk U ResidualFamily.rem) =
      ResidualRouting.rem U := rfl

theorem ResidualRouting.sound (P : Params) (D : ClosureData P) (R : ResidualRouting P D) :
    InDomain P D (ResidualRouting.state P D R).val := by
  exact (ResidualRouting.state P D R).property

theorem ResidualRouting.is_dis (P : Params) (D : ClosureData P) (U : DomainState P D) :
    ResidualRouting.family P D (.dis U) = ResidualFamily.dis := rfl

theorem ResidualRouting.is_rem (P : Params) (D : ClosureData P) (U : DomainState P D) :
    ResidualRouting.family P D (.rem U) = ResidualFamily.rem := rfl

theorem residualRoutingOfState_spec (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    (IsDisResidual P D U ∧ residualRoutingOfState P D U = ResidualRouting.dis U.val) ∨
    (IsRemResidual P D U ∧ residualRoutingOfState P D U = ResidualRouting.rem U.val) := by
  cases U with
  | mk val family =>
      cases family with
      | dis =>
          left
          constructor
          · rfl
          · rfl
      | rem =>
          right
          constructor
          · rfl
          · rfl

end StateMachine
end CaseC
end Lehmer