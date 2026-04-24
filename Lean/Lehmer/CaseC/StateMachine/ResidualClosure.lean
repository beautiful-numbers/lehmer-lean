-- FILE: Lean/Lehmer/CaseC/StateMachine/ResidualClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.StateMachine.Actions : def thm
- Lehmer.CaseC.StateMachine.State : def thm
- Lehmer.CaseC.StateMachine.Domain : def thm
- Lehmer.CaseC.StateMachine.Residual : def thm
- Lehmer.CaseC.StateMachine.PotentialPhi : def thm
- Lehmer.CaseC.StateMachine.WellFounded : def thm
- Lehmer.CaseC.StateMachine.StrictDescent : def thm
- Lehmer.CaseC.StateMachine.NextDis : def thm
- Lehmer.CaseC.StateMachine.NextRem : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.StateMachine.Actions
import Lehmer.CaseC.StateMachine.State
import Lehmer.CaseC.StateMachine.Domain
import Lehmer.CaseC.StateMachine.Residual
import Lehmer.CaseC.StateMachine.PotentialPhi
import Lehmer.CaseC.StateMachine.WellFounded
import Lehmer.CaseC.StateMachine.StrictDescent
import Lehmer.CaseC.StateMachine.NextDis
import Lehmer.CaseC.StateMachine.NextRem

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

theorem residual_state_exhaustive (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsDisResidual P D U ∨ IsRemResidual P D U := by
  exact residualState_family_exhaustive P D U

inductive ResidualClosureRouting (P : Params) (D : ClosureData P) where
  | dis (U : DisResidualState P D)
  | rem (U : RemResidualState P D)

def residualClosureRoutingOfState (P : Params) (D : ClosureData P)
    (U : ResidualState P D) : ResidualClosureRouting P D :=
  match hFam : residualFamily P D U with
  | ResidualFamily.dis =>
      ResidualClosureRouting.dis (mkDisResidualState P D U hFam)
  | ResidualFamily.rem =>
      ResidualClosureRouting.rem (mkRemResidualState P D U hFam)

def ResidualClosureRouting.state (P : Params) (D : ClosureData P) :
    ResidualClosureRouting P D → ResidualState P D
  | .dis U => U.val
  | .rem U => U.val

@[simp] theorem ResidualClosureRouting.state_dis (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    ResidualClosureRouting.state P D (.dis U) = U.val := rfl

@[simp] theorem ResidualClosureRouting.state_rem (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    ResidualClosureRouting.state P D (.rem U) = U.val := rfl

def ResidualClosureRouting.family (P : Params) (D : ClosureData P) :
    ResidualClosureRouting P D → ResidualFamily
  | .dis _ => ResidualFamily.dis
  | .rem _ => ResidualFamily.rem

@[simp] theorem ResidualClosureRouting.family_dis (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    ResidualClosureRouting.family P D (.dis U) = ResidualFamily.dis := rfl

@[simp] theorem ResidualClosureRouting.family_rem (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    ResidualClosureRouting.family P D (.rem U) = ResidualFamily.rem := rfl

theorem ResidualClosureRouting.is_dis (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    IsDisResidual P D (ResidualClosureRouting.state P D (.dis U)) := by
  simpa using U.isDis

theorem ResidualClosureRouting.is_rem (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    IsRemResidual P D (ResidualClosureRouting.state P D (.rem U)) := by
  simpa using U.isRem

theorem ResidualClosureRouting.sound (P : Params) (D : ClosureData P)
    (R : ResidualClosureRouting P D) :
    ResidualClosureRouting.state P D R = match R with
      | .dis U => U.val
      | .rem U => U.val := by
  cases R <;> rfl

theorem residualClosureRoutingOfState_spec (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    (∃ h : IsDisResidual P D U,
        residualClosureRoutingOfState P D U =
          ResidualClosureRouting.dis (mkDisResidualState P D U h)) ∨
      (∃ h : IsRemResidual P D U,
        residualClosureRoutingOfState P D U =
          ResidualClosureRouting.rem (mkRemResidualState P D U h)) := by
  unfold residualClosureRoutingOfState
  split
  · left
    exact ⟨by assumption, rfl⟩
  · right
    exact ⟨by assumption, rfl⟩

@[simp] theorem residualClosureRoutingOfState_state (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualClosureRouting.state P D (residualClosureRoutingOfState P D U) = U := by
  unfold residualClosureRoutingOfState
  split <;> rfl

@[simp] theorem residualClosureRoutingOfState_family (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualClosureRouting.family P D (residualClosureRoutingOfState P D U) = residualFamily P D U := by
  unfold residualClosureRoutingOfState
  split
  · rename_i heq
    exact heq.symm
  · rename_i heq
    exact heq.symm

def ResidualClosed (P : Params) (D : ClosureData P) (U : ResidualState P D) : Prop :=
  ResidualStrictDescentAccessible P D U

@[simp] theorem ResidualClosed_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    ResidualClosed P D U = ResidualStrictDescentAccessible P D U := rfl

theorem dis_residual_closed (P : Params) (D : ClosureData P) (U : DisResidualState P D) :
    ResidualClosed P D U.val := by
  exact residualStrictDescent_accessible P D U.val

theorem rem_residual_closed (P : Params) (D : ClosureData P) (U : RemResidualState P D) :
    ResidualClosed P D U.val := by
  exact residualStrictDescent_accessible P D U.val

theorem residual_closed (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    ResidualClosed P D U := by
  exact residualStrictDescent_accessible P D U

theorem residual_closed_of_routing (P : Params) (D : ClosureData P)
    (R : ResidualClosureRouting P D) :
    ResidualClosed P D (ResidualClosureRouting.state P D R) := by
  cases R with
  | dis U =>
      exact dis_residual_closed P D U
  | rem U =>
      exact rem_residual_closed P D U

theorem residual_closed_by_cases (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    (IsDisResidual P D U ∧ ResidualClosed P D U) ∨
      (IsRemResidual P D U ∧ ResidualClosed P D U) := by
  rcases residual_state_exhaustive P D U with hDis | hRem
  · left
    exact ⟨hDis, residual_closed P D U⟩
  · right
    exact ⟨hRem, residual_closed P D U⟩

theorem residual_closure_routing_closed (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualClosed P D (ResidualClosureRouting.state P D (residualClosureRoutingOfState P D U)) := by
  simpa using residual_closed P D U

theorem residual_closure_family_dis_or_rem (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    residualFamily P D U = ResidualFamily.dis ∨ residualFamily P D U = ResidualFamily.rem := by
  rcases residual_state_exhaustive P D U with hDis | hRem
  · left
    exact hDis
  · right
    exact hRem

theorem dis_step_target_closed (P : Params) (D : ClosureData P) (s : NextDisStep P D) :
    ResidualClosed P D s.target := by
  exact residual_closed P D s.target

theorem dis_step_source_closed (P : Params) (D : ClosureData P) (s : NextDisStep P D) :
    ResidualClosed P D s.source.val := by
  exact residual_closed P D s.source.val

theorem rem_step_target_closed (P : Params) (D : ClosureData P) (s : NextRemStep P D) :
    ResidualClosed P D s.target := by
  exact residual_closed P D s.target

theorem rem_step_source_closed (P : Params) (D : ClosureData P) (s : NextRemStep P D) :
    ResidualClosed P D s.source.val := by
  exact residual_closed P D s.source.val

theorem dis_step_descends (P : Params) (D : ClosureData P) (s : NextDisStep P D) :
    ResidualStrictDescent P D s.target s.source.val := by
  exact s.descent

theorem rem_step_descends (P : Params) (D : ClosureData P) (s : NextRemStep P D) :
    ResidualStrictDescent P D s.target s.source.val := by
  exact s.descent

structure ResidualClosurePackage (P : Params) (D : ClosureData P) where
  state : ResidualState P D
  closed : ResidualClosed P D state

@[simp] theorem ResidualClosurePackage.state_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : ResidualClosed P D U) :
    (ResidualClosurePackage.mk U hU).state = U := rfl

@[simp] theorem ResidualClosurePackage.closed_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : ResidualClosed P D U) :
    (ResidualClosurePackage.mk U hU).closed = hU := rfl

def residualClosurePackageOfState (P : Params) (D : ClosureData P)
    (U : ResidualState P D) : ResidualClosurePackage P D :=
  ResidualClosurePackage.mk U (residual_closed P D U)

@[simp] theorem residualClosurePackageOfState_state (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    (residualClosurePackageOfState P D U).state = U := rfl

@[simp] theorem residualClosurePackageOfState_closed (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    (residualClosurePackageOfState P D U).closed = residual_closed P D U := rfl

end StateMachine
end CaseC
end Lehmer