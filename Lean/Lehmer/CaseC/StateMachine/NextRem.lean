-- FILE: Lean/Lehmer/CaseC/StateMachine/NextRem.lean
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

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

structure RemResidualState (P : Params) (D : ClosureData P) where
  val : ResidualState P D
  isRem : IsRemResidual P D val

@[simp] theorem RemResidualState.val_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsRemResidual P D U) :
    (RemResidualState.mk U hU).val = U := rfl

@[simp] theorem RemResidualState.isRem_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsRemResidual P D U) :
    (RemResidualState.mk U hU).isRem = hU := rfl

def remResidualState (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) : ResidualState P D :=
  U.val

@[simp] theorem remResidualState_def (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    remResidualState P D U = U.val := rfl

def remResidualFamily (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) : ResidualFamily :=
  residualFamily P D U.val

@[simp] theorem remResidualFamily_def (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    remResidualFamily P D U = residualFamily P D U.val := rfl

def remResidualSupport (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) : Support :=
  residualSupport P D U.val

@[simp] theorem remResidualSupport_def (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    remResidualSupport P D U = residualSupport P D U.val := rfl

def remResidualPhi (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) : ℕ :=
  residualPhi P D U.val

@[simp] theorem remResidualPhi_def (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    remResidualPhi P D U = residualPhi P D U.val := rfl

@[simp] theorem remResidualFamily_eq_rem (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    remResidualFamily P D U = ResidualFamily.rem := by
  exact U.isRem

@[simp] theorem remResidualSupport_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsRemResidual P D U) :
    remResidualSupport P D (RemResidualState.mk U hU) = residualSupport P D U := rfl

@[simp] theorem remResidualPhi_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsRemResidual P D U) :
    remResidualPhi P D (RemResidualState.mk U hU) = residualPhi P D U := rfl

theorem remResidual_underlying_inDomain (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    InDomain P D (residualState P D U.val) := by
  exact residual_underlying_inDomain P D U.val

theorem remResidual_support_below (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    SupportBelow D.N (remResidualSupport P D U) := by
  exact residual_support_below P D U.val

theorem remResidual_support_within_omega (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    SupportWithinOmega D.omegaHat (remResidualSupport P D U) := by
  exact residual_support_within_omega P D U.val

theorem remResidual_accessible (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    ResidualStrictDescentAccessible P D U.val := by
  exact residualStrictDescent_accessible P D U.val

structure NextRemStep (P : Params) (D : ClosureData P) where
  source : RemResidualState P D
  target : ResidualState P D
  descent : ResidualStrictDescent P D target source.val

@[simp] theorem NextRemStep.source_mk (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (NextRemStep.mk U V h).source = U := rfl

@[simp] theorem NextRemStep.target_mk (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (NextRemStep.mk U V h).target = V := rfl

@[simp] theorem NextRemStep.descent_mk (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (NextRemStep.mk U V h).descent = h := rfl

def nextRemSource (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) : RemResidualState P D :=
  s.source

@[simp] theorem nextRemSource_def (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemSource P D s = s.source := rfl

def nextRemTarget (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) : ResidualState P D :=
  s.target

@[simp] theorem nextRemTarget_def (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemTarget P D s = s.target := rfl

def nextRemDescent (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) : Prop :=
  ResidualStrictDescent P D (nextRemTarget P D s) (nextRemSource P D s).val

@[simp] theorem nextRemDescent_def (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemDescent P D s =
      ResidualStrictDescent P D (nextRemTarget P D s) (nextRemSource P D s).val := rfl

theorem nextRem_descent_iff (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemDescent P D s ↔
      residualPhi P D s.target < residualPhi P D s.source.val := by
  rfl

theorem nextRem_descent_holds (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemDescent P D s := by
  exact s.descent

theorem nextRem_source_family_eq_rem (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    residualFamily P D s.source.val = ResidualFamily.rem := by
  exact s.source.isRem

def nextRemSourcePhi (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) : ℕ :=
  remResidualPhi P D s.source

@[simp] theorem nextRemSourcePhi_def (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemSourcePhi P D s = remResidualPhi P D s.source := rfl

def nextRemTargetPhi (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) : ℕ :=
  residualPhi P D s.target

@[simp] theorem nextRemTargetPhi_def (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemTargetPhi P D s = residualPhi P D s.target := rfl

theorem nextRem_phi_strict (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    nextRemTargetPhi P D s < nextRemSourcePhi P D s := by
  exact s.descent

theorem nextRem_target_accessible (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    ResidualStrictDescentAccessible P D s.target := by
  exact residualStrictDescent_accessible P D s.target

theorem nextRem_source_accessible (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    ResidualStrictDescentAccessible P D s.source.val := by
  exact residualStrictDescent_accessible P D s.source.val

theorem nextRem_target_inDomain (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    InDomain P D (residualState P D s.target) := by
  exact residual_underlying_inDomain P D s.target

theorem nextRem_source_inDomain (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    InDomain P D (residualState P D s.source.val) := by
  exact residual_underlying_inDomain P D s.source.val

theorem nextRem_irrefl (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    ¬ ResidualStrictDescent P D U.val U.val := by
  exact not_ResidualStrictDescent_self P D U.val

theorem nextRem_of_support_eq_false (P : Params) (D : ClosureData P)
    (s : NextRemStep P D) :
    residualSupport P D s.target = residualSupport P D s.source.val → False := by
  intro hEq
  have hPhiEq : residualPhi P D s.target = residualPhi P D s.source.val := by
    exact residualPhi_of_support_eq P D hEq
  have hLt : residualPhi P D s.target < residualPhi P D s.source.val := by
    exact s.descent
  exact Nat.lt_irrefl _ (hPhiEq ▸ hLt)

def mkRemResidualState (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsRemResidual P D U) : RemResidualState P D :=
  RemResidualState.mk U hU

@[simp] theorem mkRemResidualState_val (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsRemResidual P D U) :
    (mkRemResidualState P D U hU).val = U := rfl

@[simp] theorem mkRemResidualState_isRem (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsRemResidual P D U) :
    (mkRemResidualState P D U hU).isRem = hU := rfl

def mkNextRemStep (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) : NextRemStep P D :=
  NextRemStep.mk U V h

@[simp] theorem mkNextRemStep_source (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (mkNextRemStep P D U V h).source = U := rfl

@[simp] theorem mkNextRemStep_target (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (mkNextRemStep P D U V h).target = V := rfl

@[simp] theorem mkNextRemStep_descent (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (mkNextRemStep P D U V h).descent = h := rfl

end StateMachine
end CaseC
end Lehmer