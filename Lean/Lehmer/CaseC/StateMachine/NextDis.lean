-- FILE: Lean/Lehmer/CaseC/StateMachine/NextDis.lean
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

structure DisResidualState (P : Params) (D : ClosureData P) where
  val : ResidualState P D
  isDis : IsDisResidual P D val

@[simp] theorem DisResidualState.val_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsDisResidual P D U) :
    (DisResidualState.mk U hU).val = U := rfl

@[simp] theorem DisResidualState.isDis_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsDisResidual P D U) :
    (DisResidualState.mk U hU).isDis = hU := rfl

def disResidualState (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) : ResidualState P D :=
  U.val

@[simp] theorem disResidualState_def (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    disResidualState P D U = U.val := rfl

def disResidualFamily (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) : ResidualFamily :=
  residualFamily P D U.val

@[simp] theorem disResidualFamily_def (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    disResidualFamily P D U = residualFamily P D U.val := rfl

def disResidualSupport (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) : Support :=
  residualSupport P D U.val

@[simp] theorem disResidualSupport_def (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    disResidualSupport P D U = residualSupport P D U.val := rfl

def disResidualPhi (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) : ℕ :=
  residualPhi P D U.val

@[simp] theorem disResidualPhi_def (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    disResidualPhi P D U = residualPhi P D U.val := rfl

@[simp] theorem disResidualFamily_eq_dis (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    disResidualFamily P D U = ResidualFamily.dis := by
  exact U.isDis

@[simp] theorem disResidualSupport_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsDisResidual P D U) :
    disResidualSupport P D (DisResidualState.mk U hU) = residualSupport P D U := rfl

@[simp] theorem disResidualPhi_mk (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsDisResidual P D U) :
    disResidualPhi P D (DisResidualState.mk U hU) = residualPhi P D U := rfl

theorem disResidual_underlying_inDomain (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    InDomain P D (residualState P D U.val) := by
  exact residual_underlying_inDomain P D U.val

theorem disResidual_support_below (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    SupportBelow D.N (disResidualSupport P D U) := by
  exact residual_support_below P D U.val

theorem disResidual_support_within_omega (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    SupportWithinOmega D.omegaHat (disResidualSupport P D U) := by
  exact residual_support_within_omega P D U.val

theorem disResidual_accessible (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    ResidualStrictDescentAccessible P D U.val := by
  exact residualStrictDescent_accessible P D U.val

structure NextDisStep (P : Params) (D : ClosureData P) where
  source : DisResidualState P D
  target : ResidualState P D
  descent : ResidualStrictDescent P D target source.val

@[simp] theorem NextDisStep.source_mk (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (NextDisStep.mk U V h).source = U := rfl

@[simp] theorem NextDisStep.target_mk (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (NextDisStep.mk U V h).target = V := rfl

@[simp] theorem NextDisStep.descent_mk (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (NextDisStep.mk U V h).descent = h := rfl

def nextDisSource (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) : DisResidualState P D :=
  s.source

@[simp] theorem nextDisSource_def (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisSource P D s = s.source := rfl

def nextDisTarget (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) : ResidualState P D :=
  s.target

@[simp] theorem nextDisTarget_def (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisTarget P D s = s.target := rfl

def nextDisDescent (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) : Prop :=
  ResidualStrictDescent P D (nextDisTarget P D s) (nextDisSource P D s).val

@[simp] theorem nextDisDescent_def (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisDescent P D s =
      ResidualStrictDescent P D (nextDisTarget P D s) (nextDisSource P D s).val := rfl

theorem nextDis_descent_iff (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisDescent P D s ↔
      residualPhi P D s.target < residualPhi P D s.source.val := by
  rfl

theorem nextDis_descent_holds (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisDescent P D s := by
  exact s.descent

theorem nextDis_source_family_eq_dis (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    residualFamily P D s.source.val = ResidualFamily.dis := by
  exact s.source.isDis

def nextDisSourcePhi (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) : ℕ :=
  disResidualPhi P D s.source

@[simp] theorem nextDisSourcePhi_def (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisSourcePhi P D s = disResidualPhi P D s.source := rfl

def nextDisTargetPhi (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) : ℕ :=
  residualPhi P D s.target

@[simp] theorem nextDisTargetPhi_def (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisTargetPhi P D s = residualPhi P D s.target := rfl

theorem nextDis_phi_strict (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    nextDisTargetPhi P D s < nextDisSourcePhi P D s := by
  exact s.descent

theorem nextDis_target_accessible (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    ResidualStrictDescentAccessible P D s.target := by
  exact residualStrictDescent_accessible P D s.target

theorem nextDis_source_accessible (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    ResidualStrictDescentAccessible P D s.source.val := by
  exact residualStrictDescent_accessible P D s.source.val

theorem nextDis_target_inDomain (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    InDomain P D (residualState P D s.target) := by
  exact residual_underlying_inDomain P D s.target

theorem nextDis_source_inDomain (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    InDomain P D (residualState P D s.source.val) := by
  exact residual_underlying_inDomain P D s.source.val

theorem nextDis_irrefl (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    ¬ ResidualStrictDescent P D U.val U.val := by
  exact not_ResidualStrictDescent_self P D U.val

theorem nextDis_of_support_eq_false (P : Params) (D : ClosureData P)
    (s : NextDisStep P D) :
    residualSupport P D s.target = residualSupport P D s.source.val → False := by
  intro hEq
  have hPhiEq : residualPhi P D s.target = residualPhi P D s.source.val := by
    exact residualPhi_of_support_eq P D hEq
  have hLt : residualPhi P D s.target < residualPhi P D s.source.val := by
    exact s.descent
  exact Nat.lt_irrefl _ (hPhiEq ▸ hLt)

def mkDisResidualState (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsDisResidual P D U) : DisResidualState P D :=
  DisResidualState.mk U hU

@[simp] theorem mkDisResidualState_val (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsDisResidual P D U) :
    (mkDisResidualState P D U hU).val = U := rfl

@[simp] theorem mkDisResidualState_isDis (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : IsDisResidual P D U) :
    (mkDisResidualState P D U hU).isDis = hU := rfl

def mkNextDisStep (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) : NextDisStep P D :=
  NextDisStep.mk U V h

@[simp] theorem mkNextDisStep_source (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (mkNextDisStep P D U V h).source = U := rfl

@[simp] theorem mkNextDisStep_target (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (mkNextDisStep P D U V h).target = V := rfl

@[simp] theorem mkNextDisStep_descent (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) (V : ResidualState P D)
    (h : ResidualStrictDescent P D V U.val) :
    (mkNextDisStep P D U V h).descent = h := rfl

end StateMachine
end CaseC
end Lehmer