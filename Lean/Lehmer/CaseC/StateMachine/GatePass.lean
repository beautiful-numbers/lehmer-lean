-- FILE: Lean/Lehmer/CaseC/StateMachine/GatePass.lean
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

structure GatePassState (P : Params) (D : ClosureData P) where
  val : DomainState P D

@[simp] theorem GatePassState.val_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) :
    (GatePassState.mk U).val = U := rfl

def gatePassVal (P : Params) (D : ClosureData P) (U : GatePassState P D) : DomainState P D :=
  U.val

@[simp] theorem gatePassVal_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassVal P D U = U.val := rfl

def gatePassState (P : Params) (D : ClosureData P) (U : GatePassState P D) : MachineState P :=
  U.val.val

@[simp] theorem gatePassState_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassState P D U = U.val.val := rfl

def gatePassSupport (P : Params) (D : ClosureData P) (U : GatePassState P D) : Support :=
  stateSupport P (gatePassState P D U)

@[simp] theorem gatePassSupport_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassSupport P D U = stateSupport P (gatePassState P D U) := rfl

def gatePassCard (P : Params) (D : ClosureData P) (U : GatePassState P D) : ℕ :=
  stateCard P (gatePassState P D U)

@[simp] theorem gatePassCard_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassCard P D U = stateCard P (gatePassState P D U) := rfl

def gatePassAction (P : Params) (D : ClosureData P) (_ : GatePassState P D) : MachineAction :=
  MachineAction.gatePass

@[simp] theorem gatePassAction_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassAction P D U = MachineAction.gatePass := rfl

def gatePassStatus (P : Params) (D : ClosureData P) (_ : GatePassState P D) : Status :=
  Status.gatePass

@[simp] theorem gatePassStatus_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassStatus P D U = Status.gatePass := rfl

@[simp] theorem gatePassState_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    gatePassState P D (GatePassState.mk U) = U.val := rfl

@[simp] theorem gatePassSupport_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    gatePassSupport P D (GatePassState.mk U) = stateSupport P U.val := rfl

@[simp] theorem gatePassCard_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    gatePassCard P D (GatePassState.mk U) = stateCard P U.val := rfl

@[simp] theorem gatePassAction_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    gatePassAction P D (GatePassState.mk U) = MachineAction.gatePass := rfl

@[simp] theorem gatePassStatus_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    gatePassStatus P D (GatePassState.mk U) = Status.gatePass := rfl

theorem gatePass_underlying_inDomain (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    InDomain P D (gatePassState P D U) := by
  exact U.val.property

theorem gatePass_support_below (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    SupportBelow D.N (gatePassSupport P D U) := by
  exact domainState_support_below P D U.val

theorem gatePass_support_within_omega (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    SupportWithinOmega D.omegaHat (gatePassSupport P D U) := by
  exact domainState_support_within_omega P D U.val

theorem gatePassAction_is_gatePass (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    IsGatePassAction (gatePassAction P D U) := by
  rfl

theorem gatePassAction_not_terminal (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    ¬ IsTerminalAction (gatePassAction P D U) := by
  intro h
  exact (IsGatePassAction.not_terminal (gatePassAction P D U) (gatePassAction_is_gatePass P D U)) h

theorem gatePassAction_not_dis (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    ¬ IsDisAction (gatePassAction P D U) := by
  intro h
  exact (IsGatePassAction.not_dis (gatePassAction P D U) (gatePassAction_is_gatePass P D U)) h

theorem gatePassAction_not_rem (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    ¬ IsRemAction (gatePassAction P D U) := by
  intro h
  exact (IsGatePassAction.not_rem (gatePassAction P D U) (gatePassAction_is_gatePass P D U)) h

theorem gatePass_eq_of_val_eq (P : Params) (D : ClosureData P) {U V : GatePassState P D} :
    gatePassVal P D U = gatePassVal P D V → U = V := by
  intro h
  cases U
  cases V
  simp [gatePassVal] at h
  cases h
  rfl

@[ext] theorem GatePassState.ext (P : Params) (D : ClosureData P) {U V : GatePassState P D}
    (h : gatePassVal P D U = gatePassVal P D V) : U = V :=
  gatePass_eq_of_val_eq P D h

def gatePassSupportEmpty (P : Params) (D : ClosureData P) (U : GatePassState P D) : Prop :=
  gatePassSupport P D U = ∅

@[simp] theorem gatePassSupportEmpty_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassSupportEmpty P D U = (gatePassSupport P D U = ∅) := rfl

def gatePassSupportNonempty (P : Params) (D : ClosureData P) (U : GatePassState P D) : Prop :=
  (gatePassSupport P D U).Nonempty

@[simp] theorem gatePassSupportNonempty_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassSupportNonempty P D U = (gatePassSupport P D U).Nonempty := rfl

theorem gatePassSupport_empty_or_nonempty (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassSupportEmpty P D U ∨ gatePassSupportNonempty P D U := by
  by_cases h : gatePassSupport P D U = ∅
  · left
    exact h
  · right
    exact Finset.nonempty_iff_ne_empty.mpr h

theorem gatePassSupportNonempty_iff_not_empty (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassSupportNonempty P D U ↔ ¬ gatePassSupportEmpty P D U := by
  constructor
  · intro h hEmpty
    have hne : gatePassSupport P D U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h
    exact hne hEmpty
  · intro h
    exact Finset.nonempty_iff_ne_empty.mpr (by
      simpa [gatePassSupportEmpty] using h)

end StateMachine
end CaseC
end Lehmer