-- FILE: Lean/Lehmer/CaseC/StateMachine/Terminal.lean
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

structure TerminalState (P : Params) (D : ClosureData P) where
  val : DomainState P D

@[simp] theorem TerminalState.val_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) :
    (TerminalState.mk U).val = U := rfl

def terminalVal (P : Params) (D : ClosureData P) (U : TerminalState P D) : DomainState P D :=
  U.val

@[simp] theorem terminalVal_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalVal P D U = U.val := rfl

def terminalState (P : Params) (D : ClosureData P) (U : TerminalState P D) : MachineState P :=
  U.val.val

@[simp] theorem terminalState_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalState P D U = U.val.val := rfl

def terminalSupport (P : Params) (D : ClosureData P) (U : TerminalState P D) : Support :=
  stateSupport P (terminalState P D U)

@[simp] theorem terminalSupport_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalSupport P D U = stateSupport P (terminalState P D U) := rfl

def terminalCard (P : Params) (D : ClosureData P) (U : TerminalState P D) : ℕ :=
  stateCard P (terminalState P D U)

@[simp] theorem terminalCard_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalCard P D U = stateCard P (terminalState P D U) := rfl

def terminalAction (P : Params) (D : ClosureData P) (_ : TerminalState P D) : MachineAction :=
  MachineAction.terminal

@[simp] theorem terminalAction_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalAction P D U = MachineAction.terminal := rfl

def terminalStatus (P : Params) (D : ClosureData P) (_ : TerminalState P D) : Status :=
  Status.terminal

@[simp] theorem terminalStatus_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalStatus P D U = Status.terminal := rfl

@[simp] theorem terminalState_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    terminalState P D (TerminalState.mk U) = U.val := rfl

@[simp] theorem terminalSupport_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    terminalSupport P D (TerminalState.mk U) = stateSupport P U.val := rfl

@[simp] theorem terminalCard_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    terminalCard P D (TerminalState.mk U) = stateCard P U.val := rfl

@[simp] theorem terminalAction_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    terminalAction P D (TerminalState.mk U) = MachineAction.terminal := rfl

@[simp] theorem terminalStatus_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    terminalStatus P D (TerminalState.mk U) = Status.terminal := rfl

theorem terminal_underlying_inDomain (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    InDomain P D (terminalState P D U) := by
  exact U.val.property

theorem terminal_support_below (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    SupportBelow D.N (terminalSupport P D U) := by
  exact domainState_support_below P D U.val

theorem terminal_support_within_omega (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    SupportWithinOmega D.omegaHat (terminalSupport P D U) := by
  exact domainState_support_within_omega P D U.val

theorem terminalAction_is_terminal (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    IsTerminalAction (terminalAction P D U) := by
  rfl

theorem terminalAction_not_gatePass (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    ¬ IsGatePassAction (terminalAction P D U) := by
  intro h
  exact (IsTerminalAction.not_gatePass (terminalAction P D U) (terminalAction_is_terminal P D U)) h

theorem terminalAction_not_dis (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    ¬ IsDisAction (terminalAction P D U) := by
  intro h
  exact (IsTerminalAction.not_dis (terminalAction P D U) (terminalAction_is_terminal P D U)) h

theorem terminalAction_not_rem (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    ¬ IsRemAction (terminalAction P D U) := by
  intro h
  exact (IsTerminalAction.not_rem (terminalAction P D U) (terminalAction_is_terminal P D U)) h

theorem terminal_eq_of_val_eq (P : Params) (D : ClosureData P) {U V : TerminalState P D} :
    terminalVal P D U = terminalVal P D V → U = V := by
  intro h
  cases U
  cases V
  simp [terminalVal] at h
  cases h
  rfl

@[ext] theorem TerminalState.ext (P : Params) (D : ClosureData P) {U V : TerminalState P D}
    (h : terminalVal P D U = terminalVal P D V) : U = V :=
  terminal_eq_of_val_eq P D h

def terminalSupportEmpty (P : Params) (D : ClosureData P) (U : TerminalState P D) : Prop :=
  terminalSupport P D U = ∅

@[simp] theorem terminalSupportEmpty_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalSupportEmpty P D U = (terminalSupport P D U = ∅) := rfl

def terminalSupportNonempty (P : Params) (D : ClosureData P) (U : TerminalState P D) : Prop :=
  (terminalSupport P D U).Nonempty

@[simp] theorem terminalSupportNonempty_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalSupportNonempty P D U = (terminalSupport P D U).Nonempty := rfl

theorem terminalSupport_empty_or_nonempty (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalSupportEmpty P D U ∨ terminalSupportNonempty P D U := by
  by_cases h : terminalSupport P D U = ∅
  · left
    exact h
  · right
    exact Finset.nonempty_iff_ne_empty.mpr h

theorem terminalSupportNonempty_iff_not_empty (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalSupportNonempty P D U ↔ ¬ terminalSupportEmpty P D U := by
  constructor
  · intro h hEmpty
    have hne : terminalSupport P D U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h
    exact hne hEmpty
  · intro h
    exact Finset.nonempty_iff_ne_empty.mpr (by
      simpa [terminalSupportEmpty] using h)

end StateMachine
end CaseC
end Lehmer