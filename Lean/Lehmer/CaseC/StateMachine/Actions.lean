-- FILE: Lean/Lehmer/CaseC/StateMachine/Actions.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

abbrev StatusAction := Status

abbrev ResidualAction := ResidualFamily

@[simp] theorem StatusAction.terminal_ne_gatePass :
    (Status.terminal : StatusAction) ≠ (Status.gatePass : StatusAction) := by
  exact Status.terminal_ne_gatePass

@[simp] theorem StatusAction.gatePass_ne_terminal :
    (Status.gatePass : StatusAction) ≠ (Status.terminal : StatusAction) := by
  exact Status.gatePass_ne_terminal

@[simp] theorem ResidualAction.dis_ne_rem :
    (ResidualFamily.dis : ResidualAction) ≠ (ResidualFamily.rem : ResidualAction) := by
  exact ResidualFamily.dis_ne_rem

@[simp] theorem ResidualAction.rem_ne_dis :
    (ResidualFamily.rem : ResidualAction) ≠ (ResidualFamily.dis : ResidualAction) := by
  exact ResidualFamily.rem_ne_dis

theorem residualFamily_exhaustive (f : ResidualFamily) :
    f = ResidualFamily.dis ∨ f = ResidualFamily.rem := by
  cases f with
  | dis =>
      left
      rfl
  | rem =>
      right
      rfl

def ResidualPriority (a b : ResidualFamily) : Prop :=
  a = ResidualFamily.dis ∨ b = ResidualFamily.rem

@[simp] theorem ResidualPriority_def (a b : ResidualFamily) :
    ResidualPriority a b = (a = ResidualFamily.dis ∨ b = ResidualFamily.rem) := rfl

theorem dis_priority_over_rem :
    ResidualPriority ResidualFamily.dis ResidualFamily.rem := by
  left
  rfl

theorem dis_priority_over_dis :
    ResidualPriority ResidualFamily.dis ResidualFamily.dis := by
  left
  rfl

theorem rem_priority_over_rem :
    ResidualPriority ResidualFamily.rem ResidualFamily.rem := by
  right
  rfl

theorem not_rem_priority_over_dis :
    ¬ ResidualPriority ResidualFamily.rem ResidualFamily.dis := by
  intro h
  rcases h with h | h
  · exact ResidualFamily.rem_ne_dis h
  · exact ResidualFamily.dis_ne_rem h

inductive MachineAction where
  | terminal
  | gatePass
  | residual (f : ResidualFamily)
deriving DecidableEq

@[simp] theorem MachineAction.terminal_ne_gatePass :
    MachineAction.terminal ≠ MachineAction.gatePass := by
  decide

@[simp] theorem MachineAction.terminal_ne_residual_dis :
    MachineAction.terminal ≠ MachineAction.residual ResidualFamily.dis := by
  decide

@[simp] theorem MachineAction.terminal_ne_residual_rem :
    MachineAction.terminal ≠ MachineAction.residual ResidualFamily.rem := by
  decide

@[simp] theorem MachineAction.gatePass_ne_terminal :
    MachineAction.gatePass ≠ MachineAction.terminal := by
  decide

@[simp] theorem MachineAction.gatePass_ne_residual_dis :
    MachineAction.gatePass ≠ MachineAction.residual ResidualFamily.dis := by
  decide

@[simp] theorem MachineAction.gatePass_ne_residual_rem :
    MachineAction.gatePass ≠ MachineAction.residual ResidualFamily.rem := by
  decide

@[simp] theorem MachineAction.residual_dis_ne_terminal :
    MachineAction.residual ResidualFamily.dis ≠ MachineAction.terminal := by
  decide

@[simp] theorem MachineAction.residual_rem_ne_terminal :
    MachineAction.residual ResidualFamily.rem ≠ MachineAction.terminal := by
  decide

@[simp] theorem MachineAction.residual_dis_ne_gatePass :
    MachineAction.residual ResidualFamily.dis ≠ MachineAction.gatePass := by
  decide

@[simp] theorem MachineAction.residual_rem_ne_gatePass :
    MachineAction.residual ResidualFamily.rem ≠ MachineAction.gatePass := by
  decide

@[simp] theorem MachineAction.residual_dis_ne_residual_rem :
    MachineAction.residual ResidualFamily.dis ≠ MachineAction.residual ResidualFamily.rem := by
  decide

@[simp] theorem MachineAction.residual_rem_ne_residual_dis :
    MachineAction.residual ResidualFamily.rem ≠ MachineAction.residual ResidualFamily.dis := by
  decide

def IsTerminalAction (a : MachineAction) : Prop :=
  a = MachineAction.terminal

def IsGatePassAction (a : MachineAction) : Prop :=
  a = MachineAction.gatePass

def IsResidualAction (a : MachineAction) : Prop :=
  ∃ f : ResidualFamily, a = MachineAction.residual f

def IsDisAction (a : MachineAction) : Prop :=
  a = MachineAction.residual ResidualFamily.dis

def IsRemAction (a : MachineAction) : Prop :=
  a = MachineAction.residual ResidualFamily.rem

@[simp] theorem IsTerminalAction_def (a : MachineAction) :
    IsTerminalAction a = (a = MachineAction.terminal) := rfl

@[simp] theorem IsGatePassAction_def (a : MachineAction) :
    IsGatePassAction a = (a = MachineAction.gatePass) := rfl

@[simp] theorem IsResidualAction_def (a : MachineAction) :
    IsResidualAction a = (∃ f : ResidualFamily, a = MachineAction.residual f) := rfl

@[simp] theorem IsDisAction_def (a : MachineAction) :
    IsDisAction a = (a = MachineAction.residual ResidualFamily.dis) := rfl

@[simp] theorem IsRemAction_def (a : MachineAction) :
    IsRemAction a = (a = MachineAction.residual ResidualFamily.rem) := rfl

def actionStatus? : MachineAction → Option Status
  | .terminal => some Status.terminal
  | .gatePass => some Status.gatePass
  | .residual _ => none

def actionResidual? : MachineAction → Option ResidualFamily
  | .terminal => none
  | .gatePass => none
  | .residual f => some f

@[simp] theorem actionStatus?_terminal :
    actionStatus? MachineAction.terminal = some Status.terminal := rfl

@[simp] theorem actionStatus?_gatePass :
    actionStatus? MachineAction.gatePass = some Status.gatePass := rfl

@[simp] theorem actionStatus?_residual (f : ResidualFamily) :
    actionStatus? (MachineAction.residual f) = none := rfl

@[simp] theorem actionResidual?_terminal :
    actionResidual? MachineAction.terminal = none := rfl

@[simp] theorem actionResidual?_gatePass :
    actionResidual? MachineAction.gatePass = none := rfl

@[simp] theorem actionResidual?_residual (f : ResidualFamily) :
    actionResidual? (MachineAction.residual f) = some f := rfl

theorem MachineAction.exhaustive (a : MachineAction) :
    IsTerminalAction a ∨ IsGatePassAction a ∨ IsDisAction a ∨ IsRemAction a := by
  cases a with
  | terminal =>
      left
      rfl
  | gatePass =>
      right
      left
      rfl
  | residual f =>
      cases f with
      | dis =>
          right
          right
          left
          rfl
      | rem =>
          right
          right
          right
          rfl

theorem IsTerminalAction.not_gatePass (a : MachineAction) :
    IsTerminalAction a → ¬ IsGatePassAction a := by
  intro hT hG
  rw [hT] at hG
  exact MachineAction.terminal_ne_gatePass hG

theorem IsTerminalAction.not_dis (a : MachineAction) :
    IsTerminalAction a → ¬ IsDisAction a := by
  intro hT hD
  rw [hT] at hD
  exact MachineAction.terminal_ne_residual_dis hD

theorem IsTerminalAction.not_rem (a : MachineAction) :
    IsTerminalAction a → ¬ IsRemAction a := by
  intro hT hR
  rw [hT] at hR
  exact MachineAction.terminal_ne_residual_rem hR

theorem IsGatePassAction.not_terminal (a : MachineAction) :
    IsGatePassAction a → ¬ IsTerminalAction a := by
  intro hG hT
  exact (IsTerminalAction.not_gatePass a hT) hG

theorem IsGatePassAction.not_dis (a : MachineAction) :
    IsGatePassAction a → ¬ IsDisAction a := by
  intro hG hD
  rw [hG] at hD
  exact MachineAction.gatePass_ne_residual_dis hD

theorem IsGatePassAction.not_rem (a : MachineAction) :
    IsGatePassAction a → ¬ IsRemAction a := by
  intro hG hR
  rw [hG] at hR
  exact MachineAction.gatePass_ne_residual_rem hR

theorem IsDisAction.not_terminal (a : MachineAction) :
    IsDisAction a → ¬ IsTerminalAction a := by
  intro hD hT
  exact (IsTerminalAction.not_dis a hT) hD

theorem IsDisAction.not_gatePass (a : MachineAction) :
    IsDisAction a → ¬ IsGatePassAction a := by
  intro hD hG
  exact (IsGatePassAction.not_dis a hG) hD

theorem IsDisAction.not_rem (a : MachineAction) :
    IsDisAction a → ¬ IsRemAction a := by
  intro hD hR
  rw [hD] at hR
  exact MachineAction.residual_dis_ne_residual_rem hR

theorem IsRemAction.not_terminal (a : MachineAction) :
    IsRemAction a → ¬ IsTerminalAction a := by
  intro hR hT
  exact (IsTerminalAction.not_rem a hT) hR

theorem IsRemAction.not_gatePass (a : MachineAction) :
    IsRemAction a → ¬ IsGatePassAction a := by
  intro hR hG
  exact (IsGatePassAction.not_rem a hG) hR

theorem IsRemAction.not_dis (a : MachineAction) :
    IsRemAction a → ¬ IsDisAction a := by
  intro hR hD
  exact (IsDisAction.not_rem a hD) hR

theorem IsResidualAction_iff_dis_or_rem (a : MachineAction) :
    IsResidualAction a ↔ IsDisAction a ∨ IsRemAction a := by
  constructor
  · intro h
    rcases h with ⟨f, rfl⟩
    cases f with
    | dis =>
        left
        rfl
    | rem =>
        right
        rfl
  · intro h
    rcases h with h | h
    · exact ⟨ResidualFamily.dis, h⟩
    · exact ⟨ResidualFamily.rem, h⟩

theorem residualAction_exhaustive (a : ResidualAction) :
    a = ResidualFamily.dis ∨ a = ResidualFamily.rem := by
  exact residualFamily_exhaustive a

end StateMachine
end CaseC
end Lehmer