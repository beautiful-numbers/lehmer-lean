-- FILE: Lean/Lehmer/CaseC/StateMachine/PotentialPhi.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.StateMachine.Actions : def thm
- Lehmer.CaseC.StateMachine.State : def thm
- Lehmer.CaseC.StateMachine.Domain : def thm
- Lehmer.CaseC.StateMachine.Terminal : def thm
- Lehmer.CaseC.StateMachine.GatePass : def thm
- Lehmer.CaseC.StateMachine.Residual : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.StateMachine.Actions
import Lehmer.CaseC.StateMachine.State
import Lehmer.CaseC.StateMachine.Domain
import Lehmer.CaseC.StateMachine.Terminal
import Lehmer.CaseC.StateMachine.GatePass
import Lehmer.CaseC.StateMachine.Residual

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

def phi (P : Params) (U : MachineState P) : ℕ :=
  stateCard P U

@[simp] theorem phi_def (P : Params) (U : MachineState P) :
    phi P U = stateCard P U := rfl

@[simp] theorem phi_mk (P : Params) (S : Support) :
    phi P (CaseC.State.mk S : MachineState P) = supportCard S := rfl

def terminalPhi (P : Params) (D : ClosureData P) (U : TerminalState P D) : ℕ :=
  phi P (terminalState P D U)

@[simp] theorem terminalPhi_def (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalPhi P D U = phi P (terminalState P D U) := rfl

@[simp] theorem terminalPhi_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    terminalPhi P D (TerminalState.mk U) = stateCard P U.val := rfl

def gatePassPhi (P : Params) (D : ClosureData P) (U : GatePassState P D) : ℕ :=
  phi P (gatePassState P D U)

@[simp] theorem gatePassPhi_def (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassPhi P D U = phi P (gatePassState P D U) := rfl

@[simp] theorem gatePassPhi_mk (P : Params) (D : ClosureData P) (U : DomainState P D) :
    gatePassPhi P D (GatePassState.mk U) = stateCard P U.val := rfl

def residualPhi (P : Params) (D : ClosureData P) (U : ResidualState P D) : ℕ :=
  phi P (residualState P D U)

@[simp] theorem residualPhi_def (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualPhi P D U = phi P (residualState P D U) := rfl

@[simp] theorem residualPhi_mk (P : Params) (D : ClosureData P)
    (U : DomainState P D) (f : ResidualFamily) :
    residualPhi P D (ResidualState.mk U f) = stateCard P U.val := rfl

theorem terminalPhi_eq_phi (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalPhi P D U = phi P (terminalState P D U) := rfl

theorem gatePassPhi_eq_phi (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassPhi P D U = phi P (gatePassState P D U) := rfl

theorem residualPhi_eq_phi (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualPhi P D U = phi P (residualState P D U) := rfl

def PhiLe (P : Params) (U V : MachineState P) : Prop :=
  phi P U ≤ phi P V

def PhiLt (P : Params) (U V : MachineState P) : Prop :=
  phi P U < phi P V

@[simp] theorem PhiLe_def (P : Params) (U V : MachineState P) :
    PhiLe P U V = (phi P U ≤ phi P V) := rfl

@[simp] theorem PhiLt_def (P : Params) (U V : MachineState P) :
    PhiLt P U V = (phi P U < phi P V) := rfl

theorem PhiLe_refl (P : Params) (U : MachineState P) :
    PhiLe P U U := by
  exact le_rfl

theorem PhiLt_irrefl (P : Params) (U : MachineState P) :
    ¬ PhiLt P U U := by
  exact Nat.lt_irrefl _

theorem phi_of_support_eq (P : Params) {U V : MachineState P} :
    stateSupport P U = stateSupport P V → phi P U = phi P V := by
  intro h
  unfold phi
  rw [stateCard_def, stateCard_def, h]

theorem terminalPhi_of_support_eq (P : Params) (D : ClosureData P)
    {U V : TerminalState P D} :
    terminalSupport P D U = terminalSupport P D V →
    terminalPhi P D U = terminalPhi P D V := by
  intro h
  apply phi_of_support_eq P
  simpa [terminalSupport_def, terminalState_def] using h

theorem gatePassPhi_of_support_eq (P : Params) (D : ClosureData P)
    {U V : GatePassState P D} :
    gatePassSupport P D U = gatePassSupport P D V →
    gatePassPhi P D U = gatePassPhi P D V := by
  intro h
  apply phi_of_support_eq P
  simpa [gatePassSupport_def, gatePassState_def] using h

theorem residualPhi_of_support_eq (P : Params) (D : ClosureData P)
    {U V : ResidualState P D} :
    residualSupport P D U = residualSupport P D V →
    residualPhi P D U = residualPhi P D V := by
  intro h
  apply phi_of_support_eq P
  simpa [residualSupport_def, residualState_def] using h

theorem phi_nonneg (P : Params) (U : MachineState P) :
    0 ≤ phi P U := by
  exact Nat.zero_le _

theorem terminalPhi_nonneg (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    0 ≤ terminalPhi P D U := by
  exact Nat.zero_le _

theorem gatePassPhi_nonneg (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    0 ≤ gatePassPhi P D U := by
  exact Nat.zero_le _

theorem residualPhi_nonneg (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    0 ≤ residualPhi P D U := by
  exact Nat.zero_le _

theorem terminalPhi_eq_card (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    terminalPhi P D U = stateCard P (terminalState P D U) := rfl

theorem gatePassPhi_eq_card (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    gatePassPhi P D U = stateCard P (gatePassState P D U) := rfl

theorem residualPhi_eq_card (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    residualPhi P D U = stateCard P (residualState P D U) := rfl

end StateMachine
end CaseC
end Lehmer