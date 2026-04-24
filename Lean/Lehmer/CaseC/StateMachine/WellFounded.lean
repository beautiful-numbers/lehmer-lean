-- FILE: Lean/Lehmer/CaseC/StateMachine/WellFounded.lean
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
- Lehmer.CaseC.StateMachine.PotentialPhi : def thm
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
import Lehmer.CaseC.StateMachine.PotentialPhi

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

def PhiRel (P : Params) (U V : MachineState P) : Prop :=
  phi P U < phi P V

@[simp] theorem PhiRel_def (P : Params) (U V : MachineState P) :
    PhiRel P U V = (phi P U < phi P V) := rfl

theorem phiRel_iff (P : Params) (U V : MachineState P) :
    PhiRel P U V ↔ phi P U < phi P V := Iff.rfl

theorem not_PhiRel_self (P : Params) (U : MachineState P) :
    ¬ PhiRel P U U := by
  exact Nat.lt_irrefl _

theorem PhiRel_trans (P : Params) {U V W : MachineState P} :
    PhiRel P U V → PhiRel P V W → PhiRel P U W := by
  intro hUV hVW
  exact Nat.lt_trans hUV hVW

theorem PhiRel_of_support_eq (P : Params) {U V W : MachineState P} :
    stateSupport P U = stateSupport P V →
    (PhiRel P U W ↔ PhiRel P V W) := by
  intro hUV
  constructor
  · intro h
    unfold PhiRel at h ⊢
    rw [phi_of_support_eq P hUV] at h
    exact h
  · intro h
    unfold PhiRel at h ⊢
    rw [phi_of_support_eq P hUV]
    exact h

theorem PhiRel_to_support_eq (P : Params) {U V W : MachineState P} :
    stateSupport P V = stateSupport P W →
    (PhiRel P U V ↔ PhiRel P U W) := by
  intro hVW
  constructor
  · intro h
    unfold PhiRel at h ⊢
    rw [← phi_of_support_eq P hVW]
    exact h
  · intro h
    unfold PhiRel at h ⊢
    rw [← phi_of_support_eq P hVW] at h
    exact h

theorem PhiRel_wellFounded (P : Params) :
    WellFounded (PhiRel P) := by
  classical
  unfold PhiRel
  simpa using (measure (phi P)).wf

def TerminalPhiRel (P : Params) (D : ClosureData P)
    (U V : TerminalState P D) : Prop :=
  PhiRel P (terminalState P D U) (terminalState P D V)

def GatePassPhiRel (P : Params) (D : ClosureData P)
    (U V : GatePassState P D) : Prop :=
  PhiRel P (gatePassState P D U) (gatePassState P D V)

def ResidualPhiRel (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) : Prop :=
  PhiRel P (residualState P D U) (residualState P D V)

@[simp] theorem TerminalPhiRel_def (P : Params) (D : ClosureData P)
    (U V : TerminalState P D) :
    TerminalPhiRel P D U V =
      PhiRel P (terminalState P D U) (terminalState P D V) := rfl

@[simp] theorem GatePassPhiRel_def (P : Params) (D : ClosureData P)
    (U V : GatePassState P D) :
    GatePassPhiRel P D U V =
      PhiRel P (gatePassState P D U) (gatePassState P D V) := rfl

@[simp] theorem ResidualPhiRel_def (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) :
    ResidualPhiRel P D U V =
      PhiRel P (residualState P D U) (residualState P D V) := rfl

theorem TerminalPhiRel_iff (P : Params) (D : ClosureData P)
    (U V : TerminalState P D) :
    TerminalPhiRel P D U V ↔ terminalPhi P D U < terminalPhi P D V := by
  rfl

theorem GatePassPhiRel_iff (P : Params) (D : ClosureData P)
    (U V : GatePassState P D) :
    GatePassPhiRel P D U V ↔ gatePassPhi P D U < gatePassPhi P D V := by
  rfl

theorem ResidualPhiRel_iff (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) :
    ResidualPhiRel P D U V ↔ residualPhi P D U < residualPhi P D V := by
  rfl

theorem not_TerminalPhiRel_self (P : Params) (D : ClosureData P)
    (U : TerminalState P D) :
    ¬ TerminalPhiRel P D U U := by
  exact not_PhiRel_self P _

theorem not_GatePassPhiRel_self (P : Params) (D : ClosureData P)
    (U : GatePassState P D) :
    ¬ GatePassPhiRel P D U U := by
  exact not_PhiRel_self P _

theorem not_ResidualPhiRel_self (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ¬ ResidualPhiRel P D U U := by
  exact not_PhiRel_self P _

theorem TerminalPhiRel_trans (P : Params) (D : ClosureData P)
    {U V W : TerminalState P D} :
    TerminalPhiRel P D U V → TerminalPhiRel P D V W → TerminalPhiRel P D U W := by
  intro hUV hVW
  exact PhiRel_trans P hUV hVW

theorem GatePassPhiRel_trans (P : Params) (D : ClosureData P)
    {U V W : GatePassState P D} :
    GatePassPhiRel P D U V → GatePassPhiRel P D V W → GatePassPhiRel P D U W := by
  intro hUV hVW
  exact PhiRel_trans P hUV hVW

theorem ResidualPhiRel_trans (P : Params) (D : ClosureData P)
    {U V W : ResidualState P D} :
    ResidualPhiRel P D U V → ResidualPhiRel P D V W → ResidualPhiRel P D U W := by
  intro hUV hVW
  exact PhiRel_trans P hUV hVW

theorem TerminalPhiRel_of_support_eq (P : Params) (D : ClosureData P)
    {U V W : TerminalState P D} :
    terminalSupport P D U = terminalSupport P D V →
    (TerminalPhiRel P D U W ↔ TerminalPhiRel P D V W) := by
  intro hUV
  constructor
  · intro h
    rw [TerminalPhiRel_iff] at h ⊢
    rw [terminalPhi_of_support_eq P D hUV] at h
    exact h
  · intro h
    rw [TerminalPhiRel_iff] at h ⊢
    rw [terminalPhi_of_support_eq P D hUV]
    exact h

theorem GatePassPhiRel_of_support_eq (P : Params) (D : ClosureData P)
    {U V W : GatePassState P D} :
    gatePassSupport P D U = gatePassSupport P D V →
    (GatePassPhiRel P D U W ↔ GatePassPhiRel P D V W) := by
  intro hUV
  constructor
  · intro h
    rw [GatePassPhiRel_iff] at h ⊢
    rw [gatePassPhi_of_support_eq P D hUV] at h
    exact h
  · intro h
    rw [GatePassPhiRel_iff] at h ⊢
    rw [gatePassPhi_of_support_eq P D hUV]
    exact h

theorem ResidualPhiRel_of_support_eq (P : Params) (D : ClosureData P)
    {U V W : ResidualState P D} :
    residualSupport P D U = residualSupport P D V →
    (ResidualPhiRel P D U W ↔ ResidualPhiRel P D V W) := by
  intro hUV
  constructor
  · intro h
    rw [ResidualPhiRel_iff] at h ⊢
    rw [residualPhi_of_support_eq P D hUV] at h
    exact h
  · intro h
    rw [ResidualPhiRel_iff] at h ⊢
    rw [residualPhi_of_support_eq P D hUV]
    exact h

theorem terminalPhiRel_wellFounded (P : Params) (D : ClosureData P) :
    WellFounded (TerminalPhiRel P D) := by
  classical
  unfold TerminalPhiRel
  simpa using (measure (terminalPhi P D)).wf

theorem gatePassPhiRel_wellFounded (P : Params) (D : ClosureData P) :
    WellFounded (GatePassPhiRel P D) := by
  classical
  unfold GatePassPhiRel
  simpa using (measure (gatePassPhi P D)).wf

theorem residualPhiRel_wellFounded (P : Params) (D : ClosureData P) :
    WellFounded (ResidualPhiRel P D) := by
  classical
  unfold ResidualPhiRel
  simpa using (measure (residualPhi P D)).wf

def PhiAccessible (P : Params) (U : MachineState P) : Prop :=
  Acc (PhiRel P) U

@[simp] theorem PhiAccessible_def (P : Params) (U : MachineState P) :
    PhiAccessible P U = Acc (PhiRel P) U := rfl

theorem phiAccessible (P : Params) (U : MachineState P) :
    PhiAccessible P U := by
  exact (PhiRel_wellFounded P).apply U

def TerminalPhiAccessible (P : Params) (D : ClosureData P) (U : TerminalState P D) : Prop :=
  Acc (TerminalPhiRel P D) U

def GatePassPhiAccessible (P : Params) (D : ClosureData P) (U : GatePassState P D) : Prop :=
  Acc (GatePassPhiRel P D) U

def ResidualPhiAccessible (P : Params) (D : ClosureData P) (U : ResidualState P D) : Prop :=
  Acc (ResidualPhiRel P D) U

@[simp] theorem TerminalPhiAccessible_def (P : Params) (D : ClosureData P)
    (U : TerminalState P D) :
    TerminalPhiAccessible P D U = Acc (TerminalPhiRel P D) U := rfl

@[simp] theorem GatePassPhiAccessible_def (P : Params) (D : ClosureData P)
    (U : GatePassState P D) :
    GatePassPhiAccessible P D U = Acc (GatePassPhiRel P D) U := rfl

@[simp] theorem ResidualPhiAccessible_def (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualPhiAccessible P D U = Acc (ResidualPhiRel P D) U := rfl

theorem terminalPhiAccessible (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    TerminalPhiAccessible P D U := by
  exact (terminalPhiRel_wellFounded P D).apply U

theorem gatePassPhiAccessible (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    GatePassPhiAccessible P D U := by
  exact (gatePassPhiRel_wellFounded P D).apply U

theorem residualPhiAccessible (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    ResidualPhiAccessible P D U := by
  exact (residualPhiRel_wellFounded P D).apply U

end StateMachine
end CaseC
end Lehmer