-- FILE: Lean/Lehmer/CaseC/StateMachine/StrictDescent.lean
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
- Lehmer.CaseC.StateMachine.WellFounded : def thm
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
import Lehmer.CaseC.StateMachine.WellFounded

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

def StrictDescent (P : Params) (U V : MachineState P) : Prop :=
  PhiRel P U V

@[simp] theorem StrictDescent_def (P : Params) (U V : MachineState P) :
    StrictDescent P U V = PhiRel P U V := rfl

theorem strictDescent_iff (P : Params) (U V : MachineState P) :
    StrictDescent P U V ↔ phi P U < phi P V := by
  rfl

def ResidualStrictDescent (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) : Prop :=
  ResidualPhiRel P D U V

@[simp] theorem ResidualStrictDescent_def (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) :
    ResidualStrictDescent P D U V = ResidualPhiRel P D U V := rfl

theorem residualStrictDescent_iff (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) :
    ResidualStrictDescent P D U V ↔ residualPhi P D U < residualPhi P D V := by
  rfl

theorem not_StrictDescent_self (P : Params) (U : MachineState P) :
    ¬ StrictDescent P U U := by
  exact not_PhiRel_self P U

theorem not_ResidualStrictDescent_self (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ¬ ResidualStrictDescent P D U U := by
  exact not_ResidualPhiRel_self P D U

theorem StrictDescent_trans (P : Params) {U V W : MachineState P} :
    StrictDescent P U V → StrictDescent P V W → StrictDescent P U W := by
  intro hUV hVW
  exact PhiRel_trans P hUV hVW

theorem ResidualStrictDescent_trans (P : Params) (D : ClosureData P)
    {U V W : ResidualState P D} :
    ResidualStrictDescent P D U V →
    ResidualStrictDescent P D V W →
    ResidualStrictDescent P D U W := by
  intro hUV hVW
  exact ResidualPhiRel_trans P D hUV hVW

theorem strictDescent_wellFounded (P : Params) :
    WellFounded (StrictDescent P) := by
  simpa [StrictDescent] using (PhiRel_wellFounded P)

theorem residualStrictDescent_wellFounded (P : Params) (D : ClosureData P) :
    WellFounded (ResidualStrictDescent P D) := by
  simpa [ResidualStrictDescent] using (residualPhiRel_wellFounded P D)

theorem strictDescent_of_support_eq (P : Params) {U V W : MachineState P} :
    stateSupport P U = stateSupport P V →
    (StrictDescent P U W ↔ StrictDescent P V W) := by
  intro hUV
  simpa [StrictDescent] using (PhiRel_of_support_eq P hUV)

theorem strictDescent_to_support_eq (P : Params) {U V W : MachineState P} :
    stateSupport P V = stateSupport P W →
    (StrictDescent P U V ↔ StrictDescent P U W) := by
  intro hVW
  simpa [StrictDescent] using (PhiRel_to_support_eq P hVW)

theorem residualStrictDescent_of_support_eq (P : Params) (D : ClosureData P)
    {U V W : ResidualState P D} :
    residualSupport P D U = residualSupport P D V →
    (ResidualStrictDescent P D U W ↔ ResidualStrictDescent P D V W) := by
  intro hUV
  simpa [ResidualStrictDescent] using (ResidualPhiRel_of_support_eq P D hUV)

def StrictDescentAccessible (P : Params) (U : MachineState P) : Prop :=
  Acc (StrictDescent P) U

@[simp] theorem StrictDescentAccessible_def (P : Params) (U : MachineState P) :
    StrictDescentAccessible P U = Acc (StrictDescent P) U := rfl

theorem strictDescent_accessible (P : Params) (U : MachineState P) :
    StrictDescentAccessible P U := by
  exact (strictDescent_wellFounded P).apply U

def ResidualStrictDescentAccessible (P : Params) (D : ClosureData P)
    (U : ResidualState P D) : Prop :=
  Acc (ResidualStrictDescent P D) U

@[simp] theorem ResidualStrictDescentAccessible_def (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualStrictDescentAccessible P D U = Acc (ResidualStrictDescent P D) U := rfl

theorem residualStrictDescent_accessible (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualStrictDescentAccessible P D U := by
  exact (residualStrictDescent_wellFounded P D).apply U

theorem residualStrictDescent_eq_phiRel (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) :
    ResidualStrictDescent P D U V ↔
      StrictDescent P (residualState P D U) (residualState P D V) := by
  rfl

theorem residualStrictDescent_eq_phi (P : Params) (D : ClosureData P)
    (U V : ResidualState P D) :
    ResidualStrictDescent P D U V ↔
      phi P (residualState P D U) < phi P (residualState P D V) := by
  rfl

end StateMachine
end CaseC
end Lehmer