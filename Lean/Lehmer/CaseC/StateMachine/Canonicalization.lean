-- FILE: Lean/Lehmer/CaseC/StateMachine/Canonicalization.lean
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
- Lehmer.CaseC.StateMachine.StrictDescent : def thm
- Lehmer.CaseC.StateMachine.NextDis : def thm
- Lehmer.CaseC.StateMachine.NextRem : def thm
- Lehmer.CaseC.StateMachine.ResidualClosure : def thm
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
import Lehmer.CaseC.StateMachine.StrictDescent
import Lehmer.CaseC.StateMachine.NextDis
import Lehmer.CaseC.StateMachine.NextRem
import Lehmer.CaseC.StateMachine.ResidualClosure

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

inductive CanonicalStateView (P : Params) (D : ClosureData P) where
  | terminal (U : TerminalState P D)
  | gatePass (U : GatePassState P D)
  | residual (U : ResidualState P D)

def CanonicalStateView.domainState (P : Params) (D : ClosureData P) :
    CanonicalStateView P D → DomainState P D
  | .terminal U => U.val
  | .gatePass U => U.val
  | .residual U => U.val

@[simp] theorem CanonicalStateView.domainState_terminal
    (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    CanonicalStateView.domainState P D (.terminal U) = U.val := rfl

@[simp] theorem CanonicalStateView.domainState_gatePass
    (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    CanonicalStateView.domainState P D (.gatePass U) = U.val := rfl

@[simp] theorem CanonicalStateView.domainState_residual
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    CanonicalStateView.domainState P D (.residual U) = U.val := rfl

def canonicalSupport (P : Params) (D : ClosureData P) :
    CanonicalStateView P D → Finset ℕ
  | .terminal U => terminalSupport P D U
  | .gatePass U => gatePassSupport P D U
  | .residual U => residualSupport P D U

@[simp] theorem canonicalSupport_terminal
    (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    canonicalSupport P D (.terminal U) = terminalSupport P D U := rfl

@[simp] theorem canonicalSupport_gatePass
    (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    canonicalSupport P D (.gatePass U) = gatePassSupport P D U := rfl

@[simp] theorem canonicalSupport_residual
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    canonicalSupport P D (.residual U) = residualSupport P D U := rfl

def canonicalPhi (P : Params) (D : ClosureData P) :
    CanonicalStateView P D → ℕ
  | .terminal U => terminalPhi P D U
  | .gatePass U => gatePassPhi P D U
  | .residual U => residualPhi P D U

@[simp] theorem canonicalPhi_terminal
    (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    canonicalPhi P D (.terminal U) = terminalPhi P D U := rfl

@[simp] theorem canonicalPhi_gatePass
    (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    canonicalPhi P D (.gatePass U) = gatePassPhi P D U := rfl

@[simp] theorem canonicalPhi_residual
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    canonicalPhi P D (.residual U) = residualPhi P D U := rfl

def canonicalAction (P : Params) (D : ClosureData P) :
    CanonicalStateView P D → MachineAction
  | .terminal U => terminalAction P D U
  | .gatePass U => gatePassAction P D U
  | .residual U => MachineAction.residual (residualFamily P D U)

@[simp] theorem canonicalAction_terminal
    (P : Params) (D : ClosureData P) (U : TerminalState P D) :
    canonicalAction P D (.terminal U) = terminalAction P D U := rfl

@[simp] theorem canonicalAction_gatePass
    (P : Params) (D : ClosureData P) (U : GatePassState P D) :
    canonicalAction P D (.gatePass U) = gatePassAction P D U := rfl

@[simp] theorem canonicalAction_residual
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    canonicalAction P D (.residual U) = MachineAction.residual (residualFamily P D U) := rfl

theorem canonicalView_exhaustive
    (P : Params) (D : ClosureData P) (V : CanonicalStateView P D) :
    (∃ U : TerminalState P D, V = .terminal U) ∨
    (∃ U : GatePassState P D, V = .gatePass U) ∨
    (∃ U : ResidualState P D, V = .residual U) := by
  cases V with
  | terminal U =>
      exact Or.inl ⟨U, rfl⟩
  | gatePass U =>
      exact Or.inr (Or.inl ⟨U, rfl⟩)
  | residual U =>
      exact Or.inr (Or.inr ⟨U, rfl⟩)

theorem canonicalAction_terminal_ne_gatePass
    (P : Params) (D : ClosureData P)
    (U : TerminalState P D) (V : GatePassState P D) :
    canonicalAction P D (.terminal U) ≠ canonicalAction P D (.gatePass V) := by
  simp [canonicalAction]

theorem canonicalAction_terminal_ne_residual
    (P : Params) (D : ClosureData P)
    (U : TerminalState P D) (V : ResidualState P D) :
    canonicalAction P D (.terminal U) ≠ canonicalAction P D (.residual V) := by
  simp [canonicalAction]

theorem canonicalAction_gatePass_ne_residual
    (P : Params) (D : ClosureData P)
    (U : GatePassState P D) (V : ResidualState P D) :
    canonicalAction P D (.gatePass U) ≠ canonicalAction P D (.residual V) := by
  simp [canonicalAction]

inductive CanonicalResidualView (P : Params) (D : ClosureData P) where
  | dis (U : DisResidualState P D)
  | rem (U : RemResidualState P D)

def CanonicalResidualView.state (P : Params) (D : ClosureData P) :
    CanonicalResidualView P D → ResidualState P D
  | .dis U => U.val
  | .rem U => U.val

@[simp] theorem CanonicalResidualView.state_dis
    (P : Params) (D : ClosureData P) (U : DisResidualState P D) :
    CanonicalResidualView.state P D (.dis U) = U.val := rfl

@[simp] theorem CanonicalResidualView.state_rem
    (P : Params) (D : ClosureData P) (U : RemResidualState P D) :
    CanonicalResidualView.state P D (.rem U) = U.val := rfl

def CanonicalResidualView.family (P : Params) (D : ClosureData P) :
    CanonicalResidualView P D → ResidualFamily
  | .dis _ => ResidualFamily.dis
  | .rem _ => ResidualFamily.rem

@[simp] theorem CanonicalResidualView.family_dis
    (P : Params) (D : ClosureData P) (U : DisResidualState P D) :
    CanonicalResidualView.family P D (.dis U) = ResidualFamily.dis := rfl

@[simp] theorem CanonicalResidualView.family_rem
    (P : Params) (D : ClosureData P) (U : RemResidualState P D) :
    CanonicalResidualView.family P D (.rem U) = ResidualFamily.rem := rfl

def canonicalResidualViewOfState (P : Params) (D : ClosureData P)
    (U : ResidualState P D) : CanonicalResidualView P D :=
  match hFam : residualFamily P D U with
  | ResidualFamily.dis =>
      CanonicalResidualView.dis (mkDisResidualState P D U hFam)
  | ResidualFamily.rem =>
      CanonicalResidualView.rem (mkRemResidualState P D U hFam)

theorem canonicalResidualViewOfState_spec
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    (∃ h : IsDisResidual P D U,
        canonicalResidualViewOfState P D U =
          .dis (mkDisResidualState P D U h)) ∨
    (∃ h : IsRemResidual P D U,
        canonicalResidualViewOfState P D U =
          .rem (mkRemResidualState P D U h)) := by
  unfold canonicalResidualViewOfState
  split
  · left
    exact ⟨by assumption, rfl⟩
  · right
    exact ⟨by assumption, rfl⟩

@[simp] theorem canonicalResidualViewOfState_state
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    CanonicalResidualView.state P D (canonicalResidualViewOfState P D U) = U := by
  unfold canonicalResidualViewOfState
  split <;> rfl

@[simp] theorem canonicalResidualViewOfState_family
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    CanonicalResidualView.family P D (canonicalResidualViewOfState P D U) =
      residualFamily P D U := by
  unfold canonicalResidualViewOfState
  split
  · rename_i hDis
    exact hDis.symm
  · rename_i hRem
    exact hRem.symm

theorem canonicalResidualView_closed
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    ResidualClosed P D (CanonicalResidualView.state P D (canonicalResidualViewOfState P D U)) := by
  simpa using residual_closed P D U

theorem canonicalResidualView_exhaustive
    (P : Params) (D : ClosureData P) (V : CanonicalResidualView P D) :
    (∃ U : DisResidualState P D, V = .dis U) ∨
    (∃ U : RemResidualState P D, V = .rem U) := by
  cases V with
  | dis U =>
      exact Or.inl ⟨U, rfl⟩
  | rem U =>
      exact Or.inr ⟨U, rfl⟩

def canonicalResidualPhi (P : Params) (D : ClosureData P)
    (V : CanonicalResidualView P D) : ℕ :=
  residualPhi P D (CanonicalResidualView.state P D V)

@[simp] theorem canonicalResidualPhi_dis
    (P : Params) (D : ClosureData P) (U : DisResidualState P D) :
    canonicalResidualPhi P D (.dis U) = residualPhi P D U.val := rfl

@[simp] theorem canonicalResidualPhi_rem
    (P : Params) (D : ClosureData P) (U : RemResidualState P D) :
    canonicalResidualPhi P D (.rem U) = residualPhi P D U.val := rfl

def canonicalResidualSupport (P : Params) (D : ClosureData P)
    (V : CanonicalResidualView P D) : Finset ℕ :=
  residualSupport P D (CanonicalResidualView.state P D V)

@[simp] theorem canonicalResidualSupport_dis
    (P : Params) (D : ClosureData P) (U : DisResidualState P D) :
    canonicalResidualSupport P D (.dis U) = residualSupport P D U.val := rfl

@[simp] theorem canonicalResidualSupport_rem
    (P : Params) (D : ClosureData P) (U : RemResidualState P D) :
    canonicalResidualSupport P D (.rem U) = residualSupport P D U.val := rfl

def canonicalResidualAction (P : Params) (D : ClosureData P)
    (V : CanonicalResidualView P D) : MachineAction :=
  MachineAction.residual (CanonicalResidualView.family P D V)

@[simp] theorem canonicalResidualAction_dis
    (P : Params) (D : ClosureData P) (U : DisResidualState P D) :
    canonicalResidualAction P D (.dis U) = MachineAction.residual ResidualFamily.dis := rfl

@[simp] theorem canonicalResidualAction_rem
    (P : Params) (D : ClosureData P) (U : RemResidualState P D) :
    canonicalResidualAction P D (.rem U) = MachineAction.residual ResidualFamily.rem := rfl

def canonicalResidualRouting (P : Params) (D : ClosureData P)
    (U : ResidualState P D) : ResidualClosureRouting P D :=
  residualClosureRoutingOfState P D U

@[simp] theorem canonicalResidualRouting_def
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    canonicalResidualRouting P D U = residualClosureRoutingOfState P D U := rfl

structure CanonicalizationPackage (P : Params) (D : ClosureData P) where
  view : CanonicalStateView P D

@[simp] theorem CanonicalizationPackage.view_mk
    (P : Params) (D : ClosureData P) (V : CanonicalStateView P D) :
    (CanonicalizationPackage.mk V).view = V := rfl

def CanonicalizationPackage.domainState (P : Params) (D : ClosureData P)
    (X : CanonicalizationPackage P D) : DomainState P D :=
  CanonicalStateView.domainState P D X.view

@[simp] theorem CanonicalizationPackage.domainState_def
    (P : Params) (D : ClosureData P) (X : CanonicalizationPackage P D) :
    X.domainState = CanonicalStateView.domainState P D X.view := rfl

def CanonicalizationPackage.support (P : Params) (D : ClosureData P)
    (X : CanonicalizationPackage P D) : Finset ℕ :=
  canonicalSupport P D X.view

@[simp] theorem CanonicalizationPackage.support_def
    (P : Params) (D : ClosureData P) (X : CanonicalizationPackage P D) :
    X.support = canonicalSupport P D X.view := rfl

def CanonicalizationPackage.phi (P : Params) (D : ClosureData P)
    (X : CanonicalizationPackage P D) : ℕ :=
  canonicalPhi P D X.view

@[simp] theorem CanonicalizationPackage.phi_def
    (P : Params) (D : ClosureData P) (X : CanonicalizationPackage P D) :
    X.phi = canonicalPhi P D X.view := rfl

def CanonicalizationPackage.action (P : Params) (D : ClosureData P)
    (X : CanonicalizationPackage P D) : MachineAction :=
  canonicalAction P D X.view

@[simp] theorem CanonicalizationPackage.action_def
    (P : Params) (D : ClosureData P) (X : CanonicalizationPackage P D) :
    X.action = canonicalAction P D X.view := rfl

theorem CanonicalizationPackage.exhaustive
    (P : Params) (D : ClosureData P) (X : CanonicalizationPackage P D) :
    (∃ U : TerminalState P D, X.view = .terminal U) ∨
    (∃ U : GatePassState P D, X.view = .gatePass U) ∨
    (∃ U : ResidualState P D, X.view = .residual U) := by
  exact canonicalView_exhaustive P D X.view

theorem CanonicalizationPackage.residual_refines
    (P : Params) (D : ClosureData P) (X : CanonicalizationPackage P D) :
    (∃ U : ResidualState P D,
      X.view = .residual U ∧
      ((∃ V : DisResidualState P D,
          canonicalResidualViewOfState P D U = .dis V) ∨
       (∃ V : RemResidualState P D,
          canonicalResidualViewOfState P D U = .rem V))) ∨
    ¬ (∃ U : ResidualState P D, X.view = .residual U) := by
  cases X.view with
  | terminal U =>
      right
      intro h
      rcases h with ⟨V, hV⟩
      cases hV
  | gatePass U =>
      right
      intro h
      rcases h with ⟨V, hV⟩
      cases hV
  | residual U =>
      left
      refine ⟨U, rfl, ?_⟩
      rcases canonicalResidualViewOfState_spec P D U with hDis | hRem
      · left
        rcases hDis with ⟨h, hh⟩
        exact ⟨mkDisResidualState P D U h, hh⟩
      · right
        rcases hRem with ⟨h, hh⟩
        exact ⟨mkRemResidualState P D U h, hh⟩

end StateMachine
end CaseC
end Lehmer