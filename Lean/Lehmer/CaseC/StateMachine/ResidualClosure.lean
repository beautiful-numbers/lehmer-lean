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
- Lehmer.CaseC.Certificate.Format : def thm
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
import Lehmer.CaseC.Certificate.Format

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

theorem residual_state_exhaustive
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    IsDisResidual P D U ∨ IsRemResidual P D U := by
  exact residualState_family_exhaustive P D U

inductive ResidualClosureRouting (P : Params) (D : ClosureData P) where
  | dis (U : DisResidualState P D)
  | rem (U : RemResidualState P D)

def residualClosureRoutingOfState
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) : ResidualClosureRouting P D :=
  match hFam : residualFamily P D U with
  | ResidualFamily.dis =>
      ResidualClosureRouting.dis (mkDisResidualState P D U hFam)
  | ResidualFamily.rem =>
      ResidualClosureRouting.rem (mkRemResidualState P D U hFam)

def ResidualClosureRouting.state
    (P : Params) (D : ClosureData P) :
    ResidualClosureRouting P D → ResidualState P D
  | .dis U => U.val
  | .rem U => U.val

@[simp] theorem ResidualClosureRouting.state_dis
    (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    ResidualClosureRouting.state P D (.dis U) = U.val := rfl

@[simp] theorem ResidualClosureRouting.state_rem
    (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    ResidualClosureRouting.state P D (.rem U) = U.val := rfl

def ResidualClosureRouting.family
    (P : Params) (D : ClosureData P) :
    ResidualClosureRouting P D → ResidualFamily
  | .dis _ => ResidualFamily.dis
  | .rem _ => ResidualFamily.rem

@[simp] theorem ResidualClosureRouting.family_dis
    (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    ResidualClosureRouting.family P D (.dis U) = ResidualFamily.dis := rfl

@[simp] theorem ResidualClosureRouting.family_rem
    (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    ResidualClosureRouting.family P D (.rem U) = ResidualFamily.rem := rfl

theorem ResidualClosureRouting.is_dis
    (P : Params) (D : ClosureData P)
    (U : DisResidualState P D) :
    IsDisResidual P D (ResidualClosureRouting.state P D (.dis U)) := by
  simpa using U.isDis

theorem ResidualClosureRouting.is_rem
    (P : Params) (D : ClosureData P)
    (U : RemResidualState P D) :
    IsRemResidual P D (ResidualClosureRouting.state P D (.rem U)) := by
  simpa using U.isRem

theorem ResidualClosureRouting.sound
    (P : Params) (D : ClosureData P)
    (R : ResidualClosureRouting P D) :
    ResidualClosureRouting.state P D R =
      match R with
      | .dis U => U.val
      | .rem U => U.val := by
  cases R <;> rfl

theorem residualClosureRoutingOfState_spec
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    (∃ h : IsDisResidual P D U,
        residualClosureRoutingOfState P D U =
          ResidualClosureRouting.dis (mkDisResidualState P D U h)) ∨
      (∃ h : IsRemResidual P D U,
        residualClosureRoutingOfState P D U =
          ResidualClosureRouting.rem (mkRemResidualState P D U h)) := by
  unfold residualClosureRoutingOfState
  split
  · rename_i h
    left
    exact ⟨h, rfl⟩
  · rename_i h
    right
    exact ⟨h, rfl⟩

@[simp] theorem residualClosureRoutingOfState_state
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualClosureRouting.state P D (residualClosureRoutingOfState P D U) = U := by
  unfold residualClosureRoutingOfState
  split <;> rfl

@[simp] theorem residualClosureRoutingOfState_family
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualClosureRouting.family P D (residualClosureRoutingOfState P D U) =
      residualFamily P D U := by
  unfold residualClosureRoutingOfState
  split
  · rename_i h
    exact h.symm
  · rename_i h
    exact h.symm

def ResidualClosed
    (P : Params) (D : ClosureData P) (U : ResidualState P D) : Prop :=
  ResidualStrictDescentAccessible P D U

@[simp] theorem ResidualClosed_def
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    ResidualClosed P D U = ResidualStrictDescentAccessible P D U := rfl

theorem dis_residual_closed
    (P : Params) (D : ClosureData P) (U : DisResidualState P D) :
    ResidualClosed P D U.val := by
  exact residualStrictDescent_accessible P D U.val

theorem rem_residual_closed
    (P : Params) (D : ClosureData P) (U : RemResidualState P D) :
    ResidualClosed P D U.val := by
  exact residualStrictDescent_accessible P D U.val

theorem residual_closed
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    ResidualClosed P D U := by
  exact residualStrictDescent_accessible P D U

theorem residual_closed_of_routing
    (P : Params) (D : ClosureData P)
    (R : ResidualClosureRouting P D) :
    ResidualClosed P D (ResidualClosureRouting.state P D R) := by
  cases R with
  | dis U =>
      exact dis_residual_closed P D U
  | rem U =>
      exact rem_residual_closed P D U

theorem residual_closed_by_cases
    (P : Params) (D : ClosureData P) (U : ResidualState P D) :
    (IsDisResidual P D U ∧ ResidualClosed P D U) ∨
      (IsRemResidual P D U ∧ ResidualClosed P D U) := by
  rcases residual_state_exhaustive P D U with hDis | hRem
  · left
    exact ⟨hDis, residual_closed P D U⟩
  · right
    exact ⟨hRem, residual_closed P D U⟩

theorem residual_closure_routing_closed
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    ResidualClosed P D
      (ResidualClosureRouting.state P D (residualClosureRoutingOfState P D U)) := by
  simpa using residual_closed P D U

theorem residual_closure_family_dis_or_rem
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    residualFamily P D U = ResidualFamily.dis ∨
      residualFamily P D U = ResidualFamily.rem := by
  rcases residual_state_exhaustive P D U with hDis | hRem
  · left
    exact hDis
  · right
    exact hRem

theorem dis_step_target_closed
    (P : Params) (D : ClosureData P) (s : NextDisStep P D) :
    ResidualClosed P D s.target := by
  exact residual_closed P D s.target

theorem dis_step_source_closed
    (P : Params) (D : ClosureData P) (s : NextDisStep P D) :
    ResidualClosed P D s.source.val := by
  exact residual_closed P D s.source.val

theorem rem_step_target_closed
    (P : Params) (D : ClosureData P) (s : NextRemStep P D) :
    ResidualClosed P D s.target := by
  exact residual_closed P D s.target

theorem rem_step_source_closed
    (P : Params) (D : ClosureData P) (s : NextRemStep P D) :
    ResidualClosed P D s.source.val := by
  exact residual_closed P D s.source.val

theorem dis_step_descends
    (P : Params) (D : ClosureData P) (s : NextDisStep P D) :
    ResidualStrictDescent P D s.target s.source.val := by
  exact s.descent

theorem rem_step_descends
    (P : Params) (D : ClosureData P) (s : NextRemStep P D) :
    ResidualStrictDescent P D s.target s.source.val := by
  exact s.descent

structure ResidualClosurePackage (P : Params) (D : ClosureData P) where
  state : ResidualState P D
  closed : ResidualClosed P D state

@[simp] theorem ResidualClosurePackage.state_mk
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : ResidualClosed P D U) :
    (ResidualClosurePackage.mk U hU).state = U := rfl

@[simp] theorem ResidualClosurePackage.closed_mk
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) (hU : ResidualClosed P D U) :
    (ResidualClosurePackage.mk U hU).closed = hU := rfl

def residualClosurePackageOfState
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) : ResidualClosurePackage P D :=
  ResidualClosurePackage.mk U (residual_closed P D U)

@[simp] theorem residualClosurePackageOfState_state
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    (residualClosurePackageOfState P D U).state = U := rfl

@[simp] theorem residualClosurePackageOfState_closed
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D) :
    (residualClosurePackageOfState P D U).closed =
      residual_closed P D U := rfl

structure ResidualTerminalClosureContext
    (P : Params) (D : ClosureData P) where
  nonIntegralityClosed :
    ∀ S : Support,
      Certificate.PreCaseCAdmissibleSupport P D S →
      Certificate.supportNonIntegral S →
      False
  candNClosed :
    ∀ S : Support,
      Certificate.PreCaseCAdmissibleSupport P D S →
      Certificate.CandNEmpty P D S →
      False
  childClosed :
    ∀ child : Prefix,
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.PrefixCoversSupport child S →
        False

theorem ResidualTerminalClosureContext.close_nonIntegrality
    (P : Params) (D : ClosureData P)
    (Γ : ResidualTerminalClosureContext P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hNon : Certificate.supportNonIntegral S) :
    False := by
  exact Γ.nonIntegralityClosed S hPre hNon

theorem ResidualTerminalClosureContext.close_candN
    (P : Params) (D : ClosureData P)
    (Γ : ResidualTerminalClosureContext P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hEmpty : Certificate.CandNEmpty P D S) :
    False := by
  exact Γ.candNClosed S hPre hEmpty

theorem ResidualTerminalClosureContext.close_child
    (P : Params) (D : ClosureData P)
    (Γ : ResidualTerminalClosureContext P D)
    (child : Prefix)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hCov : Certificate.PrefixCoversSupport child S) :
    False := by
  exact Γ.childClosed child S hPre hCov

theorem residualTerminalContext_nonIntegrality_closed
    (P : Params) (D : ClosureData P)
    (Γ : ResidualTerminalClosureContext P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hNon : Certificate.supportNonIntegral S) :
    False := by
  exact Γ.nonIntegralityClosed S hPre hNon

theorem residualTerminalContext_candN_closed
    (P : Params) (D : ClosureData P)
    (Γ : ResidualTerminalClosureContext P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hEmpty : Certificate.CandNEmpty P D S) :
    False := by
  exact Γ.candNClosed S hPre hEmpty

theorem residualTerminalContext_child_closed
    (P : Params) (D : ClosureData P)
    (Γ : ResidualTerminalClosureContext P D)
    (child : Prefix)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hCov : Certificate.PrefixCoversSupport child S) :
    False := by
  exact Γ.childClosed child S hPre hCov

def mkResidualTerminalClosureContext
    (P : Params) (D : ClosureData P)
    (hNon :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.supportNonIntegral S →
        False)
    (hCandN :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.CandNEmpty P D S →
        False)
    (hChild :
      ∀ child : Prefix,
        ∀ S : Support,
          Certificate.PreCaseCAdmissibleSupport P D S →
          Certificate.PrefixCoversSupport child S →
          False) :
    ResidualTerminalClosureContext P D :=
  { nonIntegralityClosed := hNon
    candNClosed := hCandN
    childClosed := hChild }

@[simp] theorem mkResidualTerminalClosureContext_nonIntegralityClosed
    (P : Params) (D : ClosureData P)
    (hNon :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.supportNonIntegral S →
        False)
    (hCandN :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.CandNEmpty P D S →
        False)
    (hChild :
      ∀ child : Prefix,
        ∀ S : Support,
          Certificate.PreCaseCAdmissibleSupport P D S →
          Certificate.PrefixCoversSupport child S →
          False) :
    (mkResidualTerminalClosureContext P D hNon hCandN hChild).nonIntegralityClosed =
      hNon := rfl

@[simp] theorem mkResidualTerminalClosureContext_candNClosed
    (P : Params) (D : ClosureData P)
    (hNon :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.supportNonIntegral S →
        False)
    (hCandN :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.CandNEmpty P D S →
        False)
    (hChild :
      ∀ child : Prefix,
        ∀ S : Support,
          Certificate.PreCaseCAdmissibleSupport P D S →
          Certificate.PrefixCoversSupport child S →
          False) :
    (mkResidualTerminalClosureContext P D hNon hCandN hChild).candNClosed =
      hCandN := rfl

@[simp] theorem mkResidualTerminalClosureContext_childClosed
    (P : Params) (D : ClosureData P)
    (hNon :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.supportNonIntegral S →
        False)
    (hCandN :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.CandNEmpty P D S →
        False)
    (hChild :
      ∀ child : Prefix,
        ∀ S : Support,
          Certificate.PreCaseCAdmissibleSupport P D S →
          Certificate.PrefixCoversSupport child S →
          False) :
    (mkResidualTerminalClosureContext P D hNon hCandN hChild).childClosed =
      hChild := rfl

structure ResidualClosureTerminalPackage
    (P : Params) (D : ClosureData P) where
  residual : ResidualClosurePackage P D
  terminalContext : ResidualTerminalClosureContext P D

@[simp] theorem ResidualClosureTerminalPackage.residual_mk
    (P : Params) (D : ClosureData P)
    (R : ResidualClosurePackage P D)
    (Γ : ResidualTerminalClosureContext P D) :
    (ResidualClosureTerminalPackage.mk R Γ).residual = R := rfl

@[simp] theorem ResidualClosureTerminalPackage.terminalContext_mk
    (P : Params) (D : ClosureData P)
    (R : ResidualClosurePackage P D)
    (Γ : ResidualTerminalClosureContext P D) :
    (ResidualClosureTerminalPackage.mk R Γ).terminalContext = Γ := rfl

theorem ResidualClosureTerminalPackage.residual_closed
    (P : Params) (D : ClosureData P)
    (X : ResidualClosureTerminalPackage P D) :
    ResidualClosed P D X.residual.state := by
  exact X.residual.closed

theorem ResidualClosureTerminalPackage.nonIntegrality_closed
    (P : Params) (D : ClosureData P)
    (X : ResidualClosureTerminalPackage P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hNon : Certificate.supportNonIntegral S) :
    False := by
  exact X.terminalContext.nonIntegralityClosed S hPre hNon

theorem ResidualClosureTerminalPackage.candN_closed
    (P : Params) (D : ClosureData P)
    (X : ResidualClosureTerminalPackage P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hEmpty : Certificate.CandNEmpty P D S) :
    False := by
  exact X.terminalContext.candNClosed S hPre hEmpty

theorem ResidualClosureTerminalPackage.child_closed
    (P : Params) (D : ClosureData P)
    (X : ResidualClosureTerminalPackage P D)
    (child : Prefix)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hCov : Certificate.PrefixCoversSupport child S) :
    False := by
  exact X.terminalContext.childClosed child S hPre hCov

def residualClosureTerminalPackageOfState
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D)
    (Γ : ResidualTerminalClosureContext P D) :
    ResidualClosureTerminalPackage P D :=
  { residual := residualClosurePackageOfState P D U
    terminalContext := Γ }

@[simp] theorem residualClosureTerminalPackageOfState_residual
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D)
    (Γ : ResidualTerminalClosureContext P D) :
    (residualClosureTerminalPackageOfState P D U Γ).residual =
      residualClosurePackageOfState P D U := rfl

@[simp] theorem residualClosureTerminalPackageOfState_terminalContext
    (P : Params) (D : ClosureData P)
    (U : ResidualState P D)
    (Γ : ResidualTerminalClosureContext P D) :
    (residualClosureTerminalPackageOfState P D U Γ).terminalContext = Γ := rfl

end StateMachine
end CaseC
end Lehmer