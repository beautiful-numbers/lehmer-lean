-- FILE: Lean/Lehmer/CaseC/StateMachine/Domain.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.StateMachine.Actions : def thm
- Lehmer.CaseC.StateMachine.State : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.StateMachine.Actions
import Lehmer.CaseC.StateMachine.State

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

def InDomain (P : Params) (D : ClosureData P) (U : MachineState P) : Prop :=
  StateInTruncatedDomain P D U

@[simp] theorem InDomain_def (P : Params) (D : ClosureData P) (U : MachineState P) :
    InDomain P D U = StateInTruncatedDomain P D U := rfl

def DomainSupportBelow (P : Params) (D : ClosureData P) (U : MachineState P) : Prop :=
  SupportBelow D.N (stateSupport P U)

def DomainSupportWithinOmega (P : Params) (D : ClosureData P) (U : MachineState P) : Prop :=
  SupportWithinOmega D.omegaHat (stateSupport P U)

@[simp] theorem DomainSupportBelow_def (P : Params) (D : ClosureData P) (U : MachineState P) :
    DomainSupportBelow P D U = SupportBelow D.N (stateSupport P U) := rfl

@[simp] theorem DomainSupportWithinOmega_def (P : Params) (D : ClosureData P) (U : MachineState P) :
    DomainSupportWithinOmega P D U = SupportWithinOmega D.omegaHat (stateSupport P U) := rfl

theorem inDomain_iff (P : Params) (D : ClosureData P) (U : MachineState P) :
    InDomain P D U ↔ DomainSupportBelow P D U ∧ DomainSupportWithinOmega P D U := by
  unfold InDomain DomainSupportBelow DomainSupportWithinOmega
  simp [StateInTruncatedDomain, InTruncatedDomain]

theorem inDomain_support_iff (P : Params) (D : ClosureData P) (U : MachineState P) :
    InDomain P D U ↔
      SupportBelow D.N (stateSupport P U) ∧ SupportWithinOmega D.omegaHat (stateSupport P U) := by
  exact inDomain_iff P D U

theorem inDomain_below_cap (P : Params) (D : ClosureData P) (U : MachineState P) :
    InDomain P D U → SupportBelow D.N (stateSupport P U) := by
  intro h
  exact (inDomain_iff P D U).mp h |>.1

theorem inDomain_within_omega (P : Params) (D : ClosureData P) (U : MachineState P) :
    InDomain P D U → SupportWithinOmega D.omegaHat (stateSupport P U) := by
  intro h
  exact (inDomain_iff P D U).mp h |>.2

theorem inDomain_intro (P : Params) (D : ClosureData P) (U : MachineState P) :
    SupportBelow D.N (stateSupport P U) →
    SupportWithinOmega D.omegaHat (stateSupport P U) →
    InDomain P D U := by
  intro hBelow hOmega
  exact (inDomain_iff P D U).mpr ⟨hBelow, hOmega⟩

@[simp] theorem inDomain_mk (P : Params) (D : ClosureData P) (S : Support) :
    InDomain P D (CaseC.State.mk S : MachineState P) ↔
      SupportBelow D.N S ∧ SupportWithinOmega D.omegaHat S := by
  exact inDomain_iff P D (CaseC.State.mk S)

@[simp] theorem inDomain_mk_def (P : Params) (D : ClosureData P) (S : Support) :
    InDomain P D (CaseC.State.mk S : MachineState P) =
      (SupportBelow D.N S ∧ SupportWithinOmega D.omegaHat S) := by
  apply propext
  exact inDomain_mk P D S

theorem inDomain_of_support_eq (P : Params) (D : ClosureData P) {U V : MachineState P} :
    stateSupport P U = stateSupport P V →
    InDomain P D U →
    InDomain P D V := by
  intro hUV hU
  have hEq : U = V := state_eq_of_support_eq P hUV
  simpa [hEq] using hU

theorem inDomain_iff_of_support_eq (P : Params) (D : ClosureData P) {U V : MachineState P} :
    stateSupport P U = stateSupport P V →
    (InDomain P D U ↔ InDomain P D V) := by
  intro hUV
  constructor
  · intro hU
    exact inDomain_of_support_eq P D hUV hU
  · intro hV
    exact inDomain_of_support_eq P D hUV.symm hV

theorem domainSupportBelow_mono_of_inDomain (P : Params) (D : ClosureData P) (U : MachineState P) :
    InDomain P D U → DomainSupportBelow P D U := by
  intro h
  exact inDomain_below_cap P D U h

theorem domainSupportWithinOmega_mono_of_inDomain (P : Params) (D : ClosureData P) (U : MachineState P) :
    InDomain P D U → DomainSupportWithinOmega P D U := by
  intro h
  exact inDomain_within_omega P D U h

structure DomainState (P : Params) (D : ClosureData P) where
  val : MachineState P
  property : InDomain P D val

@[simp] theorem DomainState.val_mk (P : Params) (D : ClosureData P)
    (U : MachineState P) (h : InDomain P D U) :
    (DomainState.mk U h).val = U := rfl

@[simp] theorem DomainState.property_mk (P : Params) (D : ClosureData P)
    (U : MachineState P) (h : InDomain P D U) :
    (DomainState.mk U h).property = h := rfl

def domainStateSupport (P : Params) (D : ClosureData P) (U : DomainState P D) : Support :=
  stateSupport P U.val

@[simp] theorem domainStateSupport_def (P : Params) (D : ClosureData P) (U : DomainState P D) :
    domainStateSupport P D U = stateSupport P U.val := rfl

def domainStateCard (P : Params) (D : ClosureData P) (U : DomainState P D) : ℕ :=
  stateCard P U.val

@[simp] theorem domainStateCard_def (P : Params) (D : ClosureData P) (U : DomainState P D) :
    domainStateCard P D U = stateCard P U.val := rfl

theorem domainState_inDomain (P : Params) (D : ClosureData P) (U : DomainState P D) :
    InDomain P D U.val := U.property

theorem domainState_support_below (P : Params) (D : ClosureData P) (U : DomainState P D) :
    SupportBelow D.N (domainStateSupport P D U) := by
  exact inDomain_below_cap P D U.val U.property

theorem domainState_support_within_omega (P : Params) (D : ClosureData P) (U : DomainState P D) :
    SupportWithinOmega D.omegaHat (domainStateSupport P D U) := by
  exact inDomain_within_omega P D U.val U.property

end StateMachine
end CaseC
end Lehmer