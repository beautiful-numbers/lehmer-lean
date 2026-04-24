-- FILE: Lean/Lehmer/CaseC/StateMachine/State.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.StateMachine.Actions : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.StateMachine.Actions

namespace Lehmer
namespace CaseC
namespace StateMachine

open Lehmer.Basic

abbrev MachineState (P : Params) := CaseC.State P

def stateSupport (P : Params) (U : MachineState P) : Support :=
  U.support

@[simp] theorem stateSupport_def (P : Params) (U : MachineState P) :
    stateSupport P U = U.support := rfl

def stateCard (P : Params) (U : MachineState P) : ℕ :=
  supportCard (stateSupport P U)

@[simp] theorem stateCard_def (P : Params) (U : MachineState P) :
    stateCard P U = supportCard (stateSupport P U) := rfl

def statePrefix (P : Params) (U : MachineState P) : Prefix :=
  Prefix.mk (stateSupport P U)

@[simp] theorem statePrefix_def (P : Params) (U : MachineState P) :
    statePrefix P U = Prefix.mk (stateSupport P U) := rfl

def stateContains (P : Params) (U : MachineState P) (p : ℕ) : Prop :=
  p ∈ stateSupport P U

@[simp] theorem stateContains_def (P : Params) (U : MachineState P) (p : ℕ) :
    stateContains P U p = (p ∈ stateSupport P U) := rfl

def stateHasPrefix (P : Params) (R : Prefix) (U : MachineState P) : Prop :=
  IsPrefixOf R (stateSupport P U)

@[simp] theorem stateHasPrefix_def (P : Params) (R : Prefix) (U : MachineState P) :
    stateHasPrefix P R U = IsPrefixOf R (stateSupport P U) := rfl

def stateSupportNonempty (P : Params) (U : MachineState P) : Prop :=
  (stateSupport P U).Nonempty

@[simp] theorem stateSupportNonempty_def (P : Params) (U : MachineState P) :
    stateSupportNonempty P U = (stateSupport P U).Nonempty := rfl

def stateSupportEmpty (P : Params) (U : MachineState P) : Prop :=
  stateSupport P U = ∅

@[simp] theorem stateSupportEmpty_def (P : Params) (U : MachineState P) :
    stateSupportEmpty P U = (stateSupport P U = ∅) := rfl

@[simp] theorem stateSupport_mk (P : Params) (S : Support) :
    stateSupport P (CaseC.State.mk S : MachineState P) = S := rfl

@[simp] theorem stateCard_mk (P : Params) (S : Support) :
    stateCard P (CaseC.State.mk S : MachineState P) = supportCard S := rfl

@[simp] theorem statePrefix_mk (P : Params) (S : Support) :
    statePrefix P (CaseC.State.mk S : MachineState P) = Prefix.mk S := rfl

@[simp] theorem stateContains_mk (P : Params) (S : Support) (p : ℕ) :
    stateContains P (CaseC.State.mk S : MachineState P) p = (p ∈ S) := rfl

@[simp] theorem stateHasPrefix_mk (P : Params) (R : Prefix) (S : Support) :
    stateHasPrefix P R (CaseC.State.mk S : MachineState P) = IsPrefixOf R S := rfl

@[simp] theorem stateSupportNonempty_mk (P : Params) (S : Support) :
    stateSupportNonempty P (CaseC.State.mk S : MachineState P) = S.Nonempty := rfl

@[simp] theorem stateSupportEmpty_mk (P : Params) (S : Support) :
    stateSupportEmpty P (CaseC.State.mk S : MachineState P) = (S = ∅) := rfl

theorem state_eq_of_support_eq (P : Params) {U V : MachineState P} :
    stateSupport P U = stateSupport P V → U = V := by
  intro h
  cases U
  cases V
  simp [stateSupport] at h
  cases h
  rfl

@[ext] theorem MachineState.ext (P : Params) {U V : MachineState P}
    (h : stateSupport P U = stateSupport P V) : U = V :=
  state_eq_of_support_eq P h

theorem stateSupport_empty_or_nonempty (P : Params) (U : MachineState P) :
    stateSupportEmpty P U ∨ stateSupportNonempty P U := by
  by_cases h : stateSupport P U = ∅
  · left
    exact h
  · right
    exact Finset.nonempty_iff_ne_empty.mpr h

theorem stateSupportNonempty_iff_not_empty (P : Params) (U : MachineState P) :
    stateSupportNonempty P U ↔ ¬ stateSupportEmpty P U := by
  constructor
  · intro h hEmpty
    have hne : stateSupport P U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h
    exact hne hEmpty
  · intro h
    exact Finset.nonempty_iff_ne_empty.mpr (by
      simpa [stateSupportEmpty] using h)

@[simp] theorem not_stateSupportEmpty_of_nonempty (P : Params) (U : MachineState P) :
    stateSupportNonempty P U → ¬ stateSupportEmpty P U := by
  intro h
  exact (stateSupportNonempty_iff_not_empty P U).mp h

theorem statePrefix_support (P : Params) (U : MachineState P) :
    (statePrefix P U).support = stateSupport P U := rfl

@[simp] theorem stateHasPrefix_self (P : Params) (U : MachineState P) :
    stateHasPrefix P (statePrefix P U) U := by
  simp [stateHasPrefix, statePrefix, IsPrefixOf]

theorem stateContains_of_stateHasPrefix (P : Params) {R : Prefix} {U : MachineState P} {p : ℕ} :
    stateHasPrefix P R U → p ∈ R.support → stateContains P U p := by
  intro hPrefix hp
  exact hPrefix hp

end StateMachine
end CaseC
end Lehmer