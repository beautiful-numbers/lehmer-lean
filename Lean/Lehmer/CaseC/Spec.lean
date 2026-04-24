-- FILE: Lean/Lehmer/CaseC/Spec.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs

namespace Lehmer
namespace CaseC

open Lehmer.Basic

structure Params where
  y : ℕ
  W : ℕ

abbrev level (P : Params) : ℕ :=
  P.y

abbrev width (P : Params) : ℕ :=
  P.W

@[simp] theorem level_mk (y W : ℕ) :
    level ⟨y, W⟩ = y := rfl

@[simp] theorem width_mk (y W : ℕ) :
    width ⟨y, W⟩ = W := rfl

structure ClosureData (P : Params) where
  N : ℕ
  omegaHat : ℕ

abbrev cap (P : Params) (D : ClosureData P) : ℕ :=
  D.N

abbrev omegaBound (P : Params) (D : ClosureData P) : ℕ :=
  D.omegaHat

@[simp] theorem cap_mk (P : Params) (N omegaHat : ℕ) :
    cap P ({ N := N, omegaHat := omegaHat } : ClosureData P) = N := rfl

@[simp] theorem omegaBound_mk (P : Params) (N omegaHat : ℕ) :
    omegaBound P ({ N := N, omegaHat := omegaHat } : ClosureData P) = omegaHat := rfl

abbrev Support := Finset ℕ

def supportCard (S : Support) : ℕ :=
  S.card

@[simp] theorem supportCard_def (S : Support) :
    supportCard S = S.card := rfl

def SupportBelow (N : ℕ) (S : Support) : Prop :=
  ∀ p ∈ S, p ≤ N

def SupportWithinOmega (omega : ℕ) (S : Support) : Prop :=
  supportCard S ≤ omega

@[simp] theorem SupportBelow_def (N : ℕ) (S : Support) :
    SupportBelow N S = (∀ p ∈ S, p ≤ N) := rfl

@[simp] theorem SupportWithinOmega_def (omega : ℕ) (S : Support) :
    SupportWithinOmega omega S = (supportCard S ≤ omega) := rfl

def InTruncatedDomain (P : Params) (D : ClosureData P) (S : Support) : Prop :=
  SupportBelow D.N S ∧ SupportWithinOmega D.omegaHat S

@[simp] theorem InTruncatedDomain_def (P : Params) (D : ClosureData P) (S : Support) :
    InTruncatedDomain P D S = (SupportBelow D.N S ∧ SupportWithinOmega D.omegaHat S) := rfl

structure State (P : Params) where
  support : Support

@[simp] theorem State.support_mk (P : Params) (S : Support) :
    (State.mk S : State P).support = S := rfl

def stateCard (P : Params) (U : State P) : ℕ :=
  supportCard U.support

@[simp] theorem stateCard_def (P : Params) (U : State P) :
    stateCard P U = supportCard U.support := rfl

def StateInTruncatedDomain (P : Params) (D : ClosureData P) (U : State P) : Prop :=
  InTruncatedDomain P D U.support

@[simp] theorem StateInTruncatedDomain_def (P : Params) (D : ClosureData P) (U : State P) :
    StateInTruncatedDomain P D U = InTruncatedDomain P D U.support := rfl

inductive Status where
  | terminal
  | gatePass
  | residual
deriving DecidableEq

@[simp] theorem Status.terminal_ne_gatePass :
    Status.terminal ≠ Status.gatePass := by
  decide

@[simp] theorem Status.terminal_ne_residual :
    Status.terminal ≠ Status.residual := by
  decide

@[simp] theorem Status.gatePass_ne_terminal :
    Status.gatePass ≠ Status.terminal := by
  decide

@[simp] theorem Status.gatePass_ne_residual :
    Status.gatePass ≠ Status.residual := by
  decide

@[simp] theorem Status.residual_ne_terminal :
    Status.residual ≠ Status.terminal := by
  decide

@[simp] theorem Status.residual_ne_gatePass :
    Status.residual ≠ Status.gatePass := by
  decide

inductive ResidualFamily where
  | dis
  | rem
deriving DecidableEq

@[simp] theorem ResidualFamily.dis_ne_rem :
    ResidualFamily.dis ≠ ResidualFamily.rem := by
  decide

@[simp] theorem ResidualFamily.rem_ne_dis :
    ResidualFamily.rem ≠ ResidualFamily.dis := by
  decide

def IsTerminal (s : Status) : Prop :=
  s = Status.terminal

def IsGatePass (s : Status) : Prop :=
  s = Status.gatePass

def IsResidual (s : Status) : Prop :=
  s = Status.residual

@[simp] theorem IsTerminal_def (s : Status) :
    IsTerminal s = (s = Status.terminal) := rfl

@[simp] theorem IsGatePass_def (s : Status) :
    IsGatePass s = (s = Status.gatePass) := rfl

@[simp] theorem IsResidual_def (s : Status) :
    IsResidual s = (s = Status.residual) := rfl

def ResidualSet (P : Params) (D : ClosureData P) : Set (State P) :=
  { U | StateInTruncatedDomain P D U }

@[simp] theorem mem_ResidualSet (P : Params) (D : ClosureData P) (U : State P) :
    U ∈ ResidualSet P D ↔ StateInTruncatedDomain P D U := Iff.rfl

def HasResidualFamily (f : ResidualFamily) (g : ResidualFamily) : Prop :=
  f = g

@[simp] theorem HasResidualFamily_def (f g : ResidualFamily) :
    HasResidualFamily f g = (f = g) := rfl

structure Prefix where
  support : Support

@[simp] theorem Prefix.support_mk (S : Support) :
    (Prefix.mk S).support = S := rfl

def prefixCard (R : Prefix) : ℕ :=
  supportCard R.support

@[simp] theorem prefixCard_def (R : Prefix) :
    prefixCard R = supportCard R.support := rfl

def IsPrefixOf (R : Prefix) (U : Support) : Prop :=
  R.support ⊆ U

@[simp] theorem IsPrefixOf_def (R : Prefix) (U : Support) :
    IsPrefixOf R U = (R.support ⊆ U) := rfl

def Cylinder (R : Prefix) : Set Support :=
  { U | IsPrefixOf R U }

@[simp] theorem mem_Cylinder (R : Prefix) (U : Support) :
    U ∈ Cylinder R ↔ IsPrefixOf R U := Iff.rfl

end CaseC
end Lehmer