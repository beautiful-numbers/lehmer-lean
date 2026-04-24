-- FILE: Lean/Lehmer/CaseC/GapClosure/NonIntegrality.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure NonIntegralityWitness (P : Params) (D : ClosureData P) (R : SupportProfile) where
  rigid : RigidProfile P D R
  measure : ℕ
  positive : 0 < measure

@[simp] theorem NonIntegralityWitness.rigid_mk
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (hR : RigidProfile P D R) (m : ℕ) (hm : 0 < m) :
    (NonIntegralityWitness.mk hR m hm).rigid = hR := rfl

@[simp] theorem NonIntegralityWitness.measure_mk
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (hR : RigidProfile P D R) (m : ℕ) (hm : 0 < m) :
    (NonIntegralityWitness.mk hR m hm).measure = m := rfl

@[simp] theorem NonIntegralityWitness.positive_mk
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (hR : RigidProfile P D R) (m : ℕ) (hm : 0 < m) :
    (NonIntegralityWitness.mk hR m hm).positive = hm := rfl

def rigidityMeasure (P : Params) (D : ClosureData P) (R : SupportProfile) : Type :=
  NonIntegralityWitness P D R

def hasNonIntegralityWitness (P : Params) (D : ClosureData P) (R : SupportProfile) : Prop :=
  Nonempty (NonIntegralityWitness P D R)

@[simp] theorem hasNonIntegralityWitness_def
    (P : Params) (D : ClosureData P) (R : SupportProfile) :
    hasNonIntegralityWitness P D R = Nonempty (NonIntegralityWitness P D R) := rfl

def witnessMeasure (P : Params) (D : ClosureData P) (R : SupportProfile)
    (X : NonIntegralityWitness P D R) : ℕ :=
  X.measure

@[simp] theorem witnessMeasure_def
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (X : NonIntegralityWitness P D R) :
    witnessMeasure P D R X = X.measure := rfl

theorem witnessMeasure_pos
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (X : NonIntegralityWitness P D R) :
    0 < witnessMeasure P D R X := by
  exact X.positive

theorem hasNonIntegralityWitness_of_witness
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (X : NonIntegralityWitness P D R) :
    hasNonIntegralityWitness P D R := by
  exact ⟨X⟩

def transportNonIntegralityWitness
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (_h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S)
    (X : NonIntegralityWitness P D R) :
    NonIntegralityWitness P D S :=
  { rigid := hS
    measure := X.measure
    positive := X.positive }

@[simp] theorem transportNonIntegralityWitness_measure
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S)
    (X : NonIntegralityWitness P D R) :
    (transportNonIntegralityWitness P D h hS X).measure = X.measure := rfl

@[simp] theorem transportNonIntegralityWitness_positive
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S)
    (X : NonIntegralityWitness P D R) :
    (transportNonIntegralityWitness P D h hS X).positive = X.positive := rfl

@[simp] theorem transportNonIntegralityWitness_rigid
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S)
    (X : NonIntegralityWitness P D R) :
    (transportNonIntegralityWitness P D h hS X).rigid = hS := rfl

theorem hasNonIntegralityWitness_of_support_eq
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S) :
    hasNonIntegralityWitness P D R →
      hasNonIntegralityWitness P D S := by
  intro hR
  rcases hR with ⟨X⟩
  exact ⟨transportNonIntegralityWitness P D h hS X⟩

def NonIntegralityWitnessFamily (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) : Prop :=
  ∀ R, R ∈ F → hasNonIntegralityWitness P D R

@[simp] theorem NonIntegralityWitnessFamily_def
    (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    NonIntegralityWitnessFamily P D F =
      (∀ R, R ∈ F → hasNonIntegralityWitness P D R) := rfl

theorem nonIntegralityWitnessFamily_nil
    (P : Params) (D : ClosureData P) :
    NonIntegralityWitnessFamily P D [] := by
  intro R hR
  cases hR

theorem nonIntegralityWitnessFamily_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    NonIntegralityWitnessFamily P D (R :: F) ↔
      hasNonIntegralityWitness P D R ∧ NonIntegralityWitnessFamily P D F := by
  constructor
  · intro h
    constructor
    · exact h R (by simp)
    · intro S hS
      exact h S (by simp [hS])
  · intro h
    rcases h with ⟨hR, hF⟩
    intro S hS
    rcases List.mem_cons.1 hS with rfl | hSF
    · exact hR
    · exact hF S hSF

theorem nonIntegralityWitnessFamily_mem
    (P : Params) (D : ClosureData P)
    {F : SupportProfileFamily} :
    NonIntegralityWitnessFamily P D F →
      ∀ R, R ∈ F → hasNonIntegralityWitness P D R := by
  intro h R hR
  exact h R hR

theorem nonIntegralityWitnessFamily_of_pointwise
    (P : Params) (D : ClosureData P)
    {F : SupportProfileFamily} :
    (∀ R, R ∈ F → hasNonIntegralityWitness P D R) →
      NonIntegralityWitnessFamily P D F := by
  intro h
  exact h

structure NonIntegralityPackage (P : Params) (D : ClosureData P) where
  profile : SupportProfile
  witness : NonIntegralityWitness P D profile

@[simp] theorem NonIntegralityPackage.profile_mk
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (X : NonIntegralityWitness P D R) :
    (NonIntegralityPackage.mk R X).profile = R := rfl

@[simp] theorem NonIntegralityPackage.witness_mk
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (X : NonIntegralityWitness P D R) :
    (NonIntegralityPackage.mk R X).witness = X := rfl

def packageRigid
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityPackage P D) : RigidProfile P D X.profile :=
  X.witness.rigid

@[simp] theorem packageRigid_def
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityPackage P D) :
    packageRigid P D X = X.witness.rigid := rfl

def packageMeasure
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityPackage P D) : ℕ :=
  X.witness.measure

@[simp] theorem packageMeasure_def
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityPackage P D) :
    packageMeasure P D X = X.witness.measure := rfl

theorem packageMeasure_pos
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityPackage P D) :
    0 < packageMeasure P D X := by
  exact X.witness.positive

structure NonIntegralityFamilyPackage (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  witnesses : NonIntegralityWitnessFamily P D family

@[simp] theorem NonIntegralityFamilyPackage.family_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : NonIntegralityWitnessFamily P D F) :
    (NonIntegralityFamilyPackage.mk F hF).family = F := rfl

@[simp] theorem NonIntegralityFamilyPackage.witnesses_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : NonIntegralityWitnessFamily P D F) :
    (NonIntegralityFamilyPackage.mk F hF).witnesses = hF := rfl

theorem NonIntegralityFamilyPackage.mem_hasWitness
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityFamilyPackage P D) :
    ∀ R, R ∈ X.family → hasNonIntegralityWitness P D R := by
  intro R hR
  exact X.witnesses R hR

theorem NonIntegralityFamilyPackage.mem_rigid
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityFamilyPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  rcases X.witnesses R hR with ⟨W⟩
  exact W.rigid

theorem NonIntegralityFamilyPackage.mem_measure_pos
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityFamilyPackage P D) :
    ∀ R, R ∈ X.family → ∃ m : ℕ, 0 < m := by
  intro R hR
  rcases X.witnesses R hR with ⟨W⟩
  exact ⟨W.measure, W.positive⟩

end GapClosure
end CaseC
end Lehmer