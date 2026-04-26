-- FILE: Lean/Lehmer/CaseC/GapClosure/NonIntegrality.lean

/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.Certificate.Format : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.Certificate.Format

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def SupportIndexIntegral (S : Support) : Prop :=
  ∃ z : ℤ, Certificate.supportIndex S = (z : ℚ)

@[simp] theorem SupportIndexIntegral_def (S : Support) :
    SupportIndexIntegral S =
      (∃ z : ℤ, Certificate.supportIndex S = (z : ℚ)) := rfl

theorem supportNonIntegral_contradicts_integral
    (S : Support) :
    SupportIndexIntegral S →
    Certificate.supportNonIntegral S →
    False := by
  intro hInt hNon
  rcases hInt with ⟨z, hz⟩
  exact hNon z hz

structure CaseCIndexIntegralityData
    (P : Params) (D : ClosureData P) where
  integral :
    ∀ S : Support,
      Certificate.CaseCAdmissibleSupport P D S →
      SupportIndexIntegral S

theorem caseCAdmissible_supportIndexIntegral
    (P : Params) (D : ClosureData P)
    (I : CaseCIndexIntegralityData P D)
    (S : Support)
    (hAdm : Certificate.CaseCAdmissibleSupport P D S) :
    SupportIndexIntegral S := by
  exact I.integral S hAdm

theorem caseCAdmissible_nonIntegral_contradiction
    (P : Params) (D : ClosureData P)
    (I : CaseCIndexIntegralityData P D)
    (S : Support)
    (hAdm : Certificate.CaseCAdmissibleSupport P D S)
    (hNon : Certificate.supportNonIntegral S) :
    False := by
  exact supportNonIntegral_contradicts_integral S
    (I.integral S hAdm) hNon

structure NonIntegralityWitness
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) where
  rigid : RigidProfile P D R
  nonIntegral :
    Certificate.supportNonIntegral (profileSupport R)

@[simp] theorem NonIntegralityWitness.rigid_mk
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (hR : RigidProfile P D R)
    (hN : Certificate.supportNonIntegral (profileSupport R)) :
    (NonIntegralityWitness.mk hR hN).rigid = hR := rfl

@[simp] theorem NonIntegralityWitness.nonIntegral_mk
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (hR : RigidProfile P D R)
    (hN : Certificate.supportNonIntegral (profileSupport R)) :
    (NonIntegralityWitness.mk hR hN).nonIntegral = hN := rfl

def hasNonIntegralityWitness
    (P : Params) (D : ClosureData P) (R : SupportProfile) : Prop :=
  Nonempty (NonIntegralityWitness P D R)

@[simp] theorem hasNonIntegralityWitness_def
    (P : Params) (D : ClosureData P) (R : SupportProfile) :
    hasNonIntegralityWitness P D R =
      Nonempty (NonIntegralityWitness P D R) := rfl

theorem hasNonIntegralityWitness_of_witness
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (X : NonIntegralityWitness P D R) :
    hasNonIntegralityWitness P D R := by
  exact ⟨X⟩

def NonIntegralityWitness.profile_rigid
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (W : NonIntegralityWitness P D R) :
    RigidProfile P D R :=
  W.rigid

theorem NonIntegralityWitness.profile_nonIntegral
    (P : Params) (D : ClosureData P) (R : SupportProfile)
    (W : NonIntegralityWitness P D R) :
    Certificate.supportNonIntegral (profileSupport R) := by
  exact W.nonIntegral

theorem nonIntegralityWitness_closes_profile
    (P : Params) (D : ClosureData P)
    (I : CaseCIndexIntegralityData P D)
    (R : SupportProfile)
    (W : NonIntegralityWitness P D R)
    (hAdm : Certificate.CaseCAdmissibleSupport P D (profileSupport R)) :
    False := by
  -- TYPO CORRIGÉ ICI : "contradiction" au lieu de "contradicts"
  exact caseCAdmissible_nonIntegral_contradiction
    P D I (profileSupport R) hAdm W.nonIntegral

theorem hasNonIntegralityWitness_closes_profile
    (P : Params) (D : ClosureData P)
    (I : CaseCIndexIntegralityData P D)
    (R : SupportProfile)
    (hW : hasNonIntegralityWitness P D R)
    (hAdm : Certificate.CaseCAdmissibleSupport P D (profileSupport R)) :
    False := by
  rcases hW with ⟨W⟩
  exact nonIntegralityWitness_closes_profile P D I R W hAdm

def transportNonIntegralityWitness
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S)
    (X : NonIntegralityWitness P D R) :
    NonIntegralityWitness P D S := by
  cases profile_eq_of_support_eq h
  exact {
    rigid := hS
    nonIntegral := X.nonIntegral
  }

@[simp] theorem transportNonIntegralityWitness_rigid
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S)
    (X : NonIntegralityWitness P D R) :
    (transportNonIntegralityWitness P D h hS X).rigid = hS := by
  cases profile_eq_of_support_eq h
  rfl

@[simp] theorem transportNonIntegralityWitness_nonIntegral
    (P : Params) (D : ClosureData P)
    {R S : SupportProfile}
    (h : profileSupport R = profileSupport S)
    (hS : RigidProfile P D S)
    (X : NonIntegralityWitness P D R) :
    (transportNonIntegralityWitness P D h hS X).nonIntegral =
      (by
        cases profile_eq_of_support_eq h
        exact X.nonIntegral) := by
  cases profile_eq_of_support_eq h
  rfl

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

def NonIntegralityWitnessFamily
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) : Type :=
  ∀ R, R ∈ F → NonIntegralityWitness P D R

@[simp] theorem NonIntegralityWitnessFamily_def
    (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    NonIntegralityWitnessFamily P D F =
      (∀ R, R ∈ F → NonIntegralityWitness P D R) := rfl

def nonIntegralityWitnessFamily_nil
    (P : Params) (D : ClosureData P) :
    NonIntegralityWitnessFamily P D [] := by
  intro R hR
  contradiction -- Plus propre et robuste pour éliminer False

def nonIntegralityWitnessFamily_head
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    NonIntegralityWitnessFamily P D (R :: F) →
      NonIntegralityWitness P D R := by
  intro h
  exact h R (by simp)

def nonIntegralityWitnessFamily_tail
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    NonIntegralityWitnessFamily P D (R :: F) →
      NonIntegralityWitnessFamily P D F := by
  intro h S hS
  exact h S (by simp [hS])

noncomputable def nonIntegralityWitnessFamily_cons_intro
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    NonIntegralityWitness P D R →
    NonIntegralityWitnessFamily P D F →
    NonIntegralityWitnessFamily P D (R :: F) := by
  intro hR hF S hS
  by_cases hEq : S = R
  · cases hEq
    exact hR
  · have hSF : S ∈ F := by
      have hMem : S = R ∨ S ∈ F := List.mem_cons.1 hS
      exact Or.resolve_left hMem hEq
    exact hF S hSF

theorem nonIntegralityWitnessFamily_mem
    (P : Params) (D : ClosureData P)
    {F : SupportProfileFamily} :
    NonIntegralityWitnessFamily P D F →
      ∀ R, R ∈ F → hasNonIntegralityWitness P D R := by
  intro h R hR
  exact ⟨h R hR⟩

noncomputable def nonIntegralityWitnessFamily_of_pointwise
    (P : Params) (D : ClosureData P)
    {F : SupportProfileFamily} :
    (∀ R, R ∈ F → hasNonIntegralityWitness P D R) →
      NonIntegralityWitnessFamily P D F := by
  intro h R hR
  exact Classical.choice (h R hR)

structure NonIntegralityPackage
    (P : Params) (D : ClosureData P) where
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

def NonIntegralityPackage.profile_rigid
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityPackage P D) :
    RigidProfile P D X.profile :=
  X.witness.rigid

theorem NonIntegralityPackage.profile_nonIntegral
    (P : Params) (D : ClosureData P)
    (X : NonIntegralityPackage P D) :
    Certificate.supportNonIntegral (profileSupport X.profile) := by
  exact X.witness.nonIntegral

theorem NonIntegralityPackage.closes
    (P : Params) (D : ClosureData P)
    (I : CaseCIndexIntegralityData P D)
    (X : NonIntegralityPackage P D)
    (hAdm : Certificate.CaseCAdmissibleSupport P D (profileSupport X.profile)) :
    False := by
  exact nonIntegralityWitness_closes_profile P D I X.profile X.witness hAdm

structure NonIntegralityFamilyPackage
    (P : Params) (D : ClosureData P) where
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
  exact ⟨X.witnesses R hR⟩

end GapClosure
end CaseC
end Lehmer