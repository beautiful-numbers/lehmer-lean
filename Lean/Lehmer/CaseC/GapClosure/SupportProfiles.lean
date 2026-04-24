-- FILE: Lean/Lehmer/CaseC/GapClosure/SupportProfiles.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure SupportProfile where
  support : Support

@[simp] theorem SupportProfile.support_mk (S : Support) :
    (SupportProfile.mk S).support = S := rfl

def profileSupport (R : SupportProfile) : Support :=
  R.support

@[simp] theorem profileSupport_def (R : SupportProfile) :
    profileSupport R = R.support := rfl

def profileCard (R : SupportProfile) : ℕ :=
  supportCard (profileSupport R)

def profileWidth (R : SupportProfile) : ℕ :=
  profileCard R

@[simp] theorem profileCard_def (R : SupportProfile) :
    profileCard R = supportCard (profileSupport R) := rfl

@[simp] theorem profileWidth_def (R : SupportProfile) :
    profileWidth R = profileCard R := rfl

@[simp] theorem profileSupport_mk (S : Support) :
    profileSupport (SupportProfile.mk S) = S := rfl

@[simp] theorem profileCard_mk (S : Support) :
    profileCard (SupportProfile.mk S) = supportCard S := rfl

@[simp] theorem profileWidth_mk (S : Support) :
    profileWidth (SupportProfile.mk S) = supportCard S := rfl

def profileContains (R : SupportProfile) (p : ℕ) : Prop :=
  p ∈ profileSupport R

@[simp] theorem profileContains_def (R : SupportProfile) (p : ℕ) :
    profileContains R p = (p ∈ profileSupport R) := rfl

def profileNonempty (R : SupportProfile) : Prop :=
  (profileSupport R).Nonempty

@[simp] theorem profileNonempty_def (R : SupportProfile) :
    profileNonempty R = (profileSupport R).Nonempty := rfl

def profileEmpty (R : SupportProfile) : Prop :=
  profileSupport R = ∅

@[simp] theorem profileEmpty_def (R : SupportProfile) :
    profileEmpty R = (profileSupport R = ∅) := rfl

def ProfileBelow (N : ℕ) (R : SupportProfile) : Prop :=
  SupportBelow N (profileSupport R)

def ProfileWithinOmega (omega : ℕ) (R : SupportProfile) : Prop :=
  SupportWithinOmega omega (profileSupport R)

@[simp] theorem ProfileBelow_def (N : ℕ) (R : SupportProfile) :
    ProfileBelow N R = SupportBelow N (profileSupport R) := rfl

@[simp] theorem ProfileWithinOmega_def (omega : ℕ) (R : SupportProfile) :
    ProfileWithinOmega omega R = SupportWithinOmega omega (profileSupport R) := rfl

def ProfileInTruncatedFamily (P : Params) (D : ClosureData P) (R : SupportProfile) : Prop :=
  ProfileBelow D.N R ∧ ProfileWithinOmega D.omegaHat R

@[simp] theorem ProfileInTruncatedFamily_def (P : Params) (D : ClosureData P) (R : SupportProfile) :
    ProfileInTruncatedFamily P D R = (ProfileBelow D.N R ∧ ProfileWithinOmega D.omegaHat R) := rfl

theorem profileInTruncatedFamily_iff (P : Params) (D : ClosureData P) (R : SupportProfile) :
    ProfileInTruncatedFamily P D R ↔
      SupportBelow D.N (profileSupport R) ∧
      SupportWithinOmega D.omegaHat (profileSupport R) := by
  rfl

@[simp] theorem ProfileBelow_mk (N : ℕ) (S : Support) :
    ProfileBelow N (SupportProfile.mk S) = SupportBelow N S := rfl

@[simp] theorem ProfileWithinOmega_mk (omega : ℕ) (S : Support) :
    ProfileWithinOmega omega (SupportProfile.mk S) = SupportWithinOmega omega S := rfl

@[simp] theorem ProfileInTruncatedFamily_mk (P : Params) (D : ClosureData P) (S : Support) :
    ProfileInTruncatedFamily P D (SupportProfile.mk S) ↔
      SupportBelow D.N S ∧ SupportWithinOmega D.omegaHat S := by
  rfl

theorem profile_eq_of_support_eq {R T : SupportProfile} :
    profileSupport R = profileSupport T → R = T := by
  intro h
  cases R
  cases T
  simp [profileSupport] at h
  cases h
  rfl

@[ext] theorem SupportProfile.ext {R T : SupportProfile}
    (h : profileSupport R = profileSupport T) : R = T :=
  profile_eq_of_support_eq h

theorem profileEmpty_or_nonempty (R : SupportProfile) :
    profileEmpty R ∨ profileNonempty R := by
  by_cases h : profileSupport R = ∅
  · left
    exact h
  · right
    exact Finset.nonempty_iff_ne_empty.mpr h

theorem profileNonempty_iff_not_empty (R : SupportProfile) :
    profileNonempty R ↔ ¬ profileEmpty R := by
  constructor
  · intro h hEmpty
    have hne : profileSupport R ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h
    exact hne hEmpty
  · intro h
    exact Finset.nonempty_iff_ne_empty.mpr (by
      simpa [profileEmpty] using h)

theorem profileInTruncatedFamily_of_support_eq (P : Params) (D : ClosureData P)
    {R T : SupportProfile} :
    profileSupport R = profileSupport T →
    ProfileInTruncatedFamily P D R →
    ProfileInTruncatedFamily P D T := by
  intro hRT hR
  have hEq : R = T := profile_eq_of_support_eq hRT
  simpa [hEq] using hR

theorem profileInTruncatedFamily_iff_of_support_eq (P : Params) (D : ClosureData P)
    {R T : SupportProfile} :
    profileSupport R = profileSupport T →
    (ProfileInTruncatedFamily P D R ↔ ProfileInTruncatedFamily P D T) := by
  intro hRT
  constructor
  · intro hR
    exact profileInTruncatedFamily_of_support_eq P D hRT hR
  · intro hT
    exact profileInTruncatedFamily_of_support_eq P D hRT.symm hT

abbrev SupportProfileFamily := List SupportProfile

def familySupports (F : SupportProfileFamily) : List Support :=
  F.map profileSupport

@[simp] theorem familySupports_nil :
    familySupports [] = [] := rfl

@[simp] theorem familySupports_cons (R : SupportProfile) (F : SupportProfileFamily) :
    familySupports (R :: F) = profileSupport R :: familySupports F := rfl

def profileInFamily (R : SupportProfile) (F : SupportProfileFamily) : Prop :=
  R ∈ F

@[simp] theorem profileInFamily_def (R : SupportProfile) (F : SupportProfileFamily) :
    profileInFamily R F = (R ∈ F) := rfl

theorem supportProfileFamily_exhaustive (F : SupportProfileFamily) :
    F = [] ∨ ∃ R G, F = R :: G := by
  cases F with
  | nil =>
      left
      rfl
  | cons R G =>
      right
      exact ⟨R, G, rfl⟩

def familyHead? (F : SupportProfileFamily) : Option SupportProfile :=
  F.head?

@[simp] theorem familyHead?_nil :
    familyHead? [] = none := rfl

@[simp] theorem familyHead?_cons (R : SupportProfile) (F : SupportProfileFamily) :
    familyHead? (R :: F) = some R := rfl

def FamilyAllInTruncatedFamily (P : Params) (D : ClosureData P) (F : SupportProfileFamily) : Prop :=
  ∀ R ∈ F, ProfileInTruncatedFamily P D R

@[simp] theorem FamilyAllInTruncatedFamily_def (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    FamilyAllInTruncatedFamily P D F = (∀ R ∈ F, ProfileInTruncatedFamily P D R) := rfl

@[simp] theorem FamilyAllInTruncatedFamily_nil (P : Params) (D : ClosureData P) :
    FamilyAllInTruncatedFamily P D [] := by
  intro R h
  simp at h

theorem FamilyAllInTruncatedFamily_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    FamilyAllInTruncatedFamily P D (R :: F) ↔
      ProfileInTruncatedFamily P D R ∧ FamilyAllInTruncatedFamily P D F := by
  constructor
  · intro h
    constructor
    · exact h R (by simp)
    · intro T hT
      exact h T (by simp [hT])
  · intro h
    rcases h with ⟨hR, hF⟩
    intro T hT
    simp at hT
    rcases hT with rfl | hT
    · exact hR
    · exact hF T hT

end GapClosure
end CaseC
end Lehmer