-- FILE: Lean/Lehmer/CaseC/GapClosure/SupportProfiles.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Candidate : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Candidate
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic
open Lehmer.Pipeline

structure SupportProfile where
  support : Support

@[simp] theorem SupportProfile.support_mk (S : Support) :
    (SupportProfile.mk S).support = S := rfl

def profileSupport (R : SupportProfile) : Support :=
  R.support

@[simp] theorem profileSupport_def (R : SupportProfile) :
    profileSupport R = R.support := rfl

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

def candidateProfile (n : ℕ) : SupportProfile :=
  SupportProfile.mk (candidateSupport n)

@[simp] theorem candidateProfile_support
    (n : ℕ) :
    profileSupport (candidateProfile n) = candidateSupport n := rfl

@[simp] theorem candidateProfile_card
    (n : ℕ) :
    profileCard (candidateProfile n) = supportCard (candidateSupport n) := rfl

@[simp] theorem candidateProfile_width
    (n : ℕ) :
    profileWidth (candidateProfile n) = supportCard (candidateSupport n) := rfl

def CandidateHasProfile
    (n : ℕ) (R : SupportProfile) : Prop :=
  profileSupport R = candidateSupport n

@[simp] theorem CandidateHasProfile_def
    (n : ℕ) (R : SupportProfile) :
    CandidateHasProfile n R =
      (profileSupport R = candidateSupport n) := rfl

theorem candidate_has_candidateProfile
    (n : ℕ) :
    CandidateHasProfile n (candidateProfile n) := by
  rfl

theorem candidateHasProfile_support_eq
    {n : ℕ} {R : SupportProfile}
    (h : CandidateHasProfile n R) :
    profileSupport R = candidateSupport n := h

theorem candidateHasProfile_eq_candidateProfile
    {n : ℕ} {R : SupportProfile}
    (h : CandidateHasProfile n R) :
    R = candidateProfile n := by
  apply profile_eq_of_support_eq
  exact h

theorem candidateProfile_unique
    {n : ℕ} {R T : SupportProfile}
    (hR : CandidateHasProfile n R)
    (hT : CandidateHasProfile n T) :
    R = T := by
  apply profile_eq_of_support_eq
  exact hR.trans hT.symm

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

def CandidateProfileInTruncatedFamily
    (P : Params) (D : ClosureData P) (n : ℕ) : Prop :=
  ProfileInTruncatedFamily P D (candidateProfile n)

@[simp] theorem CandidateProfileInTruncatedFamily_def
    (P : Params) (D : ClosureData P) (n : ℕ) :
    CandidateProfileInTruncatedFamily P D n =
      ProfileInTruncatedFamily P D (candidateProfile n) := rfl

theorem candidateProfile_inTruncatedFamily_of_candidateInTruncatedDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileInTruncatedFamily P D (candidateProfile n) := by
  exact ⟨hDom.1, hDom.2⟩

theorem candidateProfile_below_of_candidateInTruncatedDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileBelow D.N (candidateProfile n) := by
  exact hDom.1

theorem candidateProfile_withinOmega_of_candidateInTruncatedDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileWithinOmega D.omegaHat (candidateProfile n) := by
  exact hDom.2

theorem candidateHasProfile_inTruncatedFamily_of_candidateDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ} {R : SupportProfile}
    (hProf : CandidateHasProfile n R)
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileInTruncatedFamily P D R := by
  have hCp : ProfileInTruncatedFamily P D (candidateProfile n) :=
    candidateProfile_inTruncatedFamily_of_candidateInTruncatedDomain P D hDom
  have hEq : profileSupport (candidateProfile n) = profileSupport R := by
    simpa [candidateProfile] using hProf.symm
  exact profileInTruncatedFamily_of_support_eq P D hEq hCp

theorem candidateHasProfile_below_of_candidateDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ} {R : SupportProfile}
    (hProf : CandidateHasProfile n R)
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileBelow D.N R := by
  have h : ProfileInTruncatedFamily P D R :=
    candidateHasProfile_inTruncatedFamily_of_candidateDomain P D hProf hDom
  exact h.1

theorem candidateHasProfile_withinOmega_of_candidateDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ} {R : SupportProfile}
    (hProf : CandidateHasProfile n R)
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileWithinOmega D.omegaHat R := by
  have h : ProfileInTruncatedFamily P D R :=
    candidateHasProfile_inTruncatedFamily_of_candidateDomain P D hProf hDom
  exact h.2

theorem profileInTruncatedFamily_support
    (P : Params) (D : ClosureData P)
    {R : SupportProfile}
    (h : ProfileInTruncatedFamily P D R) :
    InTruncatedDomain P D (profileSupport R) := by
  simpa [InTruncatedDomain, ProfileInTruncatedFamily, ProfileBelow, ProfileWithinOmega] using h

theorem support_inTruncatedDomain_of_profile
    (P : Params) (D : ClosureData P)
    {R : SupportProfile}
    (h : ProfileInTruncatedFamily P D R) :
    SupportBelow D.N (profileSupport R) ∧
      SupportWithinOmega D.omegaHat (profileSupport R) := by
  simpa [ProfileInTruncatedFamily, ProfileBelow, ProfileWithinOmega] using h

theorem candidateSupport_inTruncatedDomain_of_profile
    (P : Params) (D : ClosureData P)
    {n : ℕ} {R : SupportProfile}
    (hProf : CandidateHasProfile n R)
    (hR : ProfileInTruncatedFamily P D R) :
    InTruncatedDomain P D (candidateSupport n) := by
  rw [← hProf]
  exact profileInTruncatedFamily_support P D hR

theorem candidateInTruncatedDomain_of_candidateProfile
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hR : ProfileInTruncatedFamily P D (candidateProfile n)) :
    CandidateInTruncatedDomain P D n := by
  simpa [CandidateInTruncatedDomain, candidateProfile, ProfileInTruncatedFamily,
    ProfileBelow, ProfileWithinOmega] using hR

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

def FamilyCoversProfile
    (F : SupportProfileFamily) (R : SupportProfile) : Prop :=
  R ∈ F

@[simp] theorem FamilyCoversProfile_def
    (F : SupportProfileFamily) (R : SupportProfile) :
    FamilyCoversProfile F R = (R ∈ F) := rfl

def FamilyCoversCandidate
    (F : SupportProfileFamily) (n : ℕ) : Prop :=
  ∃ R : SupportProfile,
    R ∈ F ∧ CandidateHasProfile n R

@[simp] theorem FamilyCoversCandidate_def
    (F : SupportProfileFamily) (n : ℕ) :
    FamilyCoversCandidate F n =
      (∃ R : SupportProfile,
        R ∈ F ∧ CandidateHasProfile n R) := rfl

theorem familyCoversCandidate_of_mem_candidateProfile
    (F : SupportProfileFamily) (n : ℕ)
    (h : candidateProfile n ∈ F) :
    FamilyCoversCandidate F n := by
  exact ⟨candidateProfile n, h, candidate_has_candidateProfile n⟩

theorem candidateProfile_mem_of_familyCoversCandidate
    {F : SupportProfileFamily} {n : ℕ}
    (h : FamilyCoversCandidate F n) :
    candidateProfile n ∈ F := by
  rcases h with ⟨R, hR, hProf⟩
  have hEq : R = candidateProfile n :=
    candidateHasProfile_eq_candidateProfile hProf
  simpa [hEq] using hR

theorem familyCoversCandidate_iff_candidateProfile_mem
    (F : SupportProfileFamily) (n : ℕ) :
    FamilyCoversCandidate F n ↔ candidateProfile n ∈ F := by
  constructor
  · intro h
    exact candidateProfile_mem_of_familyCoversCandidate h
  · intro h
    exact familyCoversCandidate_of_mem_candidateProfile F n h

theorem familyCoversCandidate_in_truncated
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : FamilyAllInTruncatedFamily P D F)
    {n : ℕ}
    (hCover : FamilyCoversCandidate F n) :
    CandidateProfileInTruncatedFamily P D n := by
  have hMem : candidateProfile n ∈ F :=
    candidateProfile_mem_of_familyCoversCandidate hCover
  exact hF (candidateProfile n) hMem

theorem familyCoversCandidate_candidateDomain
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : FamilyAllInTruncatedFamily P D F)
    {n : ℕ}
    (hCover : FamilyCoversCandidate F n) :
    CandidateInTruncatedDomain P D n := by
  exact candidateInTruncatedDomain_of_candidateProfile
    P D (familyCoversCandidate_in_truncated P D F hF hCover)

theorem FamilyAllInTruncatedFamily.mem
    (P : Params) (D : ClosureData P)
    {F : SupportProfileFamily} {R : SupportProfile}
    (hF : FamilyAllInTruncatedFamily P D F)
    (hR : R ∈ F) :
    ProfileInTruncatedFamily P D R := by
  exact hF R hR

theorem FamilyAllInTruncatedFamily.candidate
    (P : Params) (D : ClosureData P)
    {F : SupportProfileFamily} {n : ℕ}
    (hF : FamilyAllInTruncatedFamily P D F)
    (hCover : FamilyCoversCandidate F n) :
    ProfileInTruncatedFamily P D (candidateProfile n) := by
  exact familyCoversCandidate_in_truncated P D F hF hCover

theorem familyCoversCandidate_cons
    (R : SupportProfile) (F : SupportProfileFamily) (n : ℕ) :
    FamilyCoversCandidate (R :: F) n ↔
      CandidateHasProfile n R ∨ FamilyCoversCandidate F n := by
  constructor
  · intro h
    rcases h with ⟨T, hT, hProf⟩
    simp at hT
    rcases hT with rfl | hTF
    · exact Or.inl hProf
    · exact Or.inr ⟨T, hTF, hProf⟩
  · intro h
    rcases h with hR | hF
    · exact ⟨R, by simp, hR⟩
    · rcases hF with ⟨T, hTF, hProf⟩
      exact ⟨T, by simp [hTF], hProf⟩

@[simp] theorem familyCoversCandidate_nil
    (n : ℕ) :
    ¬ FamilyCoversCandidate [] n := by
  intro h
  rcases h with ⟨R, hR, _⟩
  simp at hR

theorem candidate_profile_ready_of_caseC_domain
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (_hL : LehmerComposite n)
    (_hC : InCaseC n)
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileInTruncatedFamily P D (candidateProfile n) := by
  exact candidateProfile_inTruncatedFamily_of_candidateInTruncatedDomain P D hDom

theorem candidate_has_profile_ready_of_caseC_domain
    (P : Params) (D : ClosureData P)
    {n : ℕ} {R : SupportProfile}
    (_hL : LehmerComposite n)
    (_hC : InCaseC n)
    (hProf : CandidateHasProfile n R)
    (hDom : CandidateInTruncatedDomain P D n) :
    ProfileInTruncatedFamily P D R := by
  exact candidateHasProfile_inTruncatedFamily_of_candidateDomain P D hProf hDom

end GapClosure
end CaseC
end Lehmer