-- FILE: Lean/Lehmer/CaseC/GapClosure/TruncatedFamily.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Candidate : def thm
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
- Lehmer.CaseC.GapClosure.Omegahat : def thm
- Lehmer.CaseC.Certificate.Format : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.DeltaStar
import Lehmer.CaseC.GapClosure.Omegahat
import Lehmer.CaseC.Certificate.Format

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def FamilySoundForCaseC
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) : Prop :=
  ∀ R : SupportProfile,
    R ∈ F →
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)

@[simp] theorem FamilySoundForCaseC_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    FamilySoundForCaseC P D F =
      (∀ R : SupportProfile,
        R ∈ F →
        Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)) := rfl

def FamilyCoversAdmissibleSupport
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) : Prop :=
  ∀ S : Support,
    Certificate.PreCaseCAdmissibleSupport P D S →
    SupportProfile.mk S ∈ F

@[simp] theorem FamilyCoversAdmissibleSupport_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    FamilyCoversAdmissibleSupport P D F =
      (∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        SupportProfile.mk S ∈ F) := rfl

def FamilyCoversPreAdmissibleSupport
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) : Prop :=
  FamilyCoversAdmissibleSupport P D F

@[simp] theorem FamilyCoversPreAdmissibleSupport_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    FamilyCoversPreAdmissibleSupport P D F =
      FamilyCoversAdmissibleSupport P D F := rfl

def IsTruncatedFamily
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) : Prop :=
  FamilySoundForCaseC P D F ∧
    FamilyCoversAdmissibleSupport P D F

@[simp] theorem IsTruncatedFamily_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    IsTruncatedFamily P D F =
      (FamilySoundForCaseC P D F ∧
        FamilyCoversAdmissibleSupport P D F) := rfl

theorem isTruncatedFamily_iff_old_plus_cover
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    IsTruncatedFamily P D F ↔
      FamilySoundForCaseC P D F ∧
        FamilyCoversAdmissibleSupport P D F := by
  rfl

theorem isTruncatedFamily_sound
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    IsTruncatedFamily P D F →
      FamilySoundForCaseC P D F := by
  intro h
  exact h.1

theorem isTruncatedFamily_covers
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    IsTruncatedFamily P D F →
      FamilyCoversAdmissibleSupport P D F := by
  intro h
  exact h.2

theorem isTruncatedFamily_mem_preAdmissible
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F)
    (R : SupportProfile)
    (hR : R ∈ F) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact hF.1 R hR

theorem isTruncatedFamily_mem_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F)
    (R : SupportProfile)
    (hR : R ∈ F) :
    Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_admissible
    P D (profileSupport R)
    (isTruncatedFamily_mem_preAdmissible P D F hF R hR)

theorem isTruncatedFamily_mem_preLocksC
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F)
    (R : SupportProfile)
    (hR : R ∈ F) :
    Certificate.PreLocksC P D (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_preLocksC
    P D (profileSupport R)
    (isTruncatedFamily_mem_preAdmissible P D F hF R hR)

theorem isTruncatedFamily_mem_locksB
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F)
    (R : SupportProfile)
    (hR : R ∈ F) :
    Certificate.LocksB (level P) (profileSupport R) := by
  exact Certificate.preLocksC_to_locksB
    P D (profileSupport R)
    (isTruncatedFamily_mem_preLocksC P D F hF R hR)

theorem isTruncatedFamily_mem
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F)
    (R : SupportProfile)
    (hR : R ∈ F) :
    ProfileInTruncatedFamily P D R := by
  exact (profileInTruncatedFamily_iff P D R).mpr
    (Certificate.preCaseCAdmissible_inTruncatedDomain
      P D (profileSupport R)
      (isTruncatedFamily_mem_preAdmissible P D F hF R hR))

theorem isTruncatedFamily_covers_support
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S) :
    SupportProfile.mk S ∈ F := by
  exact hF.2 S hPre

theorem isTruncatedFamily_covers_profile
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F)
    (R : SupportProfile)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)) :
    R ∈ F := by
  have hMem : SupportProfile.mk (profileSupport R) ∈ F :=
    isTruncatedFamily_covers_support P D F hF (profileSupport R) hPre
  have hEq : SupportProfile.mk (profileSupport R) = R := by
    apply profile_eq_of_support_eq
    rfl
  rw [hEq] at hMem
  exact hMem

theorem isTruncatedFamily_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    IsTruncatedFamily P D F →
      FamilyAllInTruncatedFamily P D F := by
  intro hF R hR
  exact isTruncatedFamily_mem P D F hF R hR

theorem isTruncatedFamily_nil_of_no_admissible
    (P : Params) (D : ClosureData P)
    (hEmpty :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S → False) :
    IsTruncatedFamily P D [] := by
  constructor
  · intro R hR
    simp at hR
  · intro S hPre
    exact False.elim (hEmpty S hPre)

theorem familySoundForCaseC_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    FamilySoundForCaseC P D (R :: F) ↔
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) ∧
        FamilySoundForCaseC P D F := by
  constructor
  · intro h
    constructor
    · exact h R (by simp)
    · intro T hT
      exact h T (by simp [hT])
  · intro h
    rcases h with ⟨hR, hF⟩
    intro T hT
    rcases List.mem_cons.mp hT with hEq | hTail
    · subst hEq
      exact hR
    · exact hF T hTail

theorem familySoundForCaseC_tail
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    FamilySoundForCaseC P D (R :: F) →
      FamilySoundForCaseC P D F := by
  intro h
  exact (familySoundForCaseC_cons P D R F).mp h |>.2

theorem familySoundForCaseC_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    FamilySoundForCaseC P D F →
      FamilyAllInTruncatedFamily P D F := by
  intro hF R hR
  exact (profileInTruncatedFamily_iff P D R).mpr
    (Certificate.preCaseCAdmissible_inTruncatedDomain
      P D (profileSupport R) (hF R hR))

structure TruncatedFamily (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  truncated : IsTruncatedFamily P D family

@[simp] theorem TruncatedFamily.family_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F) :
    (TruncatedFamily.mk F hF).family = F := rfl

@[simp] theorem TruncatedFamily.truncated_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D F) :
    (TruncatedFamily.mk F hF).truncated = hF := rfl

def truncatedFamilyProfiles
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem truncatedFamilyProfiles_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    truncatedFamilyProfiles P D X = X.family := rfl

def truncatedFamilyHead?
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    Option SupportProfile :=
  familyHead? X.family

@[simp] theorem truncatedFamilyHead?_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    truncatedFamilyHead? P D X = familyHead? X.family := rfl

def truncatedFamilyMember
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (X : TruncatedFamily P D) : Prop :=
  R ∈ X.family

@[simp] theorem truncatedFamilyMember_def
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (X : TruncatedFamily P D) :
    truncatedFamilyMember P D R X = (R ∈ X.family) := rfl

theorem TruncatedFamily.mem_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    ∀ R, R ∈ X.family →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact isTruncatedFamily_mem_preAdmissible P D X.family X.truncated R hR

theorem TruncatedFamily.mem_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    ∀ R, R ∈ X.family →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact isTruncatedFamily_mem_admissibleAtLevel P D X.family X.truncated R hR

theorem TruncatedFamily.mem_locksB
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    ∀ R, R ∈ X.family →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact isTruncatedFamily_mem_locksB P D X.family X.truncated R hR

theorem TruncatedFamily.mem_truncated
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    ∀ R, R ∈ X.family → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact isTruncatedFamily_mem P D X.family X.truncated R hR

theorem TruncatedFamily.covers_support
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S) :
    SupportProfile.mk S ∈ X.family := by
  exact isTruncatedFamily_covers_support P D X.family X.truncated S hPre

theorem TruncatedFamily.covers_profile
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D)
    (R : SupportProfile)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)) :
    R ∈ X.family := by
  exact isTruncatedFamily_covers_profile P D X.family X.truncated R hPre

theorem TruncatedFamily.allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    FamilyAllInTruncatedFamily P D X.family := by
  exact isTruncatedFamily_allInTruncatedFamily P D X.family X.truncated

theorem truncatedFamily_member_truncated
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    ∀ R, truncatedFamilyMember P D R X → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact TruncatedFamily.mem_truncated P D X R hR

theorem truncatedFamily_nil_or_cons
    (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact supportProfileFamily_exhaustive X.family

@[simp] theorem truncatedFamilyHead?_nil
    (P : Params) (D : ClosureData P)
    (hF : IsTruncatedFamily P D []) :
    truncatedFamilyHead? P D (TruncatedFamily.mk [] hF) = none := rfl

@[simp] theorem truncatedFamilyHead?_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    truncatedFamilyHead? P D (TruncatedFamily.mk (R :: F) hF) = some R := rfl

theorem truncatedFamily_head_preAdmissible
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact isTruncatedFamily_mem_preAdmissible P D (R :: F) hF R (by simp)

theorem truncatedFamily_head_truncated
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    ProfileInTruncatedFamily P D R := by
  exact isTruncatedFamily_mem P D (R :: F) hF R (by simp)

theorem truncatedFamily_tail_soundForCaseC
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    FamilySoundForCaseC P D F := by
  exact familySoundForCaseC_tail P D R F hF.1

theorem truncatedFamily_tail_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    FamilyAllInTruncatedFamily P D F := by
  exact familySoundForCaseC_allInTruncatedFamily P D F
    (truncatedFamily_tail_soundForCaseC P D R F hF)

structure TruncatedGapPackage (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  truncated : IsTruncatedFamily P D family
  rigid : RigidProfileFamily P D family
  delta : DeltaStarData P D family rigid
  kmax : KmaxData P D family rigid
  omegaHat : OmegahatData P D family rigid delta kmax

@[simp] theorem TruncatedGapPackage.family_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hR)
    (K : KmaxData P D F hR)
    (ω : OmegahatData P D F hR δ K) :
    (TruncatedGapPackage.mk F hT hR δ K ω).family = F := rfl

@[simp] theorem TruncatedGapPackage.truncated_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hR)
    (K : KmaxData P D F hR)
    (ω : OmegahatData P D F hR δ K) :
    (TruncatedGapPackage.mk F hT hR δ K ω).truncated = hT := rfl

@[simp] theorem TruncatedGapPackage.rigid_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hR)
    (K : KmaxData P D F hR)
    (ω : OmegahatData P D F hR δ K) :
    (TruncatedGapPackage.mk F hT hR δ K ω).rigid = hR := rfl

@[simp] theorem TruncatedGapPackage.delta_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hR)
    (K : KmaxData P D F hR)
    (ω : OmegahatData P D F hR δ K) :
    (TruncatedGapPackage.mk F hT hR δ K ω).delta = δ := rfl

@[simp] theorem TruncatedGapPackage.kmax_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hR)
    (K : KmaxData P D F hR)
    (ω : OmegahatData P D F hR δ K) :
    (TruncatedGapPackage.mk F hT hR δ K ω).kmax = K := rfl

@[simp] theorem TruncatedGapPackage.omegaHat_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hR)
    (K : KmaxData P D F hR)
    (ω : OmegahatData P D F hR δ K) :
    (TruncatedGapPackage.mk F hT hR δ K ω).omegaHat = ω := rfl

def truncatedGapFamily
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem truncatedGapFamily_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapFamily P D X = X.family := rfl

def truncatedGapHead?
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    Option SupportProfile :=
  familyHead? X.family

@[simp] theorem truncatedGapHead?_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapHead? P D X = familyHead? X.family := rfl

def truncatedGapDeltaValue
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : ℚ :=
  deltaStarValue P D X.family X.rigid X.delta

@[simp] theorem truncatedGapDeltaValue_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapDeltaValue P D X =
      deltaStarValue P D X.family X.rigid X.delta := rfl

def truncatedGapKmaxValue
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : ℚ :=
  kmaxValue P D X.family X.rigid X.kmax

@[simp] theorem truncatedGapKmaxValue_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapKmaxValue P D X =
      kmaxValue P D X.family X.rigid X.kmax := rfl

def truncatedGapOmegahatValue
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : ℕ :=
  omegahatValue P D X.family X.rigid X.delta X.kmax X.omegaHat

@[simp] theorem truncatedGapOmegahatValue_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapOmegahatValue P D X =
      omegahatValue P D X.family X.rigid X.delta X.kmax X.omegaHat := rfl

def truncatedGapOmegahatBelowWidth
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : Prop :=
  OmegahatBelowWidth P D X.family X.rigid X.delta X.kmax X.omegaHat

@[simp] theorem truncatedGapOmegahatBelowWidth_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapOmegahatBelowWidth P D X =
      OmegahatBelowWidth P D X.family X.rigid X.delta X.kmax X.omegaHat := rfl

def truncatedGapOmegahatMatchesClosureData
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : Prop :=
  OmegahatMatchesClosureData P D X.family X.rigid X.delta X.kmax X.omegaHat

@[simp] theorem truncatedGapOmegahatMatchesClosureData_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapOmegahatMatchesClosureData P D X =
      OmegahatMatchesClosureData P D X.family X.rigid X.delta X.kmax X.omegaHat := rfl

theorem truncatedGapPackage_member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    ∀ R, R ∈ X.family →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact isTruncatedFamily_mem_preAdmissible P D X.family X.truncated R hR

theorem truncatedGapPackage_member_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    ∀ R, R ∈ X.family →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact isTruncatedFamily_mem_admissibleAtLevel P D X.family X.truncated R hR

theorem truncatedGapPackage_member_locksB
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    ∀ R, R ∈ X.family →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact RigidProfile.locksB P D R (X.rigid R hR)

theorem truncatedGapPackage_member_truncated
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    ∀ R, R ∈ X.family →
      ProfileInTruncatedFamily P D R := by
  intro R hR
  exact isTruncatedFamily_mem P D X.family X.truncated R hR

def truncatedGapPackage_member_rigid
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact X.rigid R hR

theorem truncatedGapPackage_covers_support
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S) :
    SupportProfile.mk S ∈ X.family := by
  exact isTruncatedFamily_covers_support P D X.family X.truncated S hPre

theorem truncatedGapPackage_covers_profile
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (R : SupportProfile)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)) :
    R ∈ X.family := by
  exact isTruncatedFamily_covers_profile P D X.family X.truncated R hPre

theorem truncatedGapDeltaPositive
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    0 < truncatedGapDeltaValue P D X := by
  exact deltaStar_positive P D X.family X.rigid X.delta

theorem truncatedGapDelta_le_member_gap
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family) :
    truncatedGapDeltaValue P D X ≤
      profileRigidityGapValue P D R (X.rigid R hR) := by
  exact deltaStar_le_profile_gap P D X.family X.rigid X.delta R hR

theorem truncatedGapKmaxPositive
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    0 < truncatedGapKmaxValue P D X := by
  exact kmax_positive P D X.family X.rigid X.kmax

theorem truncatedGapMember_index_le_kmax
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family) :
    profileSupportIndex R ≤ truncatedGapKmaxValue P D X := by
  exact profileIndex_le_kmax P D X.family X.rigid X.kmax R hR

theorem truncatedGapOmegahatBelowWidth_value
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (hω : truncatedGapOmegahatBelowWidth P D X) :
    truncatedGapOmegahatValue P D X < width P := by
  exact hω

theorem truncatedGapOmegahatMatchesClosureData_value
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X) :
    D.omegaHat = truncatedGapOmegahatValue P D X := by
  exact hMatch

theorem truncatedGapPackage_member_withinClosureOmega
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X) :
    SupportWithinOmega D.omegaHat (profileSupport R) := by
  exact supportWithinClosureOmega_of_mem
    P D X.family X.rigid X.delta X.kmax X.omegaHat hMatch R hR

theorem truncatedGapPackage_member_card_lt_width
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family)
    (hω : truncatedGapOmegahatBelowWidth P D X) :
    profileCard R < width P := by
  exact profileCard_lt_width_of_mem
    P D X.family X.rigid X.delta X.kmax X.omegaHat hω R hR

theorem truncatedGapFamily_nil_or_cons
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact supportProfileFamily_exhaustive X.family

@[simp] theorem truncatedGapHead?_nil
    (P : Params) (D : ClosureData P)
    (hEmpty :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S → False)
    (hR : RigidProfileFamily P D [])
    (δ : DeltaStarData P D [] hR)
    (K : KmaxData P D [] hR)
    (_ω : OmegahatData P D [] hR δ K) :
    truncatedGapHead? P D
      (TruncatedGapPackage.mk []
        (isTruncatedFamily_nil_of_no_admissible P D hEmpty)
        hR δ K _ω) = none := rfl

@[simp] theorem truncatedGapHead?_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (_ω : OmegahatData P D (R :: F) hR δ K) :
    truncatedGapHead? P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K _ω) = some R := rfl

theorem truncatedGapHead_truncated
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (_hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) _hR)
    (_K : KmaxData P D (R :: F) _hR)
    (_ω : OmegahatData P D (R :: F) _hR _δ _K) :
    ProfileInTruncatedFamily P D R := by
  exact isTruncatedFamily_mem P D (R :: F) hT R (by simp)

theorem truncatedGapHead_preAdmissible
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (_hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) _hR)
    (_K : KmaxData P D (R :: F) _hR)
    (_ω : OmegahatData P D (R :: F) _hR _δ _K) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact isTruncatedFamily_mem_preAdmissible P D (R :: F) hT R (by simp)

def truncatedGapHead_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (_hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) hR)
    (_K : KmaxData P D (R :: F) hR)
    (_ω : OmegahatData P D (R :: F) hR _δ _K) :
    RigidProfile P D R := by
  exact rigidProfileFamily_head P D R F hR

theorem truncatedGapTail_soundForCaseC
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (_hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) _hR)
    (_K : KmaxData P D (R :: F) _hR)
    (_ω : OmegahatData P D (R :: F) _hR _δ _K) :
    FamilySoundForCaseC P D F := by
  exact truncatedFamily_tail_soundForCaseC P D R F hT

theorem truncatedGapTail_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (_hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) _hR)
    (_K : KmaxData P D (R :: F) _hR)
    (_ω : OmegahatData P D (R :: F) _hR _δ _K) :
    FamilyAllInTruncatedFamily P D F := by
  exact truncatedFamily_tail_allInTruncatedFamily P D R F hT

def truncatedGapTail_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (_hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) hR)
    (_K : KmaxData P D (R :: F) hR)
    (_ω : OmegahatData P D (R :: F) hR _δ _K) :
    RigidProfileFamily P D F := by
  exact rigidProfileFamily_tail P D R F hR

theorem truncatedGapPackage_omegahatBelowWidth_or_not
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapOmegahatBelowWidth P D X ∨
      ¬ truncatedGapOmegahatBelowWidth P D X := by
  exact Classical.em _

end GapClosure
end CaseC
end Lehmer