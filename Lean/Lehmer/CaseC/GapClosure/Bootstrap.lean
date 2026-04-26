-- FILE: Lean/Lehmer/CaseC/GapClosure/Bootstrap.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
- Lehmer.CaseC.GapClosure.Omegahat : def thm
- Lehmer.CaseC.GapClosure.TruncatedFamily : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.DeltaStar
import Lehmer.CaseC.GapClosure.Omegahat
import Lehmer.CaseC.GapClosure.TruncatedFamily

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def BootstrapCondition
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : Prop :=
  truncatedGapOmegahatBelowWidth P D X

@[simp] theorem BootstrapCondition_def
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    BootstrapCondition P D X =
      truncatedGapOmegahatBelowWidth P D X := rfl

theorem bootstrapCondition_iff
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    BootstrapCondition P D X ↔
      truncatedGapOmegahatBelowWidth P D X := by
  rfl

structure BootstrapPackage
    (P : Params) (D : ClosureData P) where
  data : TruncatedGapPackage P D
  bootstrap : BootstrapCondition P D data

@[simp] theorem BootstrapPackage.data_mk
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (hX : BootstrapCondition P D X) :
    (BootstrapPackage.mk X hX).data = X := rfl

@[simp] theorem BootstrapPackage.bootstrap_mk
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (hX : BootstrapCondition P D X) :
    (BootstrapPackage.mk X hX).bootstrap = hX := rfl

def bootstrapFamily
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    SupportProfileFamily :=
  X.data.family

@[simp] theorem bootstrapFamily_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapFamily P D X = X.data.family := rfl

def bootstrapDeltaValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) : ℚ :=
  truncatedGapDeltaValue P D X.data

@[simp] theorem bootstrapDeltaValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapDeltaValue P D X =
      truncatedGapDeltaValue P D X.data := rfl

def bootstrapKmaxValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) : ℚ :=
  truncatedGapKmaxValue P D X.data

@[simp] theorem bootstrapKmaxValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapKmaxValue P D X =
      truncatedGapKmaxValue P D X.data := rfl

def bootstrapOmegahatValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) : ℕ :=
  truncatedGapOmegahatValue P D X.data

@[simp] theorem bootstrapOmegahatValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapOmegahatValue P D X =
      truncatedGapOmegahatValue P D X.data := rfl

def bootstrapClosureOmega
    (P : Params) (D : ClosureData P)
    (_X : BootstrapPackage P D) : ℕ :=
  D.omegaHat

@[simp] theorem bootstrapClosureOmega_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapClosureOmega P D X = D.omegaHat := rfl

def bootstrapHead?
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    Option SupportProfile :=
  truncatedGapHead? P D X.data

@[simp] theorem bootstrapHead?_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapHead? P D X = truncatedGapHead? P D X.data := rfl

theorem BootstrapPackage.bootstrap_holds
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    BootstrapCondition P D X.data := by
  exact X.bootstrap

theorem BootstrapPackage.member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    ∀ R, R ∈ X.data.family →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact truncatedGapPackage_member_preAdmissible P D X.data R hR

theorem BootstrapPackage.member_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    ∀ R, R ∈ X.data.family →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact truncatedGapPackage_member_admissibleAtLevel P D X.data R hR

theorem BootstrapPackage.member_locksB
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    ∀ R, R ∈ X.data.family →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact truncatedGapPackage_member_locksB P D X.data R hR

theorem BootstrapPackage.member_truncated
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    ∀ R, R ∈ X.data.family →
      ProfileInTruncatedFamily P D R := by
  intro R hR
  exact truncatedGapPackage_member_truncated P D X.data R hR

def BootstrapPackage.member_rigid
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    ∀ R, R ∈ X.data.family →
      RigidProfile P D R := by
  intro R hR
  exact truncatedGapPackage_member_rigid P D X.data R hR

theorem BootstrapPackage.covers_preAdmissible_support
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S) :
    SupportProfile.mk S ∈ X.data.family := by
  exact truncatedGapPackage_covers_support P D X.data S hPre

theorem BootstrapPackage.covers_candidateProfile_of_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    {n : ℕ}
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n)) :
    candidateProfile n ∈ X.data.family := by
  have hMem : SupportProfile.mk (candidateSupport n) ∈ X.data.family :=
    BootstrapPackage.covers_preAdmissible_support
      P D X (candidateSupport n) hPre
  simpa [candidateProfile] using hMem

theorem BootstrapPackage.delta_positive
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    0 < bootstrapDeltaValue P D X := by
  exact truncatedGapDeltaPositive P D X.data

theorem BootstrapPackage.delta_le_member_gap
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.family) :
    bootstrapDeltaValue P D X ≤
      profileRigidityGapValue P D R (X.data.rigid R hR) := by
  exact truncatedGapDelta_le_member_gap P D X.data R hR

theorem BootstrapPackage.kmax_positive
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    0 < bootstrapKmaxValue P D X := by
  exact truncatedGapKmaxPositive P D X.data

theorem BootstrapPackage.member_index_le_kmax
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.family) :
    profileSupportIndex R ≤ bootstrapKmaxValue P D X := by
  exact truncatedGapMember_index_le_kmax P D X.data R hR

theorem BootstrapPackage.omegahat_below_width
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapOmegahatValue P D X < width P := by
  exact truncatedGapOmegahatBelowWidth_value P D X.data X.bootstrap

theorem BootstrapPackage.omegahat_le_width
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapOmegahatValue P D X ≤ width P := by
  exact Nat.le_of_lt (BootstrapPackage.omegahat_below_width P D X)

theorem BootstrapPackage.omegahat_matches_closureData
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X.data) :
    D.omegaHat = bootstrapOmegahatValue P D X := by
  exact truncatedGapOmegahatMatchesClosureData_value P D X.data hMatch

theorem BootstrapPackage.member_within_closure_omega
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.family)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X.data) :
    SupportWithinOmega D.omegaHat (profileSupport R) := by
  exact truncatedGapPackage_member_withinClosureOmega P D X.data R hR hMatch

theorem BootstrapPackage.member_card_lt_width
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.family) :
    profileCard R < width P := by
  exact truncatedGapPackage_member_card_lt_width P D X.data R hR X.bootstrap

theorem BootstrapPackage.member_supportCard_lt_width
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.family) :
    supportCard (profileSupport R) < width P := by
  simpa [profileCard] using
    BootstrapPackage.member_card_lt_width P D X R hR

theorem BootstrapPackage.family_nil_or_cons
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    X.data.family = [] ∨ ∃ R F, X.data.family = R :: F := by
  exact truncatedGapFamily_nil_or_cons P D X.data

@[simp] theorem bootstrapHead?_nil
    (P : Params) (D : ClosureData P)
    (hEmpty :
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S → False)
    (hR : RigidProfileFamily P D [])
    (δ : DeltaStarData P D [] hR)
    (K : KmaxData P D [] hR)
    (ω : OmegahatData P D [] hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk []
        (isTruncatedFamily_nil_of_no_admissible P D hEmpty)
        hR δ K ω)) :
    bootstrapHead? P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk []
          (isTruncatedFamily_nil_of_no_admissible P D hEmpty)
          hR δ K ω)
        hB) = none := rfl

@[simp] theorem bootstrapHead?_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)) :
    bootstrapHead? P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB) = some R := rfl

theorem BootstrapPackage.head_preAdmissible
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (_hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact truncatedGapHead_preAdmissible P D R F hT hR δ K ω

theorem BootstrapPackage.head_truncated
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (_hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)) :
    ProfileInTruncatedFamily P D R := by
  exact truncatedGapHead_truncated P D R F hT hR δ K ω

def BootstrapPackage.head_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (_hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)) :
    RigidProfile P D R := by
  exact truncatedGapHead_rigid P D R F hT hR δ K ω

theorem BootstrapPackage.tail_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (_hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)) :
    FamilyAllInTruncatedFamily P D F := by
  exact truncatedGapTail_allInTruncatedFamily P D R F hT hR δ K ω

theorem BootstrapPackage.tail_soundForCaseC
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (_hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)) :
    FamilySoundForCaseC P D F := by
  exact truncatedGapTail_soundForCaseC P D R F hT hR δ K ω

def BootstrapPackage.tail_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (_hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)) :
    RigidProfileFamily P D F := by
  exact truncatedGapTail_rigid P D R F hT hR δ K ω

def bootstrapFromTruncatedGap
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (hX : BootstrapCondition P D X) :
    BootstrapPackage P D :=
  BootstrapPackage.mk X hX

@[simp] theorem bootstrapFromTruncatedGap_data
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (hX : BootstrapCondition P D X) :
    (bootstrapFromTruncatedGap P D X hX).data = X := rfl

@[simp] theorem bootstrapFromTruncatedGap_bootstrap
    (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D)
    (hX : BootstrapCondition P D X) :
    (bootstrapFromTruncatedGap P D X hX).bootstrap = hX := rfl

end GapClosure
end CaseC
end Lehmer