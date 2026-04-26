-- FILE: Lean/Lehmer/CaseC/GapClosure/ClosureBoundN.lean
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
- Lehmer.CaseC.GapClosure.Bootstrap : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.DeltaStar
import Lehmer.CaseC.GapClosure.Omegahat
import Lehmer.CaseC.GapClosure.TruncatedFamily
import Lehmer.CaseC.GapClosure.Bootstrap

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure ClosureBoundData
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) where
  value : ℕ
  positive : 0 < value
  atLeastCap : cap P D ≤ value
  closureDataBelow : D.N ≤ value

@[simp] theorem ClosureBoundData.value_mk
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (value : ℕ)
    (positive : 0 < value)
    (atLeastCap : cap P D ≤ value)
    (closureDataBelow : D.N ≤ value) :
    (ClosureBoundData.mk value positive atLeastCap closureDataBelow :
      ClosureBoundData P D X).value = value := rfl

def closureBoundValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) : ℕ :=
  N.value

@[simp] theorem closureBoundValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) :
    closureBoundValue P D X N = N.value := rfl

def ClosureBoundAtLeastCap
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) : Prop :=
  cap P D ≤ closureBoundValue P D X N

@[simp] theorem ClosureBoundAtLeastCap_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) :
    ClosureBoundAtLeastCap P D X N =
      (cap P D ≤ closureBoundValue P D X N) := rfl

theorem closureBound_positive
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) :
    0 < closureBoundValue P D X N := by
  exact N.positive

theorem closureBound_atLeastCap
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) :
    ClosureBoundAtLeastCap P D X N := by
  exact N.atLeastCap

theorem closureBound_closureDataBelow
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) :
    D.N ≤ closureBoundValue P D X N := by
  exact N.closureDataBelow

structure BootstrapClosureBoundPackage
    (P : Params) (D : ClosureData P) where
  data : BootstrapPackage P D
  bound : ClosureBoundData P D data

@[simp] theorem BootstrapClosureBoundPackage.data_mk
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) :
    (BootstrapClosureBoundPackage.mk X N).data = X := rfl

@[simp] theorem BootstrapClosureBoundPackage.bound_mk
    (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D)
    (N : ClosureBoundData P D X) :
    (BootstrapClosureBoundPackage.mk X N).bound = N := rfl

def bootstrapClosureBoundFamily
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : SupportProfileFamily :=
  bootstrapFamily P D X.data

@[simp] theorem bootstrapClosureBoundFamily_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundFamily P D X =
      bootstrapFamily P D X.data := rfl

def bootstrapClosureBoundValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : ℕ :=
  closureBoundValue P D X.data X.bound

@[simp] theorem bootstrapClosureBoundValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundValue P D X =
      closureBoundValue P D X.data X.bound := rfl

def bootstrapClosureBoundDeltaValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : ℚ :=
  bootstrapDeltaValue P D X.data

@[simp] theorem bootstrapClosureBoundDeltaValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundDeltaValue P D X =
      bootstrapDeltaValue P D X.data := rfl

def bootstrapClosureBoundKmaxValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : ℚ :=
  bootstrapKmaxValue P D X.data

@[simp] theorem bootstrapClosureBoundKmaxValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundKmaxValue P D X =
      bootstrapKmaxValue P D X.data := rfl

def bootstrapClosureBoundOmegahatValue
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : ℕ :=
  bootstrapOmegahatValue P D X.data

@[simp] theorem bootstrapClosureBoundOmegahatValue_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundOmegahatValue P D X =
      bootstrapOmegahatValue P D X.data := rfl

def bootstrapClosureBoundHead?
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : Option SupportProfile :=
  bootstrapHead? P D X.data

@[simp] theorem bootstrapClosureBoundHead?_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundHead? P D X =
      bootstrapHead? P D X.data := rfl

def bootstrapClosureBoundAtLeastCap
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : Prop :=
  ClosureBoundAtLeastCap P D X.data X.bound

@[simp] theorem bootstrapClosureBoundAtLeastCap_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundAtLeastCap P D X =
      ClosureBoundAtLeastCap P D X.data X.bound := rfl

theorem BootstrapClosureBoundPackage.bootstrap_holds
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    BootstrapCondition P D X.data.data := by
  exact X.data.bootstrap

theorem BootstrapClosureBoundPackage.member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ X.data.data.family →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact BootstrapPackage.member_preAdmissible P D X.data R hR

theorem BootstrapClosureBoundPackage.member_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ X.data.data.family →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact BootstrapPackage.member_admissibleAtLevel P D X.data R hR

theorem BootstrapClosureBoundPackage.member_locksB
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ X.data.data.family →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact BootstrapPackage.member_locksB P D X.data R hR

theorem BootstrapClosureBoundPackage.member_truncated
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ X.data.data.family →
      ProfileInTruncatedFamily P D R := by
  intro R hR
  exact BootstrapPackage.member_truncated P D X.data R hR

def BootstrapClosureBoundPackage.member_rigid
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ X.data.data.family →
      RigidProfile P D R := by
  intro R hR
  exact BootstrapPackage.member_rigid P D X.data R hR

theorem BootstrapClosureBoundPackage.covers_preAdmissible_support
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S) :
    SupportProfile.mk S ∈ X.data.data.family := by
  exact BootstrapPackage.covers_preAdmissible_support P D X.data S hPre

theorem BootstrapClosureBoundPackage.covers_candidateProfile_of_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D)
    {n : ℕ}
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n)) :
    candidateProfile n ∈ X.data.data.family := by
  exact BootstrapPackage.covers_candidateProfile_of_preAdmissible P D X.data hPre

theorem BootstrapClosureBoundPackage.delta_positive
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    0 < bootstrapClosureBoundDeltaValue P D X := by
  exact BootstrapPackage.delta_positive P D X.data

theorem BootstrapClosureBoundPackage.delta_le_member_gap
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.data.family) :
    bootstrapClosureBoundDeltaValue P D X ≤
      profileRigidityGapValue P D R (X.data.data.rigid R hR) := by
  exact BootstrapPackage.delta_le_member_gap P D X.data R hR

theorem BootstrapClosureBoundPackage.kmax_positive
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    0 < bootstrapClosureBoundKmaxValue P D X := by
  exact BootstrapPackage.kmax_positive P D X.data

theorem BootstrapClosureBoundPackage.member_index_le_kmax
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.data.family) :
    profileSupportIndex R ≤ bootstrapClosureBoundKmaxValue P D X := by
  exact BootstrapPackage.member_index_le_kmax P D X.data R hR

theorem BootstrapClosureBoundPackage.omegahat_below_width
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundOmegahatValue P D X < width P := by
  exact BootstrapPackage.omegahat_below_width P D X.data

theorem BootstrapClosureBoundPackage.omegahat_le_width
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundOmegahatValue P D X ≤ width P := by
  exact BootstrapPackage.omegahat_le_width P D X.data

theorem BootstrapClosureBoundPackage.omegahat_matches_closureData
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X.data.data) :
    D.omegaHat = bootstrapClosureBoundOmegahatValue P D X := by
  exact BootstrapPackage.omegahat_matches_closureData P D X.data hMatch

theorem BootstrapClosureBoundPackage.member_within_closure_omega
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.data.family)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X.data.data) :
    SupportWithinOmega D.omegaHat (profileSupport R) := by
  exact BootstrapPackage.member_within_closure_omega P D X.data R hR hMatch

theorem BootstrapClosureBoundPackage.member_card_lt_width
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.data.data.family) :
    profileCard R < width P := by
  exact BootstrapPackage.member_card_lt_width P D X.data R hR

theorem BootstrapClosureBoundPackage.bound_positive
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    0 < bootstrapClosureBoundValue P D X := by
  exact X.bound.positive

theorem BootstrapClosureBoundPackage.bound_atLeastCap
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    cap P D ≤ bootstrapClosureBoundValue P D X := by
  exact X.bound.atLeastCap

theorem BootstrapClosureBoundPackage.bound_closureDataBelow
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    D.N ≤ bootstrapClosureBoundValue P D X := by
  exact X.bound.closureDataBelow

def BootstrapClosureBoundReady
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : Prop :=
  0 < bootstrapClosureBoundDeltaValue P D X ∧
  0 < bootstrapClosureBoundKmaxValue P D X ∧
  bootstrapClosureBoundOmegahatValue P D X < width P ∧
  0 < bootstrapClosureBoundValue P D X ∧
  cap P D ≤ bootstrapClosureBoundValue P D X ∧
  D.N ≤ bootstrapClosureBoundValue P D X

@[simp] theorem BootstrapClosureBoundReady_def
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    BootstrapClosureBoundReady P D X =
      (0 < bootstrapClosureBoundDeltaValue P D X ∧
      0 < bootstrapClosureBoundKmaxValue P D X ∧
      bootstrapClosureBoundOmegahatValue P D X < width P ∧
      0 < bootstrapClosureBoundValue P D X ∧
      cap P D ≤ bootstrapClosureBoundValue P D X ∧
      D.N ≤ bootstrapClosureBoundValue P D X) := rfl

theorem bootstrapClosureBoundReady
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    BootstrapClosureBoundReady P D X := by
  exact ⟨
    BootstrapClosureBoundPackage.delta_positive P D X,
    BootstrapClosureBoundPackage.kmax_positive P D X,
    BootstrapClosureBoundPackage.omegahat_below_width P D X,
    BootstrapClosureBoundPackage.bound_positive P D X,
    BootstrapClosureBoundPackage.bound_atLeastCap P D X,
    BootstrapClosureBoundPackage.bound_closureDataBelow P D X
  ⟩

theorem bootstrapClosureBoundFamily_nil_or_cons
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    X.data.data.family = [] ∨ ∃ R F, X.data.data.family = R :: F := by
  exact BootstrapPackage.family_nil_or_cons P D X.data

@[simp] theorem bootstrapClosureBoundHead?_nil
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
        hR δ K ω))
    (N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk []
          (isTruncatedFamily_nil_of_no_admissible P D hEmpty)
          hR δ K ω)
        hB)) :
    bootstrapClosureBoundHead? P D
      (BootstrapClosureBoundPackage.mk
        (BootstrapPackage.mk
          (TruncatedGapPackage.mk []
            (isTruncatedFamily_nil_of_no_admissible P D hEmpty)
            hR δ K ω)
          hB)
        N) = none := rfl

@[simp] theorem bootstrapClosureBoundHead?_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω))
    (N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB)) :
    bootstrapClosureBoundHead? P D
      (BootstrapClosureBoundPackage.mk
        (BootstrapPackage.mk
          (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
          hB)
        N) = some R := rfl

theorem BootstrapClosureBoundPackage.head_preAdmissible
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω))
    (_N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB)) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact BootstrapPackage.head_preAdmissible P D R F hT hR δ K ω hB

theorem BootstrapClosureBoundPackage.head_truncated
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω))
    (_N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB)) :
    ProfileInTruncatedFamily P D R := by
  exact BootstrapPackage.head_truncated P D R F hT hR δ K ω hB

def BootstrapClosureBoundPackage.head_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω))
    (_N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB)) :
    RigidProfile P D R := by
  exact BootstrapPackage.head_rigid P D R F hT hR δ K ω hB

theorem BootstrapClosureBoundPackage.tail_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω))
    (_N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB)) :
    FamilyAllInTruncatedFamily P D F := by
  exact BootstrapPackage.tail_allInTruncatedFamily P D R F hT hR δ K ω hB

theorem BootstrapClosureBoundPackage.tail_soundForCaseC
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω))
    (_N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB)) :
    FamilySoundForCaseC P D F := by
  exact BootstrapPackage.tail_soundForCaseC P D R F hT hR δ K ω hB

def BootstrapClosureBoundPackage.tail_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hR)
    (K : KmaxData P D (R :: F) hR)
    (ω : OmegahatData P D (R :: F) hR δ K)
    (hB : BootstrapCondition P D
      (TruncatedGapPackage.mk (R :: F) hT hR δ K ω))
    (_N : ClosureBoundData P D
      (BootstrapPackage.mk
        (TruncatedGapPackage.mk (R :: F) hT hR δ K ω)
        hB)) :
    RigidProfileFamily P D F := by
  exact BootstrapPackage.tail_rigid P D R F hT hR δ K ω hB

theorem bootstrapClosureBound_member_truncated_readable
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ bootstrapClosureBoundFamily P D X →
      ProfileInTruncatedFamily P D R := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_truncated P D X R hR

def bootstrapClosureBound_member_rigid_readable
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ bootstrapClosureBoundFamily P D X →
      RigidProfile P D R := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_rigid P D X R hR

theorem bootstrapClosureBound_member_preAdmissible_readable
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ bootstrapClosureBoundFamily P D X →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_preAdmissible P D X R hR

theorem bootstrapClosureBound_member_admissibleAtLevel_readable
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ bootstrapClosureBoundFamily P D X →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_admissibleAtLevel P D X R hR

theorem bootstrapClosureBound_member_locksB_readable
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ bootstrapClosureBoundFamily P D X →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_locksB P D X R hR

end GapClosure
end CaseC
end Lehmer