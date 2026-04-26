-- FILE: Lean/Lehmer/CaseC/GapClosure/Omegahat.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.DeltaStar

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure KmaxData
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F) where
  value : ℚ
  positive : 0 < value
  upperBound :
    ∀ R : SupportProfile,
      R ∈ F →
        profileSupportIndex R ≤ value

def kmaxValue
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (K : KmaxData P D F hF) : ℚ :=
  K.value

@[simp] theorem kmaxValue_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (K : KmaxData P D F hF) :
    kmaxValue P D F hF K = K.value := rfl

theorem kmax_positive
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (K : KmaxData P D F hF) :
    0 < kmaxValue P D F hF K := by
  exact K.positive

theorem profileIndex_le_kmax
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (K : KmaxData P D F hF)
    (R : SupportProfile)
    (hR : R ∈ F) :
    profileSupportIndex R ≤ kmaxValue P D F hF K := by
  exact K.upperBound R hR

structure OmegahatData
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF) where
  value : ℕ
  positive : 0 < value
  cardinalBound :
    ∀ R : SupportProfile,
      R ∈ F →
        profileCard R ≤ value

def omegahatValue
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K) : ℕ :=
  ω.value

@[simp] theorem omegahatValue_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K) :
    omegahatValue P D F hF δ K ω = ω.value := rfl

theorem omegahat_positive
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K) :
    0 < omegahatValue P D F hF δ K ω := by
  exact ω.positive

theorem profileCard_le_omegahat
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (R : SupportProfile)
    (hR : R ∈ F) :
    profileCard R ≤ omegahatValue P D F hF δ K ω := by
  exact ω.cardinalBound R hR

theorem supportCard_le_omegahat_of_mem
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (R : SupportProfile)
    (hR : R ∈ F) :
    supportCard (profileSupport R) ≤
      omegahatValue P D F hF δ K ω := by
  simpa [profileCard] using
    profileCard_le_omegahat P D F hF δ K ω R hR

def OmegahatBelowWidth
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K) : Prop :=
  omegahatValue P D F hF δ K ω < width P

@[simp] theorem OmegahatBelowWidth_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K) :
    OmegahatBelowWidth P D F hF δ K ω =
      (omegahatValue P D F hF δ K ω < width P) := rfl

theorem omegahat_lt_width
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω) :
    omegahatValue P D F hF δ K ω < width P := by
  exact hω

theorem omegahat_le_width
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω) :
    omegahatValue P D F hF δ K ω ≤ width P := by
  exact Nat.le_of_lt hω

theorem profileCard_lt_width_of_mem
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω)
    (R : SupportProfile)
    (hR : R ∈ F) :
    profileCard R < width P := by
  exact lt_of_le_of_lt
    (profileCard_le_omegahat P D F hF δ K ω R hR)
    hω

theorem supportCard_lt_width_of_mem
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω)
    (R : SupportProfile)
    (hR : R ∈ F) :
    supportCard (profileSupport R) < width P := by
  simpa [profileCard] using
    profileCard_lt_width_of_mem P D F hF δ K ω hω R hR

theorem supportWithinOmega_of_mem
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (R : SupportProfile)
    (hR : R ∈ F) :
    SupportWithinOmega
      (omegahatValue P D F hF δ K ω)
      (profileSupport R) := by
  exact supportCard_le_omegahat_of_mem P D F hF δ K ω R hR

def OmegahatMatchesClosureData
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K) : Prop :=
  D.omegaHat = omegahatValue P D F hF δ K ω

@[simp] theorem OmegahatMatchesClosureData_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K) :
    OmegahatMatchesClosureData P D F hF δ K ω =
      (D.omegaHat = omegahatValue P D F hF δ K ω) := rfl

theorem supportWithinClosureOmega_of_mem
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hMatch : OmegahatMatchesClosureData P D F hF δ K ω)
    (R : SupportProfile)
    (hR : R ∈ F) :
    SupportWithinOmega D.omegaHat (profileSupport R) := by
  rw [hMatch]
  exact supportWithinOmega_of_mem P D F hF δ K ω R hR

structure RigidOmegahatPackage
    (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  rigid : RigidProfileFamily P D family
  delta : DeltaStarData P D family rigid
  kmax : KmaxData P D family rigid
  omegaHat : OmegahatData P D family rigid delta kmax
  belowWidth : OmegahatBelowWidth P D family rigid delta kmax omegaHat
  matchesClosureData :
    OmegahatMatchesClosureData P D family rigid delta kmax omegaHat

@[simp] theorem RigidOmegahatPackage.family_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω)
    (hMatch : OmegahatMatchesClosureData P D F hF δ K ω) :
    (RigidOmegahatPackage.mk F hF δ K ω hω hMatch).family = F := rfl

@[simp] theorem RigidOmegahatPackage.rigid_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω)
    (hMatch : OmegahatMatchesClosureData P D F hF δ K ω) :
    (RigidOmegahatPackage.mk F hF δ K ω hω hMatch).rigid = hF := rfl

@[simp] theorem RigidOmegahatPackage.delta_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω)
    (hMatch : OmegahatMatchesClosureData P D F hF δ K ω) :
    (RigidOmegahatPackage.mk F hF δ K ω hω hMatch).delta = δ := rfl

@[simp] theorem RigidOmegahatPackage.kmax_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω)
    (hMatch : OmegahatMatchesClosureData P D F hF δ K ω) :
    (RigidOmegahatPackage.mk F hF δ K ω hω hMatch).kmax = K := rfl

@[simp] theorem RigidOmegahatPackage.omegaHat_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (K : KmaxData P D F hF)
    (ω : OmegahatData P D F hF δ K)
    (hω : OmegahatBelowWidth P D F hF δ K ω)
    (hMatch : OmegahatMatchesClosureData P D F hF δ K ω) :
    (RigidOmegahatPackage.mk F hF δ K ω hω hMatch).omegaHat = ω := rfl

def rigidOmegahatFamily
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem rigidOmegahatFamily_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatFamily P D X = X.family := rfl

def rigidOmegahatDeltaValue
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) : ℚ :=
  deltaStarValue P D X.family X.rigid X.delta

@[simp] theorem rigidOmegahatDeltaValue_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatDeltaValue P D X =
      deltaStarValue P D X.family X.rigid X.delta := rfl

def rigidOmegahatKmaxValue
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) : ℚ :=
  kmaxValue P D X.family X.rigid X.kmax

@[simp] theorem rigidOmegahatKmaxValue_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatKmaxValue P D X =
      kmaxValue P D X.family X.rigid X.kmax := rfl

def rigidOmegahatValue
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) : ℕ :=
  omegahatValue P D X.family X.rigid X.delta X.kmax X.omegaHat

@[simp] theorem rigidOmegahatValue_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatValue P D X =
      omegahatValue P D X.family X.rigid X.delta X.kmax X.omegaHat := rfl

def rigidOmegahatBelowWidth
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) : Prop :=
  OmegahatBelowWidth P D X.family X.rigid X.delta X.kmax X.omegaHat

@[simp] theorem rigidOmegahatBelowWidth_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatBelowWidth P D X =
      OmegahatBelowWidth P D X.family X.rigid X.delta X.kmax X.omegaHat := rfl

theorem rigidOmegahat_delta_positive
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    0 < rigidOmegahatDeltaValue P D X := by
  exact deltaStar_positive P D X.family X.rigid X.delta

theorem rigidOmegahat_kmax_positive
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    0 < rigidOmegahatKmaxValue P D X := by
  exact kmax_positive P D X.family X.rigid X.kmax

theorem rigidOmegahat_positive
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    0 < rigidOmegahatValue P D X := by
  exact omegahat_positive P D X.family X.rigid X.delta X.kmax X.omegaHat

theorem rigidOmegahat_belowWidth
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatValue P D X < width P := by
  exact X.belowWidth

theorem rigidOmegahat_leWidth
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatValue P D X ≤ width P := by
  exact Nat.le_of_lt X.belowWidth

theorem rigidOmegahat_matchesClosureData
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    D.omegaHat = rigidOmegahatValue P D X := by
  exact X.matchesClosureData

theorem rigidOmegahat_member_withinOmega
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family) :
    SupportWithinOmega D.omegaHat (profileSupport R) := by
  rw [rigidOmegahat_matchesClosureData P D X]
  exact supportWithinOmega_of_mem
    P D X.family X.rigid X.delta X.kmax X.omegaHat R hR

theorem rigidOmegahat_member_card_lt_width
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family) :
    profileCard R < width P := by
  exact profileCard_lt_width_of_mem
    P D X.family X.rigid X.delta X.kmax X.omegaHat
    X.belowWidth R hR

theorem rigidOmegahat_member_supportCard_lt_width
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family) :
    supportCard (profileSupport R) < width P := by
  simpa [profileCard] using
    rigidOmegahat_member_card_lt_width P D X R hR

def rigidOmegahatPackage_member_rigid
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact X.rigid R hR

theorem rigidOmegahatPackage_member_truncated
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    ∀ R, R ∈ X.family → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact RigidProfile.in_truncated P D R (X.rigid R hR)

theorem rigidOmegahatPackage_member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    ∀ R, R ∈ X.family →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact RigidProfile.preAdmissible P D R (X.rigid R hR)

def rigidOmegahatHead?
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) : Option SupportProfile :=
  familyHead? X.family

@[simp] theorem rigidOmegahatHead?_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatHead? P D X = familyHead? X.family := rfl

theorem rigidOmegahatFamily_nil_or_cons
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact supportProfileFamily_exhaustive X.family

@[simp] theorem rigidOmegahatHead?_nil
    (P : Params) (D : ClosureData P)
    (hF : RigidProfileFamily P D [])
    (δ : DeltaStarData P D [] hF)
    (K : KmaxData P D [] hF)
    (ω : OmegahatData P D [] hF δ K)
    (hω : OmegahatBelowWidth P D [] hF δ K ω)
    (hMatch : OmegahatMatchesClosureData P D [] hF δ K ω) :
    rigidOmegahatHead? P D
      (RigidOmegahatPackage.mk [] hF δ K ω hω hMatch) = none := rfl

@[simp] theorem rigidOmegahatHead?_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hF)
    (K : KmaxData P D (R :: F) hF)
    (ω : OmegahatData P D (R :: F) hF δ K)
    (hω : OmegahatBelowWidth P D (R :: F) hF δ K ω)
    (hMatch : OmegahatMatchesClosureData P D (R :: F) hF δ K ω) :
    rigidOmegahatHead? P D
      (RigidOmegahatPackage.mk (R :: F) hF δ K ω hω hMatch) = some R := rfl

def rigidOmegahatHead_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) hF)
    (_K : KmaxData P D (R :: F) hF)
    (_ω : OmegahatData P D (R :: F) hF _δ _K)
    (_hω : OmegahatBelowWidth P D (R :: F) hF _δ _K _ω)
    (_hMatch : OmegahatMatchesClosureData P D (R :: F) hF _δ _K _ω) :
    RigidProfile P D R := by
  exact rigidProfileFamily_head P D R F hF

def rigidOmegahatTail_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) hF)
    (_K : KmaxData P D (R :: F) hF)
    (_ω : OmegahatData P D (R :: F) hF _δ _K)
    (_hω : OmegahatBelowWidth P D (R :: F) hF _δ _K _ω)
    (_hMatch : OmegahatMatchesClosureData P D (R :: F) hF _δ _K _ω) :
    RigidProfileFamily P D F := by
  exact rigidProfileFamily_tail P D R F hF

def rigidOmegahatPackage_delta_readable
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    DeltaStarData P D X.family X.rigid :=
  X.delta

@[simp] theorem rigidOmegahatPackage_delta_readable_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatPackage_delta_readable P D X = X.delta := rfl

def rigidOmegahatPackage_kmax_readable
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    KmaxData P D X.family X.rigid :=
  X.kmax

@[simp] theorem rigidOmegahatPackage_kmax_readable_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatPackage_kmax_readable P D X = X.kmax := rfl

def rigidOmegahatPackage_omega_readable
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    OmegahatData P D X.family X.rigid X.delta X.kmax :=
  X.omegaHat

@[simp] theorem rigidOmegahatPackage_omega_readable_def
    (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatPackage_omega_readable P D X = X.omegaHat := rfl

end GapClosure
end CaseC
end Lehmer