-- FILE: Lean/Lehmer/CaseC/GapClosure/GapToClosure.lean
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
- Lehmer.CaseC.GapClosure.ClosureBoundN : def thm
- Lehmer.CaseC.GapClosure.KmaxGap : def thm
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
import Lehmer.CaseC.GapClosure.ClosureBoundN
import Lehmer.CaseC.GapClosure.KmaxGap

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure GapClosurePackage (P : Params) (D : ClosureData P) where
  data : BootstrapClosureBoundPackage P D

@[simp] theorem GapClosurePackage.data_mk
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    (GapClosurePackage.mk X).data = X := rfl

def gapClosureFamily
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : SupportProfileFamily :=
  bootstrapClosureBoundFamily P D X.data

@[simp] theorem gapClosureFamily_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureFamily P D X = bootstrapClosureBoundFamily P D X.data := rfl

def gapClosureDeltaValue
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : ℚ :=
  bootstrapClosureBoundDeltaValue P D X.data

@[simp] theorem gapClosureDeltaValue_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureDeltaValue P D X =
      bootstrapClosureBoundDeltaValue P D X.data := rfl

def gapClosureKmaxValue
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : ℚ :=
  bootstrapClosureBoundKmaxValue P D X.data

@[simp] theorem gapClosureKmaxValue_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureKmaxValue P D X =
      bootstrapClosureBoundKmaxValue P D X.data := rfl

def gapClosureOmegahatValue
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : ℕ :=
  bootstrapClosureBoundOmegahatValue P D X.data

@[simp] theorem gapClosureOmegahatValue_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegahatValue P D X =
      bootstrapClosureBoundOmegahatValue P D X.data := rfl

def gapClosureBoundValue
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : ℕ :=
  bootstrapClosureBoundValue P D X.data

@[simp] theorem gapClosureBoundValue_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureBoundValue P D X =
      bootstrapClosureBoundValue P D X.data := rfl

def gapClosureHead?
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : Option SupportProfile :=
  bootstrapClosureBoundHead? P D X.data

@[simp] theorem gapClosureHead?_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureHead? P D X =
      bootstrapClosureBoundHead? P D X.data := rfl

def gapClosureCap
    (P : Params) (D : ClosureData P)
    (_X : GapClosurePackage P D) : ℕ :=
  cap P D

@[simp] theorem gapClosureCap_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureCap P D X = cap P D := rfl

def gapClosureOmegaBound
    (P : Params) (D : ClosureData P)
    (_X : GapClosurePackage P D) : ℕ :=
  omegaBound P D

@[simp] theorem gapClosureOmegaBound_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegaBound P D X = omegaBound P D := rfl

def gapClosureClosureData
    (P : Params) (D : ClosureData P)
    (_X : GapClosurePackage P D) : ClosureData P :=
  D

@[simp] theorem gapClosureClosureData_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureClosureData P D X = D := rfl

theorem GapClosurePackage.bootstrap_holds
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    BootstrapCondition P D X.data.data.data := by
  exact BootstrapClosureBoundPackage.bootstrap_holds P D X.data

theorem GapClosurePackage.member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_preAdmissible P D X.data R hR

theorem GapClosurePackage.member_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_admissibleAtLevel P D X.data R hR

theorem GapClosurePackage.member_locksB
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_locksB P D X.data R hR

theorem GapClosurePackage.member_truncated
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        ProfileInTruncatedFamily P D R := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_truncated P D X.data R hR

def GapClosurePackage.member_rigid
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        RigidProfile P D R := by
  intro R hR
  exact BootstrapClosureBoundPackage.member_rigid P D X.data R hR

theorem GapClosurePackage.covers_preAdmissible_support
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S) :
    SupportProfile.mk S ∈ gapClosureFamily P D X := by
  exact BootstrapClosureBoundPackage.covers_preAdmissible_support P D X.data S hPre

theorem GapClosurePackage.covers_candidateProfile_of_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    {n : ℕ}
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n)) :
    candidateProfile n ∈ gapClosureFamily P D X := by
  exact BootstrapClosureBoundPackage.covers_candidateProfile_of_preAdmissible P D X.data hPre

theorem GapClosurePackage.delta_positive
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    0 < gapClosureDeltaValue P D X := by
  exact BootstrapClosureBoundPackage.delta_positive P D X.data

theorem GapClosurePackage.kmax_positive
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    0 < gapClosureKmaxValue P D X := by
  exact BootstrapClosureBoundPackage.kmax_positive P D X.data

theorem GapClosurePackage.bound_positive
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    0 < gapClosureBoundValue P D X := by
  exact BootstrapClosureBoundPackage.bound_positive P D X.data

theorem GapClosurePackage.omegahat_below_width
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegahatValue P D X < width P := by
  exact BootstrapClosureBoundPackage.omegahat_below_width P D X.data

theorem GapClosurePackage.omegahat_le_width
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegahatValue P D X ≤ width P := by
  exact BootstrapClosureBoundPackage.omegahat_le_width P D X.data

theorem GapClosurePackage.omegahat_matches_closureData
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X.data.data.data) :
    D.omegaHat = gapClosureOmegahatValue P D X := by
  exact BootstrapClosureBoundPackage.omegahat_matches_closureData P D X.data hMatch

theorem GapClosurePackage.member_within_closure_omega
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (R : SupportProfile)
    (hR : R ∈ gapClosureFamily P D X)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X.data.data.data) :
    SupportWithinOmega D.omegaHat (profileSupport R) := by
  exact BootstrapClosureBoundPackage.member_within_closure_omega
    P D X.data R hR hMatch

theorem GapClosurePackage.member_card_lt_width
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (R : SupportProfile)
    (hR : R ∈ gapClosureFamily P D X) :
    profileCard R < width P := by
  exact BootstrapClosureBoundPackage.member_card_lt_width P D X.data R hR

theorem GapClosurePackage.bound_at_least_cap
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    cap P D ≤ gapClosureBoundValue P D X := by
  exact BootstrapClosureBoundPackage.bound_atLeastCap P D X.data

theorem GapClosurePackage.bound_at_least_closureN
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    D.N ≤ gapClosureBoundValue P D X := by
  exact BootstrapClosureBoundPackage.bound_closureDataBelow P D X.data

theorem GapClosurePackage.delta_le_member_gap
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (R : SupportProfile)
    (hR : R ∈ gapClosureFamily P D X) :
    gapClosureDeltaValue P D X ≤
      profileRigidityGapValue P D R
        ((GapClosurePackage.member_rigid P D X) R hR) := by
  exact BootstrapClosureBoundPackage.delta_le_member_gap P D X.data R hR

theorem GapClosurePackage.member_index_le_kmax
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (R : SupportProfile)
    (hR : R ∈ gapClosureFamily P D X) :
    profileSupportIndex R ≤ gapClosureKmaxValue P D X := by
  exact BootstrapClosureBoundPackage.member_index_le_kmax P D X.data R hR

def GapClosureReady
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : Prop :=
  0 < gapClosureDeltaValue P D X ∧
  0 < gapClosureKmaxValue P D X ∧
  gapClosureOmegahatValue P D X < width P ∧
  0 < gapClosureBoundValue P D X ∧
  cap P D ≤ gapClosureBoundValue P D X ∧
  D.N ≤ gapClosureBoundValue P D X

@[simp] theorem GapClosureReady_def
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    GapClosureReady P D X =
      (0 < gapClosureDeltaValue P D X ∧
      0 < gapClosureKmaxValue P D X ∧
      gapClosureOmegahatValue P D X < width P ∧
      0 < gapClosureBoundValue P D X ∧
      cap P D ≤ gapClosureBoundValue P D X ∧
      D.N ≤ gapClosureBoundValue P D X) := rfl

theorem gapClosureReady
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    GapClosureReady P D X := by
  exact ⟨
    GapClosurePackage.delta_positive P D X,
    GapClosurePackage.kmax_positive P D X,
    GapClosurePackage.omegahat_below_width P D X,
    GapClosurePackage.bound_positive P D X,
    GapClosurePackage.bound_at_least_cap P D X,
    GapClosurePackage.bound_at_least_closureN P D X
  ⟩

theorem gapClosureFamily_nil_or_cons
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureFamily P D X =[] ∨
      ∃ R F, gapClosureFamily P D X = R :: F := by
  exact bootstrapClosureBoundFamily_nil_or_cons P D X.data

def gapClosureFromBootstrapBound
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : GapClosurePackage P D :=
  { data := X }

@[simp] theorem gapClosureFromBootstrapBound_data
    (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    (gapClosureFromBootstrapBound P D X).data = X := rfl

structure GapToClosureCompatibility
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D)
    (B : BootstrapClosureBoundPackage P D) : Prop where
  sameFamily :
    bootstrapClosureBoundFamily P D B = kmaxGapFamily P D K
  bootstrap_delta_eq :
    bootstrapClosureBoundDeltaValue P D B = kmaxGapPositiveValue P D K
  bootstrap_kmax_eq :
    bootstrapClosureBoundKmaxValue P D B = kmaxGapKmaxValue P D K
  bootstrap_bound_eq :
    bootstrapClosureBoundValue P D B = kmaxGapClosureCapValue P D K
  boundControlled :
    kmaxGapKmaxValue P D K ≤
      (bootstrapClosureBoundValue P D B : ℚ) *
        kmaxGapPositiveValue P D K

structure GapClosureRealizer
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D) where
  bootstrap : BootstrapClosureBoundPackage P D
  compatible : GapToClosureCompatibility P D K bootstrap

def hasGapClosureRealizer
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D) : Prop :=
  Nonempty (GapClosureRealizer P D K)

@[simp] theorem hasGapClosureRealizer_def
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D) :
    hasGapClosureRealizer P D K =
      Nonempty (GapClosureRealizer P D K) := rfl

def gapClosureOfRealizer
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D)
    (B : GapClosureRealizer P D K) :
    GapClosurePackage P D :=
  { data := B.bootstrap }

@[simp] theorem gapClosureOfRealizer_data
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D)
    (B : GapClosureRealizer P D K) :
    (gapClosureOfRealizer P D K B).data = B.bootstrap := rfl

def gapClosureFromKmaxGap
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D)
    (B : GapClosureRealizer P D K) :
    GapClosurePackage P D :=
  gapClosureOfRealizer P D K B

@[simp] theorem gapClosureFromKmaxGap_data
    (P : Params) (D : ClosureData P)
    (K : KmaxGapPackage P D)
    (B : GapClosureRealizer P D K) :
    (gapClosureFromKmaxGap P D K B).data = B.bootstrap := rfl

structure GapToClosurePackage
    (P : Params) (D : ClosureData P) where
  kmaxGap : KmaxGapPackage P D
  realizer : GapClosureRealizer P D kmaxGap

def GapToClosurePackage.gap
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) : GapClosurePackage P D :=
  { data := X.realizer.bootstrap }

@[simp] theorem GapToClosurePackage.gap_def
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    X.gap P D = { data := X.realizer.bootstrap } := rfl

@[simp] theorem GapToClosurePackage.gap_data
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    (X.gap P D).data = X.realizer.bootstrap := rfl

theorem GapToClosurePackage.gap_family_eq_kmax_family
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    gapClosureFamily P D (X.gap P D) =
      kmaxGapFamily P D X.kmaxGap := by
  exact X.realizer.compatible.sameFamily

theorem GapToClosurePackage.gap_delta_eq_kmax_delta
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    gapClosureDeltaValue P D (X.gap P D) =
      kmaxGapPositiveValue P D X.kmaxGap := by
  exact X.realizer.compatible.bootstrap_delta_eq

theorem GapToClosurePackage.gap_kmax_eq_kmax_gap
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    gapClosureKmaxValue P D (X.gap P D) =
      kmaxGapKmaxValue P D X.kmaxGap := by
  exact X.realizer.compatible.bootstrap_kmax_eq

theorem GapToClosurePackage.gap_bound_eq_kmax_cap
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    gapClosureBoundValue P D (X.gap P D) =
      kmaxGapClosureCapValue P D X.kmaxGap := by
  exact X.realizer.compatible.bootstrap_bound_eq

theorem GapToClosurePackage.gap_kmax_controlled
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    kmaxGapKmaxValue P D X.kmaxGap ≤
      (gapClosureBoundValue P D (X.gap P D) : ℚ) *
        gapClosureDeltaValue P D (X.gap P D) := by
  change kmaxGapKmaxValue P D X.kmaxGap ≤
    (bootstrapClosureBoundValue P D X.realizer.bootstrap : ℚ) *
      bootstrapClosureBoundDeltaValue P D X.realizer.bootstrap
  rw[X.realizer.compatible.bootstrap_delta_eq]
  exact X.realizer.compatible.boundControlled

def GapToClosureReady
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) : Prop :=
  GapClosureReady P D (X.gap P D) ∧
  kmaxGapKmaxValue P D X.kmaxGap ≤
    (gapClosureBoundValue P D (X.gap P D) : ℚ) *
      gapClosureDeltaValue P D (X.gap P D)

@[simp] theorem GapToClosureReady_def
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    GapToClosureReady P D X =
      (GapClosureReady P D (X.gap P D) ∧
      kmaxGapKmaxValue P D X.kmaxGap ≤
        (gapClosureBoundValue P D (X.gap P D) : ℚ) *
          gapClosureDeltaValue P D (X.gap P D)) := rfl

theorem gapToClosureReady
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    GapToClosureReady P D X := by
  exact ⟨
    gapClosureReady P D (X.gap P D),
    GapToClosurePackage.gap_kmax_controlled P D X
  ⟩

theorem GapToClosurePackage.gap_bound_atLeastCap
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    cap P D ≤ gapClosureBoundValue P D (X.gap P D) := by
  exact GapClosurePackage.bound_at_least_cap P D (X.gap P D)

theorem GapToClosurePackage.gap_bound_atLeastClosureN
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    D.N ≤ gapClosureBoundValue P D (X.gap P D) := by
  exact GapClosurePackage.bound_at_least_closureN P D (X.gap P D)

theorem GapToClosurePackage.gap_omegahat_lt_width
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    gapClosureOmegahatValue P D (X.gap P D) < width P := by
  exact GapClosurePackage.omegahat_below_width P D (X.gap P D)

theorem GapToClosurePackage.gap_member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D (X.gap P D) →
        Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_preAdmissible P D (X.gap P D) R hR

theorem GapToClosurePackage.gap_member_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D (X.gap P D) →
        Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_admissibleAtLevel P D (X.gap P D) R hR

theorem GapToClosurePackage.gap_member_locksB
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D (X.gap P D) →
        Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_locksB P D (X.gap P D) R hR

theorem GapToClosurePackage.gap_member_truncated
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D (X.gap P D) →
        ProfileInTruncatedFamily P D R := by
  intro R hR
  exact GapClosurePackage.member_truncated P D (X.gap P D) R hR

def GapToClosurePackage.gap_member_rigid
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D (X.gap P D) →
        RigidProfile P D R := by
  intro R hR
  exact GapClosurePackage.member_rigid P D (X.gap P D) R hR

theorem GapToClosurePackage.gap_covers_preAdmissible_support
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ S : Support,
      Certificate.PreCaseCAdmissibleSupport P D S →
        SupportProfile.mk S ∈ gapClosureFamily P D (X.gap P D) := by
  intro S hPre
  exact GapClosurePackage.covers_preAdmissible_support P D (X.gap P D) S hPre

theorem GapToClosurePackage.gap_member_within_closure_omega
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D)
    (hMatch :
      truncatedGapOmegahatMatchesClosureData
        P D (X.gap P D).data.data.data) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D (X.gap P D) →
        SupportWithinOmega D.omegaHat (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_within_closure_omega
    P D (X.gap P D) R hR hMatch

theorem GapToClosurePackage.gap_delta_positive
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    0 < gapClosureDeltaValue P D (X.gap P D) := by
  exact GapClosurePackage.delta_positive P D (X.gap P D)

theorem GapToClosurePackage.gap_kmax_positive
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    0 < gapClosureKmaxValue P D (X.gap P D) := by
  exact GapClosurePackage.kmax_positive P D (X.gap P D)

theorem GapToClosurePackage.gap_bound_positive
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    0 < gapClosureBoundValue P D (X.gap P D) := by
  exact GapClosurePackage.bound_positive P D (X.gap P D)

theorem GapToClosurePackage.gap_member_index_le_kmax
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D (X.gap P D) →
        profileSupportIndex R ≤ gapClosureKmaxValue P D (X.gap P D) := by
  intro R hR
  exact GapClosurePackage.member_index_le_kmax P D (X.gap P D) R hR

theorem GapToClosurePackage.gap_delta_le_member_gap
    (P : Params) (D : ClosureData P)
    (X : GapToClosurePackage P D) :
    ∀ R : SupportProfile,
      (hR : R ∈ gapClosureFamily P D (X.gap P D)) →
        gapClosureDeltaValue P D (X.gap P D) ≤
          profileRigidityGapValue P D R
            ((GapClosurePackage.member_rigid P D (X.gap P D)) R hR) := by
  intro R hR
  exact GapClosurePackage.delta_le_member_gap P D (X.gap P D) R hR

theorem gapClosure_delta_positive
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    0 < gapClosureDeltaValue P D X := by
  exact GapClosurePackage.delta_positive P D X

theorem gapClosure_kmax_positive
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    0 < gapClosureKmaxValue P D X := by
  exact GapClosurePackage.kmax_positive P D X

theorem gapClosure_bound_positive
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    0 < gapClosureBoundValue P D X := by
  exact GapClosurePackage.bound_positive P D X

theorem gapClosure_omega_lt_width
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegahatValue P D X < width P := by
  exact GapClosurePackage.omegahat_below_width P D X

theorem gapClosure_member_within_closure_omega
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (hMatch : truncatedGapOmegahatMatchesClosureData P D X.data.data.data) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        SupportWithinOmega D.omegaHat (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_within_closure_omega P D X R hR hMatch

theorem gapClosure_member_truncated_readable
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        ProfileInTruncatedFamily P D R := by
  intro R hR
  exact GapClosurePackage.member_truncated P D X R hR

def gapClosure_member_rigid_readable
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        RigidProfile P D R := by
  intro R hR
  exact GapClosurePackage.member_rigid P D X R hR

theorem gapClosure_member_preAdmissible_readable
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_preAdmissible P D X R hR

theorem gapClosure_member_admissibleAtLevel_readable
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_admissibleAtLevel P D X R hR

theorem gapClosure_member_locksB_readable
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R : SupportProfile,
      R ∈ gapClosureFamily P D X →
        Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact GapClosurePackage.member_locksB P D X R hR

theorem gapClosure_bootstrap_readable
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    BootstrapCondition P D X.data.data.data := by
  exact GapClosurePackage.bootstrap_holds P D X

theorem gapClosure_omegahat_readable
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegahatValue P D X < width P := by
  exact GapClosurePackage.omegahat_below_width P D X

theorem gapClosure_family_agrees_with_data
    (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D)
    (_hMatch : truncatedGapOmegahatMatchesClosureData P D X.data.data.data) :
    ∀ R : SupportProfile,
      (_hR : R ∈ gapClosureFamily P D X) →
        SupportBelow D.N (profileSupport R) ∧
          SupportWithinOmega D.omegaHat (profileSupport R) := by
  intro R _hR
  exact (profileInTruncatedFamily_iff P D R).mp
    (GapClosurePackage.member_truncated P D X R _hR)

end GapClosure
end CaseC
end Lehmer