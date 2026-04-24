-- FILE: Lean/Lehmer/CaseC/GapClosure/TruncatedFamily.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
- Lehmer.CaseC.GapClosure.Omegahat : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.DeltaStar
import Lehmer.CaseC.GapClosure.Omegahat

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def IsTruncatedFamily (P : Params) (D : ClosureData P) (F : SupportProfileFamily) : Prop :=
  FamilyAllInTruncatedFamily P D F

@[simp] theorem IsTruncatedFamily_def (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    IsTruncatedFamily P D F = FamilyAllInTruncatedFamily P D F := rfl

theorem isTruncatedFamily_iff (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    IsTruncatedFamily P D F ↔ ∀ R ∈ F, ProfileInTruncatedFamily P D R := by
  rfl

theorem isTruncatedFamily_nil (P : Params) (D : ClosureData P) :
    IsTruncatedFamily P D [] := by
  exact FamilyAllInTruncatedFamily_nil P D

theorem isTruncatedFamily_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    IsTruncatedFamily P D (R :: F) ↔
      ProfileInTruncatedFamily P D R ∧ IsTruncatedFamily P D F := by
  exact FamilyAllInTruncatedFamily_cons P D R F

theorem isTruncatedFamily_mem (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    IsTruncatedFamily P D F → ∀ R, R ∈ F → ProfileInTruncatedFamily P D R := by
  intro hF R hR
  exact (isTruncatedFamily_iff P D F).mp hF R hR

theorem isTruncatedFamily_of_pointwise (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    (∀ R ∈ F, ProfileInTruncatedFamily P D R) → IsTruncatedFamily P D F := by
  intro h
  exact (isTruncatedFamily_iff P D F).mpr h

structure TruncatedFamily (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  truncated : IsTruncatedFamily P D family

@[simp] theorem TruncatedFamily.family_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : IsTruncatedFamily P D F) :
    (TruncatedFamily.mk F hF).family = F := rfl

@[simp] theorem TruncatedFamily.truncated_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : IsTruncatedFamily P D F) :
    (TruncatedFamily.mk F hF).truncated = hF := rfl

def truncatedFamilyProfiles (P : Params) (D : ClosureData P) (X : TruncatedFamily P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem truncatedFamilyProfiles_def (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    truncatedFamilyProfiles P D X = X.family := rfl

def truncatedFamilyHead? (P : Params) (D : ClosureData P) (X : TruncatedFamily P D) :
    Option SupportProfile :=
  familyHead? X.family

@[simp] theorem truncatedFamilyHead?_def (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    truncatedFamilyHead? P D X = familyHead? X.family := rfl

def truncatedFamilyMember (P : Params) (D : ClosureData P)
    (R : SupportProfile) (X : TruncatedFamily P D) : Prop :=
  R ∈ X.family

@[simp] theorem truncatedFamilyMember_def (P : Params) (D : ClosureData P)
    (R : SupportProfile) (X : TruncatedFamily P D) :
    truncatedFamilyMember P D R X = (R ∈ X.family) := rfl

theorem truncatedFamily_member_truncated (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    ∀ R, truncatedFamilyMember P D R X → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact isTruncatedFamily_mem P D X.family X.truncated R hR

theorem truncatedFamily_nil_or_cons (P : Params) (D : ClosureData P)
    (X : TruncatedFamily P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact supportProfileFamily_exhaustive X.family

@[simp] theorem truncatedFamilyHead?_nil (P : Params) (D : ClosureData P)
    (hF : IsTruncatedFamily P D []) :
    truncatedFamilyHead? P D (TruncatedFamily.mk [] hF) = none := rfl

@[simp] theorem truncatedFamilyHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    truncatedFamilyHead? P D (TruncatedFamily.mk (R :: F) hF) = some R := rfl

theorem truncatedFamily_head_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    ProfileInTruncatedFamily P D R := by
  exact (isTruncatedFamily_cons P D R F).mp hF |>.1

theorem truncatedFamily_tail_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : IsTruncatedFamily P D (R :: F)) :
    IsTruncatedFamily P D F := by
  exact (isTruncatedFamily_cons P D R F).mp hF |>.2

structure TruncatedGapPackage (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  truncated : IsTruncatedFamily P D family
  rigid : RigidProfileFamily P D family
  delta : DeltaStarData P D
  omegaHat : OmegahatData P D

@[simp] theorem TruncatedGapPackage.family_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (TruncatedGapPackage.mk F hT hR δ ω).family = F := rfl

@[simp] theorem TruncatedGapPackage.truncated_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (TruncatedGapPackage.mk F hT hR δ ω).truncated = hT := rfl

@[simp] theorem TruncatedGapPackage.rigid_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (TruncatedGapPackage.mk F hT hR δ ω).rigid = hR := rfl

@[simp] theorem TruncatedGapPackage.delta_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    (TruncatedGapPackage.mk F hT hR δ _ω).delta = δ := rfl

@[simp] theorem TruncatedGapPackage.omegaHat_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hT : IsTruncatedFamily P D F)
    (hR : RigidProfileFamily P D F)
    (_δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (TruncatedGapPackage.mk F hT hR _δ ω).omegaHat = ω := rfl

def truncatedGapFamily (P : Params) (D : ClosureData P) (X : TruncatedGapPackage P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem truncatedGapFamily_def (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapFamily P D X = X.family := rfl

def truncatedGapHead? (P : Params) (D : ClosureData P) (X : TruncatedGapPackage P D) :
    Option SupportProfile :=
  familyHead? X.family

@[simp] theorem truncatedGapHead?_def (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapHead? P D X = familyHead? X.family := rfl

def truncatedGapDeltaValue (P : Params) (D : ClosureData P) (X : TruncatedGapPackage P D) : ℕ :=
  deltaStarValue P D X.delta

@[simp] theorem truncatedGapDeltaValue_def (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapDeltaValue P D X = deltaStarValue P D X.delta := rfl

def truncatedGapOmegahatValue (P : Params) (D : ClosureData P) (X : TruncatedGapPackage P D) : ℕ :=
  omegahatValue P D X.omegaHat

@[simp] theorem truncatedGapOmegahatValue_def (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapOmegahatValue P D X = omegahatValue P D X.omegaHat := rfl

def truncatedGapOmegahatBelowWidth (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : Prop :=
  OmegahatBelowWidth P D X.omegaHat

@[simp] theorem truncatedGapOmegahatBelowWidth_def (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapOmegahatBelowWidth P D X = OmegahatBelowWidth P D X.omegaHat := rfl

theorem truncatedGapPackage_member_truncated (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    ∀ R, R ∈ X.family → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact isTruncatedFamily_mem P D X.family X.truncated R hR

theorem truncatedGapPackage_member_rigid (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact rigidProfileFamily_mem P D X.family X.rigid R hR

theorem truncatedGapFamily_nil_or_cons (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact supportProfileFamily_exhaustive X.family

@[simp] theorem truncatedGapHead?_nil (P : Params) (D : ClosureData P)
    (hT : IsTruncatedFamily P D []) (_hR : RigidProfileFamily P D [])
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    truncatedGapHead? P D (TruncatedGapPackage.mk [] hT _hR _δ _ω) = none := rfl

@[simp] theorem truncatedGapHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (_hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    truncatedGapHead? P D (TruncatedGapPackage.mk (R :: F) hT _hR _δ _ω) = some R := rfl

theorem truncatedGapHead_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (_hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    ProfileInTruncatedFamily P D R := by
  exact (isTruncatedFamily_cons P D R F).mp hT |>.1

theorem truncatedGapHead_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (_hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    RigidProfile P D R := by
  exact rigidProfileFamily_head P D R F hR

theorem truncatedGapTail_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (_hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    IsTruncatedFamily P D F := by
  exact (isTruncatedFamily_cons P D R F).mp hT |>.2

theorem truncatedGapTail_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (_hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    RigidProfileFamily P D F := by
  exact rigidProfileFamily_tail P D R F hR

theorem truncatedGapPackage_omegahatBelowWidth_or_not (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    truncatedGapOmegahatBelowWidth P D X ∨ ¬ truncatedGapOmegahatBelowWidth P D X := by
  exact Classical.em _

end GapClosure
end CaseC
end Lehmer