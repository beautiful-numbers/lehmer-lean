-- FILE: Lean/Lehmer/CaseC/GapClosure/Rigidity.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def RigidProfile (P : Params) (D : ClosureData P) (R : SupportProfile) : Prop :=
  ProfileInTruncatedFamily P D R

@[simp] theorem RigidProfile_def (P : Params) (D : ClosureData P) (R : SupportProfile) :
    RigidProfile P D R = ProfileInTruncatedFamily P D R := rfl

theorem rigidProfile_iff (P : Params) (D : ClosureData P) (R : SupportProfile) :
    RigidProfile P D R ↔
      ProfileBelow D.N R ∧ ProfileWithinOmega D.omegaHat R := by
  rfl

@[simp] theorem RigidProfile_mk (P : Params) (D : ClosureData P) (S : Support) :
    RigidProfile P D (SupportProfile.mk S) ↔
      SupportBelow D.N S ∧ SupportWithinOmega D.omegaHat S := by
  rfl

theorem rigidProfile_below (P : Params) (D : ClosureData P) (R : SupportProfile) :
    RigidProfile P D R → ProfileBelow D.N R := by
  intro h
  exact (rigidProfile_iff P D R).mp h |>.1

theorem rigidProfile_withinOmega (P : Params) (D : ClosureData P) (R : SupportProfile) :
    RigidProfile P D R → ProfileWithinOmega D.omegaHat R := by
  intro h
  exact (rigidProfile_iff P D R).mp h |>.2

theorem rigidProfile_intro (P : Params) (D : ClosureData P) (R : SupportProfile) :
    ProfileBelow D.N R → ProfileWithinOmega D.omegaHat R → RigidProfile P D R := by
  intro hBelow hOmega
  exact (rigidProfile_iff P D R).mpr ⟨hBelow, hOmega⟩

theorem rigidProfile_of_support_eq (P : Params) (D : ClosureData P) {R T : SupportProfile} :
    profileSupport R = profileSupport T →
    RigidProfile P D R →
    RigidProfile P D T := by
  intro hRT hR
  exact profileInTruncatedFamily_of_support_eq P D hRT hR

theorem rigidProfile_iff_of_support_eq (P : Params) (D : ClosureData P) {R T : SupportProfile} :
    profileSupport R = profileSupport T →
    (RigidProfile P D R ↔ RigidProfile P D T) := by
  intro hRT
  exact profileInTruncatedFamily_iff_of_support_eq P D hRT

def RigidProfileFamily (P : Params) (D : ClosureData P) (F : SupportProfileFamily) : Prop :=
  FamilyAllInTruncatedFamily P D F

@[simp] theorem RigidProfileFamily_def (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    RigidProfileFamily P D F = FamilyAllInTruncatedFamily P D F := rfl

theorem rigidProfileFamily_iff (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    RigidProfileFamily P D F ↔ ∀ R ∈ F, RigidProfile P D R := by
  rfl

@[simp] theorem rigidProfileFamily_nil (P : Params) (D : ClosureData P) :
    RigidProfileFamily P D [] := by
  exact FamilyAllInTruncatedFamily_nil P D

theorem rigidProfileFamily_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfileFamily P D (R :: F) ↔
      RigidProfile P D R ∧ RigidProfileFamily P D F := by
  exact FamilyAllInTruncatedFamily_cons P D R F

theorem rigidProfileFamily_head (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfileFamily P D (R :: F) → RigidProfile P D R := by
  intro h
  exact (rigidProfileFamily_cons P D R F).mp h |>.1

theorem rigidProfileFamily_tail (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfileFamily P D (R :: F) → RigidProfileFamily P D F := by
  intro h
  exact (rigidProfileFamily_cons P D R F).mp h |>.2

theorem rigidProfileFamily_cons_intro (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfile P D R →
    RigidProfileFamily P D F →
    RigidProfileFamily P D (R :: F) := by
  intro hR hF
  exact (rigidProfileFamily_cons P D R F).mpr ⟨hR, hF⟩

theorem rigidProfileFamily_pointwise (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    RigidProfileFamily P D F → ∀ R ∈ F, RigidProfile P D R := by
  intro h
  exact (rigidProfileFamily_iff P D F).mp h

theorem rigidProfileFamily_of_pointwise (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    (∀ R ∈ F, RigidProfile P D R) → RigidProfileFamily P D F := by
  intro h
  exact (rigidProfileFamily_iff P D F).mpr h

def rigidFamilyHead? (P : Params) (_D : ClosureData P) (F : SupportProfileFamily) : Option SupportProfile :=
  familyHead? F

@[simp] theorem rigidFamilyHead?_def (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    rigidFamilyHead? P D F = familyHead? F := rfl

@[simp] theorem rigidFamilyHead?_nil (P : Params) (D : ClosureData P) :
    rigidFamilyHead? P D [] = none := rfl

@[simp] theorem rigidFamilyHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    rigidFamilyHead? P D (R :: F) = some R := rfl

theorem rigidFamily_exhaustive (F : SupportProfileFamily) :
    F = [] ∨ ∃ R G, F = R :: G := by
  exact supportProfileFamily_exhaustive F

theorem rigidProfileFamily_head_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfileFamily P D (R :: F) → RigidProfile P D R := by
  exact rigidProfileFamily_head P D R F

theorem rigidProfileFamily_mem (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    RigidProfileFamily P D F → ∀ R, R ∈ F → RigidProfile P D R := by
  intro hF R hR
  exact rigidProfileFamily_pointwise P D F hF R hR

structure RigidPackage (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  rigid : RigidProfileFamily P D family

@[simp] theorem RigidPackage.family_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (h : RigidProfileFamily P D F) :
    (RigidPackage.mk F h).family = F := rfl

@[simp] theorem RigidPackage.rigid_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (h : RigidProfileFamily P D F) :
    (RigidPackage.mk F h).rigid = h := rfl

def rigidPackageHead? (P : Params) (D : ClosureData P) (X : RigidPackage P D) : Option SupportProfile :=
  familyHead? X.family

@[simp] theorem rigidPackageHead?_def (P : Params) (D : ClosureData P) (X : RigidPackage P D) :
    rigidPackageHead? P D X = familyHead? X.family := rfl

theorem rigidPackage_member_rigid (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact rigidProfileFamily_mem P D X.family X.rigid R hR

end GapClosure
end CaseC
end Lehmer