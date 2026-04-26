-- FILE: Lean/Lehmer/CaseC/GapClosure/DeltaStar.lean

/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def rigidProfileFamily_cons_split
    (P : Params) (D : ClosureData P) (R : SupportProfile) (F : SupportProfileFamily)
    (hRF : RigidProfileFamily P D (R :: F)) :
    RigidProfile P D R × RigidProfileFamily P D F :=
  (hRF R (by simp), fun S hS => hRF S (by simp [hS]))

def profileRigidityGapValue
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) : ℚ :=
  H.gapValue P D R

@[simp] theorem profileRigidityGapValue_def
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    profileRigidityGapValue P D R H = H.gapValue P D R := rfl

theorem profileRigidityGapValue_pos
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    0 < profileRigidityGapValue P D R H := by
  exact H.gapPositive P D R

structure DeltaStarData
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F) where
  value : ℚ
  positive : 0 < value
  lowerBound :
    ∀ R : SupportProfile, ∀ hR : R ∈ F,
      value ≤ profileRigidityGapValue P D R (hF R hR)

def deltaStarValue
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) : ℚ :=
  δ.value

@[simp] theorem deltaStarValue_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    deltaStarValue P D F hF δ = δ.value := rfl

def PositiveDeltaStar
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) : Prop :=
  0 < deltaStarValue P D F hF δ

@[simp] theorem PositiveDeltaStar_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    PositiveDeltaStar P D F hF δ =
      (0 < deltaStarValue P D F hF δ) := rfl

theorem deltaStar_positive
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    0 < deltaStarValue P D F hF δ := by
  exact δ.positive

theorem deltaStar_le_profile_gap
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF)
    (R : SupportProfile)
    (hR : R ∈ F) :
    deltaStarValue P D F hF δ ≤
      profileRigidityGapValue P D R (hF R hR) := by
  exact δ.lowerBound R hR

noncomputable def deltaStarData_nil
    (P : Params) (D : ClosureData P)
    (hF : RigidProfileFamily P D []) :
    DeltaStarData P D [] hF :=
  { value := 1
    positive := by norm_num
    lowerBound := by
      intro R hR
      simp at hR }

noncomputable def deltaStarData_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (F : SupportProfileFamily)
    (hRF : RigidProfileFamily P D (R :: F))
    (δF : DeltaStarData P D F (rigidProfileFamily_cons_split P D R F hRF).2) :
    DeltaStarData P D (R :: F) hRF :=
  let hSplit := rigidProfileFamily_cons_split P D R F hRF
  { value :=
      min
        (profileRigidityGapValue P D R hSplit.1)
        (deltaStarValue P D F hSplit.2 δF)
    positive := by
      exact lt_min
        (profileRigidityGapValue_pos P D R hSplit.1)
        (deltaStar_positive P D F hSplit.2 δF)
    lowerBound := by
      intro T hT
      rcases List.mem_cons.mp hT with hHead | hTail
      · subst hHead
        exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (deltaStar_le_profile_gap P D F hSplit.2 δF T hTail) }

/-- 
  Construction récursive de DeltaStarData. 
  L'utilisation du filtrage par motif (match) remplace l'induction tactique 
  pour éviter les problèmes de portée des identifiants (R, F).
-/
noncomputable def deltaStarData_of_rigidFamily
    (P : Params) (D : ClosureData P) :
    ∀ (F : SupportProfileFamily) (hF : RigidProfileFamily P D F), DeltaStarData P D F hF
  | [], hF => deltaStarData_nil P D hF
  | R :: F, hF =>
      let hSplit := rigidProfileFamily_cons_split P D R F hF
      deltaStarData_cons P D R F hF (deltaStarData_of_rigidFamily P D F hSplit.2)

structure RigidDeltaStarPackage
    (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  rigid : RigidProfileFamily P D family
  delta : DeltaStarData P D family rigid

@[simp] theorem RigidDeltaStarPackage.family_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    (RigidDeltaStarPackage.mk F hF δ).family = F := rfl

@[simp] theorem RigidDeltaStarPackage.rigid_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    (RigidDeltaStarPackage.mk F hF δ).rigid = hF := rfl

@[simp] theorem RigidDeltaStarPackage.delta_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    (RigidDeltaStarPackage.mk F hF δ).delta = δ := rfl

def rigidDeltaStarFamily
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem rigidDeltaStarFamily_def
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarFamily P D X = X.family := rfl

def rigidDeltaStarValue
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) : ℚ :=
  deltaStarValue P D X.family X.rigid X.delta

@[simp] theorem rigidDeltaStarValue_def
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarValue P D X =
      deltaStarValue P D X.family X.rigid X.delta := rfl

def rigidDeltaStarPositive
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) : Prop :=
  PositiveDeltaStar P D X.family X.rigid X.delta

@[simp] theorem rigidDeltaStarPositive_def
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarPositive P D X =
      PositiveDeltaStar P D X.family X.rigid X.delta := rfl

theorem rigidDeltaStar_positive
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    0 < rigidDeltaStarValue P D X := by
  exact X.delta.positive

theorem rigidDeltaStar_le_member_gap
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D)
    (R : SupportProfile)
    (hR : R ∈ X.family) :
    rigidDeltaStarValue P D X ≤
      profileRigidityGapValue P D R (X.rigid R hR) := by
  exact X.delta.lowerBound R hR

noncomputable def mkRigidDeltaStarPackage
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F) :
    RigidDeltaStarPackage P D :=
  { family := F
    rigid := hF
    delta := deltaStarData_of_rigidFamily P D F hF }

@[simp] theorem mkRigidDeltaStarPackage_family
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F) :
    (mkRigidDeltaStarPackage P D F hF).family = F := rfl

@[simp] theorem mkRigidDeltaStarPackage_rigid
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F) :
    (mkRigidDeltaStarPackage P D F hF).rigid = hF := rfl

def rigidDeltaStarPackage_member_rigid
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    ∀ (R : SupportProfile), R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact X.rigid R hR

def rigidDeltaStarHead?
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) : Option SupportProfile :=
  familyHead? X.family

@[simp] theorem rigidDeltaStarHead?_def
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarHead? P D X = familyHead? X.family := rfl

theorem rigidDeltaStarFamily_nil_or_cons
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact supportProfileFamily_exhaustive X.family

@[simp] theorem rigidDeltaStarHead?_nil
    (P : Params) (D : ClosureData P)
    (hF : RigidProfileFamily P D [])
    (δ : DeltaStarData P D [] hF) :
    rigidDeltaStarHead? P D (RigidDeltaStarPackage.mk [] hF δ) = none := rfl

@[simp] theorem rigidDeltaStarHead?_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D (R :: F) hF) :
    rigidDeltaStarHead? P D (RigidDeltaStarPackage.mk (R :: F) hF δ) = some R := rfl

def rigidDeltaStarHead_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) hF) :
    RigidProfile P D R := by
  exact rigidProfileFamily_head P D R F hF

def rigidDeltaStarTail_rigid
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D (R :: F) hF) :
    RigidProfileFamily P D F := by
  exact rigidProfileFamily_tail P D R F hF

theorem rigidDeltaStarPackage_member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    ∀ (R : SupportProfile), R ∈ X.family →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact RigidProfile.preAdmissible P D R (X.rigid R hR)

theorem rigidDeltaStarPackage_member_truncated
    (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    ∀ (R : SupportProfile), R ∈ X.family →
      ProfileInTruncatedFamily P D R := by
  intro R hR
  exact RigidProfile.in_truncated P D R (X.rigid R hR)

end GapClosure
end CaseC
end Lehmer