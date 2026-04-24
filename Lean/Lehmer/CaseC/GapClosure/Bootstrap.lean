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

def BootstrapCondition (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) : Prop :=
  truncatedGapOmegahatBelowWidth P D X

@[simp] theorem BootstrapCondition_def (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    BootstrapCondition P D X = truncatedGapOmegahatBelowWidth P D X := rfl

theorem bootstrapCondition_iff (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    BootstrapCondition P D X ↔ truncatedGapOmegahatBelowWidth P D X := by
  rfl

structure BootstrapPackage (P : Params) (D : ClosureData P) where
  data : TruncatedGapPackage P D
  bootstrap : BootstrapCondition P D data

@[simp] theorem BootstrapPackage.data_mk (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) (hX : BootstrapCondition P D X) :
    (BootstrapPackage.mk X hX).data = X := rfl

@[simp] theorem BootstrapPackage.bootstrap_mk (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) (hX : BootstrapCondition P D X) :
    (BootstrapPackage.mk X hX).bootstrap = hX := rfl

def bootstrapFamily (P : Params) (D : ClosureData P) (X : BootstrapPackage P D) :
    SupportProfileFamily :=
  X.data.family

@[simp] theorem bootstrapFamily_def (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapFamily P D X = X.data.family := rfl

def bootstrapDeltaValue (P : Params) (D : ClosureData P) (X : BootstrapPackage P D) : ℕ :=
  deltaStarValue P D X.data.delta

@[simp] theorem bootstrapDeltaValue_def (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapDeltaValue P D X = deltaStarValue P D X.data.delta := rfl

def bootstrapOmegahatValue (P : Params) (D : ClosureData P) (X : BootstrapPackage P D) : ℕ :=
  omegahatValue P D X.data.omegaHat

@[simp] theorem bootstrapOmegahatValue_def (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapOmegahatValue P D X = omegahatValue P D X.data.omegaHat := rfl

def bootstrapHead? (P : Params) (D : ClosureData P) (X : BootstrapPackage P D) :
    Option SupportProfile :=
  truncatedGapHead? P D X.data

@[simp] theorem bootstrapHead?_def (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    bootstrapHead? P D X = truncatedGapHead? P D X.data := rfl

theorem BootstrapPackage.bootstrap_holds (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    BootstrapCondition P D X.data := X.bootstrap

theorem BootstrapPackage.member_truncated (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    ∀ R, R ∈ X.data.family → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact truncatedGapPackage_member_truncated P D X.data R hR

theorem BootstrapPackage.member_rigid (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    ∀ R, R ∈ X.data.family → RigidProfile P D R := by
  intro R hR
  exact truncatedGapPackage_member_rigid P D X.data R hR

theorem BootstrapPackage.family_nil_or_cons (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    X.data.family = [] ∨ ∃ R F, X.data.family = R :: F := by
  exact truncatedGapFamily_nil_or_cons P D X.data

@[simp] theorem bootstrapHead?_nil (P : Params) (D : ClosureData P)
    (hT : IsTruncatedFamily P D []) (hR : RigidProfileFamily P D [])
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk [] hT hR δ ω)) :
    bootstrapHead? P D (BootstrapPackage.mk (TruncatedGapPackage.mk [] hT hR δ ω) hB) = none := rfl

@[simp] theorem bootstrapHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω)) :
    bootstrapHead? P D (BootstrapPackage.mk (TruncatedGapPackage.mk (R :: F) hT hR δ ω) hB) = some R := rfl

theorem BootstrapPackage.head_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (_hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω)) :
    ProfileInTruncatedFamily P D R := by
  exact truncatedGapHead_truncated P D R F hT hR δ ω

theorem BootstrapPackage.head_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (_hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω)) :
    RigidProfile P D R := by
  exact truncatedGapHead_rigid P D R F hT hR δ ω

theorem BootstrapPackage.tail_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (_hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω)) :
    IsTruncatedFamily P D F := by
  exact truncatedGapTail_truncated P D R F hT hR δ ω

theorem BootstrapPackage.tail_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (_hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω)) :
    RigidProfileFamily P D F := by
  exact truncatedGapTail_rigid P D R F hT hR δ ω

theorem BootstrapPackage.omegahat_below_width (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) :
    OmegahatBelowWidth P D X.data.omegaHat := by
  exact X.bootstrap

theorem bootstrapCondition_or_not (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    BootstrapCondition P D X ∨ ¬ BootstrapCondition P D X := by
  exact Classical.em _

theorem bootstrapPackage_or_not (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) :
    (∃ Y : BootstrapPackage P D, Y.data = X) ∨
      ¬ BootstrapCondition P D X := by
  by_cases h : BootstrapCondition P D X
  · left
    exact ⟨BootstrapPackage.mk X h, rfl⟩
  · right
    exact h

def bootstrapFromTruncatedGap (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) (hX : BootstrapCondition P D X) :
    BootstrapPackage P D :=
  BootstrapPackage.mk X hX

@[simp] theorem bootstrapFromTruncatedGap_data (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) (hX : BootstrapCondition P D X) :
    (bootstrapFromTruncatedGap P D X hX).data = X := rfl

@[simp] theorem bootstrapFromTruncatedGap_bootstrap (P : Params) (D : ClosureData P)
    (X : TruncatedGapPackage P D) (hX : BootstrapCondition P D X) :
    (bootstrapFromTruncatedGap P D X hX).bootstrap = hX := rfl

end GapClosure
end CaseC
end Lehmer