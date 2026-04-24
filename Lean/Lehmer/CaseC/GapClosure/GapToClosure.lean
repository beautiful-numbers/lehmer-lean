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

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure GapClosurePackage (P : Params) (D : ClosureData P) where
  data : BootstrapClosureBoundPackage P D

@[simp] theorem GapClosurePackage.data_mk (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    (GapClosurePackage.mk X).data = X := rfl

def gapClosureFamily (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : SupportProfileFamily :=
  bootstrapClosureBoundFamily P D X.data

@[simp] theorem gapClosureFamily_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureFamily P D X = bootstrapClosureBoundFamily P D X.data := rfl

def gapClosureDeltaValue (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : ℕ :=
  bootstrapClosureBoundDeltaValue P D X.data

@[simp] theorem gapClosureDeltaValue_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureDeltaValue P D X = bootstrapClosureBoundDeltaValue P D X.data := rfl

def gapClosureOmegahatValue (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : ℕ :=
  bootstrapClosureBoundOmegahatValue P D X.data

@[simp] theorem gapClosureOmegahatValue_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegahatValue P D X = bootstrapClosureBoundOmegahatValue P D X.data := rfl

def gapClosureBoundValue (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : ℕ :=
  bootstrapClosureBoundValue P D X.data

@[simp] theorem gapClosureBoundValue_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureBoundValue P D X = bootstrapClosureBoundValue P D X.data := rfl

def gapClosureHead? (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) : Option SupportProfile :=
  bootstrapClosureBoundHead? P D X.data

@[simp] theorem gapClosureHead?_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureHead? P D X = bootstrapClosureBoundHead? P D X.data := rfl

def gapClosureCap (P : Params) (D : ClosureData P)
    (_ : GapClosurePackage P D) : ℕ :=
  cap P D

@[simp] theorem gapClosureCap_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureCap P D X = cap P D := rfl

def gapClosureOmegaBound (P : Params) (D : ClosureData P)
    (_ : GapClosurePackage P D) : ℕ :=
  omegaBound P D

@[simp] theorem gapClosureOmegaBound_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureOmegaBound P D X = omegaBound P D := rfl

def gapClosureClosureData (P : Params) (D : ClosureData P)
    (_ : GapClosurePackage P D) : ClosureData P :=
  D

@[simp] theorem gapClosureClosureData_def (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureClosureData P D X = D := rfl

theorem GapClosurePackage.bootstrap_holds (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    BootstrapCondition P D X.data.data.data := by
  exact BootstrapClosureBoundPackage.bootstrap_holds P D X.data

theorem GapClosurePackage.member_truncated (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R, R ∈ gapClosureFamily P D X → ProfileInTruncatedFamily P D R := by
  intro R hR
  rw [gapClosureFamily_def] at hR
  exact BootstrapClosureBoundPackage.member_truncated P D X.data R hR

theorem GapClosurePackage.member_rigid (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R, R ∈ gapClosureFamily P D X → RigidProfile P D R := by
  intro R hR
  rw [gapClosureFamily_def] at hR
  exact BootstrapClosureBoundPackage.member_rigid P D X.data R hR

theorem GapClosurePackage.omegahat_below_width (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    OmegahatBelowWidth P D X.data.data.data.omegaHat := by
  exact BootstrapClosureBoundPackage.omegahat_below_width P D X.data

theorem GapClosurePackage.bound_at_least_cap (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    bootstrapClosureBoundAtLeastCap P D X.data ↔
      cap P D ≤ gapClosureBoundValue P D X := by
  rfl

theorem gapClosureFamily_nil_or_cons (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    gapClosureFamily P D X = [] ∨ ∃ R F, gapClosureFamily P D X = R :: F := by
  rw [gapClosureFamily_def]
  exact bootstrapClosureBoundFamily_nil_or_cons P D X.data

@[simp] theorem gapClosureHead?_nil (P : Params) (D : ClosureData P)
    (hT : IsTruncatedFamily P D []) (hR : RigidProfileFamily P D [])
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk [] hT hR δ ω))
    (N : ClosureBoundData P D) :
    gapClosureHead? P D
      (GapClosurePackage.mk
        (BootstrapClosureBoundPackage.mk
          (BootstrapPackage.mk (TruncatedGapPackage.mk [] hT hR δ ω) hB) N)) = none := rfl

@[simp] theorem gapClosureHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (N : ClosureBoundData P D) :
    gapClosureHead? P D
      (GapClosurePackage.mk
        (BootstrapClosureBoundPackage.mk
          (BootstrapPackage.mk (TruncatedGapPackage.mk (R :: F) hT hR δ ω) hB) N)) = some R := rfl

theorem GapClosurePackage.head_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (N : ClosureBoundData P D) :
    ProfileInTruncatedFamily P D R := by
  exact BootstrapClosureBoundPackage.head_truncated P D R F hT hR δ ω hB N

theorem GapClosurePackage.head_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (N : ClosureBoundData P D) :
    RigidProfile P D R := by
  exact BootstrapClosureBoundPackage.head_rigid P D R F hT hR δ ω hB N

theorem GapClosurePackage.tail_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (N : ClosureBoundData P D) :
    IsTruncatedFamily P D F := by
  exact BootstrapClosureBoundPackage.tail_truncated P D R F hT hR δ ω hB N

theorem GapClosurePackage.tail_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (N : ClosureBoundData P D) :
    RigidProfileFamily P D F := by
  exact BootstrapClosureBoundPackage.tail_rigid P D R F hT hR δ ω hB N

theorem gapClosureBoundAtLeastCap_or_not (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    bootstrapClosureBoundAtLeastCap P D X.data ∨
      ¬ bootstrapClosureBoundAtLeastCap P D X.data := by
  exact bootstrapClosureBoundAtLeastCap_or_not P D X.data

def gapClosureFromBootstrapBound (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : GapClosurePackage P D :=
  GapClosurePackage.mk X

@[simp] theorem gapClosureFromBootstrapBound_data (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    (gapClosureFromBootstrapBound P D X).data = X := rfl

theorem gapClosure_member_truncated_readable (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R, R ∈ gapClosureFamily P D X → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact GapClosurePackage.member_truncated P D X R hR

theorem gapClosure_member_rigid_readable (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R, R ∈ gapClosureFamily P D X → RigidProfile P D R := by
  intro R hR
  exact GapClosurePackage.member_rigid P D X R hR

theorem gapClosure_bootstrap_readable (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    BootstrapCondition P D X.data.data.data := by
  exact GapClosurePackage.bootstrap_holds P D X

theorem gapClosure_omegahat_readable (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    OmegahatBelowWidth P D X.data.data.data.omegaHat := by
  exact GapClosurePackage.omegahat_below_width P D X

theorem gapClosure_family_agrees_with_data (P : Params) (D : ClosureData P)
    (X : GapClosurePackage P D) :
    ∀ R, R ∈ gapClosureFamily P D X →
      SupportBelow D.N (profileSupport R) ∧ SupportWithinOmega D.omegaHat (profileSupport R) := by
  intro R hR
  exact (profileInTruncatedFamily_iff P D R).mp (GapClosurePackage.member_truncated P D X R hR)

end GapClosure
end CaseC
end Lehmer