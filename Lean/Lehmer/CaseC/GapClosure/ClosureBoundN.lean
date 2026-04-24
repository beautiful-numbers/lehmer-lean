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

structure ClosureBoundData (P : Params) (D : ClosureData P) where
  value : ℕ

@[simp] theorem ClosureBoundData.value_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    (ClosureBoundData.mk n : ClosureBoundData P D).value = n := rfl

def closureBoundValue (P : Params) (D : ClosureData P) (X : ClosureBoundData P D) : ℕ :=
  X.value

@[simp] theorem closureBoundValue_def (P : Params) (D : ClosureData P) (X : ClosureBoundData P D) :
    closureBoundValue P D X = X.value := rfl

@[simp] theorem closureBoundValue_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    closureBoundValue P D (ClosureBoundData.mk n) = n := rfl

def ClosureBoundAtLeastCap (P : Params) (D : ClosureData P) (X : ClosureBoundData P D) : Prop :=
  cap P D ≤ closureBoundValue P D X

@[simp] theorem ClosureBoundAtLeastCap_def (P : Params) (D : ClosureData P) (X : ClosureBoundData P D) :
    ClosureBoundAtLeastCap P D X = (cap P D ≤ closureBoundValue P D X) := rfl

@[simp] theorem ClosureBoundAtLeastCap_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    ClosureBoundAtLeastCap P D (ClosureBoundData.mk n) = (cap P D ≤ n) := rfl

theorem closureBound_eq_of_value_eq (P : Params) (D : ClosureData P)
    {X Y : ClosureBoundData P D} :
    closureBoundValue P D X = closureBoundValue P D Y → X = Y := by
  intro h
  cases X
  cases Y
  simp [closureBoundValue] at h
  cases h
  rfl

@[ext] theorem ClosureBoundData.ext (P : Params) (D : ClosureData P)
    {X Y : ClosureBoundData P D}
    (h : closureBoundValue P D X = closureBoundValue P D Y) : X = Y :=
  closureBound_eq_of_value_eq P D h

theorem closureBoundAtLeastCap_or_not (P : Params) (D : ClosureData P) (X : ClosureBoundData P D) :
    ClosureBoundAtLeastCap P D X ∨ ¬ ClosureBoundAtLeastCap P D X := by
  exact Classical.em _

structure BootstrapClosureBoundPackage (P : Params) (D : ClosureData P) where
  data : BootstrapPackage P D
  bound : ClosureBoundData P D

@[simp] theorem BootstrapClosureBoundPackage.data_mk (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) (N : ClosureBoundData P D) :
    (BootstrapClosureBoundPackage.mk X N).data = X := rfl

@[simp] theorem BootstrapClosureBoundPackage.bound_mk (P : Params) (D : ClosureData P)
    (X : BootstrapPackage P D) (N : ClosureBoundData P D) :
    (BootstrapClosureBoundPackage.mk X N).bound = N := rfl

def bootstrapClosureBoundFamily (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : SupportProfileFamily :=
  bootstrapFamily P D X.data

@[simp] theorem bootstrapClosureBoundFamily_def (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundFamily P D X = bootstrapFamily P D X.data := rfl

def bootstrapClosureBoundValue (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : ℕ :=
  closureBoundValue P D X.bound

@[simp] theorem bootstrapClosureBoundValue_def (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundValue P D X = closureBoundValue P D X.bound := rfl

def bootstrapClosureBoundDeltaValue (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : ℕ :=
  bootstrapDeltaValue P D X.data

@[simp] theorem bootstrapClosureBoundDeltaValue_def (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundDeltaValue P D X = bootstrapDeltaValue P D X.data := rfl

def bootstrapClosureBoundOmegahatValue (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : ℕ :=
  bootstrapOmegahatValue P D X.data

@[simp] theorem bootstrapClosureBoundOmegahatValue_def (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundOmegahatValue P D X = bootstrapOmegahatValue P D X.data := rfl

def bootstrapClosureBoundHead? (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : Option SupportProfile :=
  bootstrapHead? P D X.data

@[simp] theorem bootstrapClosureBoundHead?_def (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundHead? P D X = bootstrapHead? P D X.data := rfl

def bootstrapClosureBoundAtLeastCap (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) : Prop :=
  ClosureBoundAtLeastCap P D X.bound

@[simp] theorem bootstrapClosureBoundAtLeastCap_def (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundAtLeastCap P D X = ClosureBoundAtLeastCap P D X.bound := rfl

theorem BootstrapClosureBoundPackage.bootstrap_holds (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    BootstrapCondition P D X.data.data := by
  exact X.data.bootstrap

theorem BootstrapClosureBoundPackage.member_truncated (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ X.data.data.family → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact BootstrapPackage.member_truncated P D X.data R hR

theorem BootstrapClosureBoundPackage.member_rigid (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ X.data.data.family → RigidProfile P D R := by
  intro R hR
  exact BootstrapPackage.member_rigid P D X.data R hR

theorem BootstrapClosureBoundPackage.omegahat_below_width (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    OmegahatBelowWidth P D X.data.data.omegaHat := by
  exact BootstrapPackage.omegahat_below_width P D X.data

theorem bootstrapClosureBoundFamily_nil_or_cons (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    X.data.data.family = [] ∨ ∃ R F, X.data.data.family = R :: F := by
  exact BootstrapPackage.family_nil_or_cons P D X.data

@[simp] theorem bootstrapClosureBoundHead?_nil (P : Params) (D : ClosureData P)
    (hT : IsTruncatedFamily P D []) (hR : RigidProfileFamily P D [])
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk [] hT hR δ ω))
    (_N : ClosureBoundData P D) :
    bootstrapClosureBoundHead? P D
      (BootstrapClosureBoundPackage.mk (BootstrapPackage.mk (TruncatedGapPackage.mk [] hT hR δ ω) hB) _N) = none := rfl

@[simp] theorem bootstrapClosureBoundHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (_N : ClosureBoundData P D) :
    bootstrapClosureBoundHead? P D
      (BootstrapClosureBoundPackage.mk (BootstrapPackage.mk (TruncatedGapPackage.mk (R :: F) hT hR δ ω) hB) _N) = some R := rfl

theorem BootstrapClosureBoundPackage.head_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (_N : ClosureBoundData P D) :
    ProfileInTruncatedFamily P D R := by
  exact BootstrapPackage.head_truncated P D R F hT hR δ ω hB

theorem BootstrapClosureBoundPackage.head_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (_N : ClosureBoundData P D) :
    RigidProfile P D R := by
  exact BootstrapPackage.head_rigid P D R F hT hR δ ω hB

theorem BootstrapClosureBoundPackage.tail_truncated (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (_N : ClosureBoundData P D) :
    IsTruncatedFamily P D F := by
  exact BootstrapPackage.tail_truncated P D R F hT hR δ ω hB

theorem BootstrapClosureBoundPackage.tail_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hT : IsTruncatedFamily P D (R :: F))
    (hR : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D)
    (hB : BootstrapCondition P D (TruncatedGapPackage.mk (R :: F) hT hR δ ω))
    (_N : ClosureBoundData P D) :
    RigidProfileFamily P D F := by
  exact BootstrapPackage.tail_rigid P D R F hT hR δ ω hB

def closureBoundZero (P : Params) (D : ClosureData P) : ClosureBoundData P D :=
  ClosureBoundData.mk 0

@[simp] theorem closureBoundZero_value (P : Params) (D : ClosureData P) :
    closureBoundValue P D (closureBoundZero P D) = 0 := rfl

def closureBoundSucc (P : Params) (D : ClosureData P) (X : ClosureBoundData P D) :
    ClosureBoundData P D :=
  ClosureBoundData.mk (Nat.succ (closureBoundValue P D X))

@[simp] theorem closureBoundSucc_value (P : Params) (D : ClosureData P)
    (X : ClosureBoundData P D) :
    closureBoundValue P D (closureBoundSucc P D X) = Nat.succ (closureBoundValue P D X) := rfl

theorem bootstrapClosureBoundAtLeastCap_or_not (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    bootstrapClosureBoundAtLeastCap P D X ∨ ¬ bootstrapClosureBoundAtLeastCap P D X := by
  exact Classical.em _

theorem bootstrapClosureBound_member_truncated_readable (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ bootstrapClosureBoundFamily P D X → ProfileInTruncatedFamily P D R := by
  intro R hR
  rw [bootstrapClosureBoundFamily_def] at hR
  exact BootstrapPackage.member_truncated P D X.data R hR

theorem bootstrapClosureBound_member_rigid_readable (P : Params) (D : ClosureData P)
    (X : BootstrapClosureBoundPackage P D) :
    ∀ R, R ∈ bootstrapClosureBoundFamily P D X → RigidProfile P D R := by
  intro R hR
  rw [bootstrapClosureBoundFamily_def] at hR
  exact BootstrapPackage.member_rigid P D X.data R hR

end GapClosure
end CaseC
end Lehmer