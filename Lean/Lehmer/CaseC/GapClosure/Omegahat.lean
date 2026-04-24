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

structure OmegahatData (P : Params) (D : ClosureData P) where
  value : ℕ

@[simp] theorem OmegahatData.value_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    (OmegahatData.mk n : OmegahatData P D).value = n := rfl

def omegahatValue (P : Params) (D : ClosureData P) (X : OmegahatData P D) : ℕ :=
  X.value

@[simp] theorem omegahatValue_def (P : Params) (D : ClosureData P) (X : OmegahatData P D) :
    omegahatValue P D X = X.value := rfl

@[simp] theorem omegahatValue_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    omegahatValue P D (OmegahatData.mk n) = n := rfl

def OmegahatBelowWidth (P : Params) (D : ClosureData P) (X : OmegahatData P D) : Prop :=
  omegahatValue P D X ≤ width P

@[simp] theorem OmegahatBelowWidth_def (P : Params) (D : ClosureData P) (X : OmegahatData P D) :
    OmegahatBelowWidth P D X = (omegahatValue P D X ≤ width P) := rfl

@[simp] theorem OmegahatBelowWidth_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    OmegahatBelowWidth P D (OmegahatData.mk n) = (n ≤ width P) := rfl

theorem omegahat_eq_of_value_eq (P : Params) (D : ClosureData P)
    {X Y : OmegahatData P D} :
    omegahatValue P D X = omegahatValue P D Y → X = Y := by
  intro h
  cases X
  cases Y
  simp [omegahatValue] at h
  cases h
  rfl

@[ext] theorem OmegahatData.ext (P : Params) (D : ClosureData P)
    {X Y : OmegahatData P D}
    (h : omegahatValue P D X = omegahatValue P D Y) : X = Y :=
  omegahat_eq_of_value_eq P D h

theorem omegahatBelowWidth_or_not (P : Params) (D : ClosureData P) (X : OmegahatData P D) :
    OmegahatBelowWidth P D X ∨ ¬ OmegahatBelowWidth P D X := by
  exact Classical.em _

structure RigidOmegahatPackage (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  rigid : RigidProfileFamily P D family
  delta : DeltaStarData P D
  omegaHat : OmegahatData P D

@[simp] theorem RigidOmegahatPackage.family_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (RigidOmegahatPackage.mk F hF δ ω).family = F := rfl

@[simp] theorem RigidOmegahatPackage.rigid_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (RigidOmegahatPackage.mk F hF δ ω).rigid = hF := rfl

@[simp] theorem RigidOmegahatPackage.delta_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (RigidOmegahatPackage.mk F hF δ ω).delta = δ := rfl

@[simp] theorem RigidOmegahatPackage.omegaHat_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    (RigidOmegahatPackage.mk F hF δ ω).omegaHat = ω := rfl

def rigidOmegahatFamily (P : Params) (D : ClosureData P) (X : RigidOmegahatPackage P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem rigidOmegahatFamily_def (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatFamily P D X = X.family := rfl

def rigidOmegahatDeltaValue (P : Params) (D : ClosureData P) (X : RigidOmegahatPackage P D) : ℕ :=
  deltaStarValue P D X.delta

@[simp] theorem rigidOmegahatDeltaValue_def (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatDeltaValue P D X = deltaStarValue P D X.delta := rfl

def rigidOmegahatValue (P : Params) (D : ClosureData P) (X : RigidOmegahatPackage P D) : ℕ :=
  omegahatValue P D X.omegaHat

@[simp] theorem rigidOmegahatValue_def (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatValue P D X = omegahatValue P D X.omegaHat := rfl

def rigidOmegahatBelowWidth (P : Params) (D : ClosureData P) (X : RigidOmegahatPackage P D) : Prop :=
  OmegahatBelowWidth P D X.omegaHat

@[simp] theorem rigidOmegahatBelowWidth_def (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatBelowWidth P D X = OmegahatBelowWidth P D X.omegaHat := rfl

theorem rigidOmegahatPackage_member_rigid (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact rigidProfileFamily_mem P D X.family X.rigid R hR

def rigidOmegahatHead? (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) : Option SupportProfile :=
  familyHead? X.family

@[simp] theorem rigidOmegahatHead?_def (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatHead? P D X = familyHead? X.family := rfl

theorem rigidOmegahatFamily_nil_or_cons (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact rigidFamily_exhaustive X.family

@[simp] theorem rigidOmegahatHead?_nil (P : Params) (D : ClosureData P)
    (hF : RigidProfileFamily P D []) (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    rigidOmegahatHead? P D (RigidOmegahatPackage.mk [] hF δ ω) = none := rfl

@[simp] theorem rigidOmegahatHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (δ : DeltaStarData P D) (ω : OmegahatData P D) :
    rigidOmegahatHead? P D (RigidOmegahatPackage.mk (R :: F) hF δ ω) = some R := rfl

theorem rigidOmegahatHead_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    RigidProfile P D R := by
  exact rigidProfileFamily_head P D R F hF

theorem rigidOmegahatTail_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F))
    (_δ : DeltaStarData P D) (_ω : OmegahatData P D) :
    RigidProfileFamily P D F := by
  exact rigidProfileFamily_tail P D R F hF

def omegahatZero (P : Params) (D : ClosureData P) : OmegahatData P D :=
  OmegahatData.mk 0

@[simp] theorem omegahatZero_value (P : Params) (D : ClosureData P) :
    omegahatValue P D (omegahatZero P D) = 0 := rfl

def omegahatSucc (P : Params) (D : ClosureData P) (X : OmegahatData P D) : OmegahatData P D :=
  OmegahatData.mk (Nat.succ (omegahatValue P D X))

@[simp] theorem omegahatSucc_value (P : Params) (D : ClosureData P) (X : OmegahatData P D) :
    omegahatValue P D (omegahatSucc P D X) = Nat.succ (omegahatValue P D X) := rfl

theorem rigidOmegahatBelowWidth_of_le_width (P : Params) (D : ClosureData P)
    (X : OmegahatData P D) :
    omegahatValue P D X ≤ width P → OmegahatBelowWidth P D X := by
  intro h
  exact h

theorem rigidOmegahatBelowWidth_mono_value (P : Params) (D : ClosureData P)
    {X Y : OmegahatData P D} :
    omegahatValue P D X = omegahatValue P D Y →
    (OmegahatBelowWidth P D X ↔ OmegahatBelowWidth P D Y) := by
  intro h
  constructor
  · intro hX
    rw [OmegahatBelowWidth_def] at hX ⊢
    rw [h] at hX
    exact hX
  · intro hY
    rw [OmegahatBelowWidth_def] at hY ⊢
    rw [← h] at hY
    exact hY

def rigidOmegahatPackage_delta_readable (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    DeltaStarData P D :=
  X.delta

@[simp] theorem rigidOmegahatPackage_delta_readable_def (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatPackage_delta_readable P D X = X.delta := rfl

def rigidOmegahatPackage_omega_readable (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    OmegahatData P D :=
  X.omegaHat

@[simp] theorem rigidOmegahatPackage_omega_readable_def (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatPackage_omega_readable P D X = X.omegaHat := rfl

theorem rigidOmegahatPackage_belowWidth_or_not (P : Params) (D : ClosureData P)
    (X : RigidOmegahatPackage P D) :
    rigidOmegahatBelowWidth P D X ∨ ¬ rigidOmegahatBelowWidth P D X := by
  exact Classical.em _

end GapClosure
end CaseC
end Lehmer