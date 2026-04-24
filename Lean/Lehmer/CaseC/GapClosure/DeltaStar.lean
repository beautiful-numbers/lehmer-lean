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

structure DeltaStarData (P : Params) (D : ClosureData P) where
  value : ℕ

@[simp] theorem DeltaStarData.value_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    (DeltaStarData.mk n : DeltaStarData P D).value = n := rfl

def deltaStarValue (P : Params) (D : ClosureData P) (X : DeltaStarData P D) : ℕ :=
  X.value

@[simp] theorem deltaStarValue_def (P : Params) (D : ClosureData P) (X : DeltaStarData P D) :
    deltaStarValue P D X = X.value := rfl

@[simp] theorem deltaStarValue_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    deltaStarValue P D (DeltaStarData.mk n) = n := rfl

def PositiveDeltaStar (P : Params) (D : ClosureData P) (X : DeltaStarData P D) : Prop :=
  0 < deltaStarValue P D X

@[simp] theorem PositiveDeltaStar_def (P : Params) (D : ClosureData P) (X : DeltaStarData P D) :
    PositiveDeltaStar P D X = (0 < deltaStarValue P D X) := rfl

@[simp] theorem PositiveDeltaStar_mk (P : Params) (D : ClosureData P) (n : ℕ) :
    PositiveDeltaStar P D (DeltaStarData.mk n) = (0 < n) := rfl

theorem deltaStar_eq_of_value_eq (P : Params) (D : ClosureData P)
    {X Y : DeltaStarData P D} :
    deltaStarValue P D X = deltaStarValue P D Y → X = Y := by
  intro h
  cases X
  cases Y
  simp [deltaStarValue] at h
  cases h
  rfl

@[ext] theorem DeltaStarData.ext (P : Params) (D : ClosureData P)
    {X Y : DeltaStarData P D}
    (h : deltaStarValue P D X = deltaStarValue P D Y) : X = Y :=
  deltaStar_eq_of_value_eq P D h

theorem positiveDeltaStar_or_not (P : Params) (D : ClosureData P) (X : DeltaStarData P D) :
    PositiveDeltaStar P D X ∨ ¬ PositiveDeltaStar P D X := by
  exact Classical.em _

structure RigidDeltaStarPackage (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  rigid : RigidProfileFamily P D family
  delta : DeltaStarData P D

@[simp] theorem RigidDeltaStarPackage.family_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : RigidProfileFamily P D F) (δ : DeltaStarData P D) :
    (RigidDeltaStarPackage.mk F hF δ).family = F := rfl

@[simp] theorem RigidDeltaStarPackage.rigid_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : RigidProfileFamily P D F) (δ : DeltaStarData P D) :
    (RigidDeltaStarPackage.mk F hF δ).rigid = hF := rfl

@[simp] theorem RigidDeltaStarPackage.delta_mk (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (hF : RigidProfileFamily P D F) (δ : DeltaStarData P D) :
    (RigidDeltaStarPackage.mk F hF δ).delta = δ := rfl

def rigidDeltaStarFamily (P : Params) (D : ClosureData P) (X : RigidDeltaStarPackage P D) :
    SupportProfileFamily :=
  X.family

@[simp] theorem rigidDeltaStarFamily_def (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarFamily P D X = X.family := rfl

def rigidDeltaStarValue (P : Params) (D : ClosureData P) (X : RigidDeltaStarPackage P D) : ℕ :=
  deltaStarValue P D X.delta

@[simp] theorem rigidDeltaStarValue_def (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarValue P D X = deltaStarValue P D X.delta := rfl

def rigidDeltaStarPositive (P : Params) (D : ClosureData P) (X : RigidDeltaStarPackage P D) : Prop :=
  PositiveDeltaStar P D X.delta

@[simp] theorem rigidDeltaStarPositive_def (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarPositive P D X = PositiveDeltaStar P D X.delta := rfl

theorem rigidDeltaStarPackage_member_rigid (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact rigidProfileFamily_mem P D X.family X.rigid R hR

def rigidDeltaStarHead? (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) : Option SupportProfile :=
  familyHead? X.family

@[simp] theorem rigidDeltaStarHead?_def (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarHead? P D X = familyHead? X.family := rfl

theorem rigidDeltaStarFamily_nil_or_cons (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    X.family = [] ∨ ∃ R F, X.family = R :: F := by
  exact rigidFamily_exhaustive X.family

@[simp] theorem rigidDeltaStarHead?_nil (P : Params) (D : ClosureData P)
    (hF : RigidProfileFamily P D []) (δ : DeltaStarData P D) :
    rigidDeltaStarHead? P D (RigidDeltaStarPackage.mk [] hF δ) = none := rfl

@[simp] theorem rigidDeltaStarHead?_cons (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F)) (δ : DeltaStarData P D) :
    rigidDeltaStarHead? P D (RigidDeltaStarPackage.mk (R :: F) hF δ) = some R := rfl

theorem rigidDeltaStarHead_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F)) (_δ : DeltaStarData P D) :
    RigidProfile P D R := by
  exact rigidProfileFamily_head P D R F hF

theorem rigidDeltaStarTail_rigid (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D (R :: F)) (_δ : DeltaStarData P D) :
    RigidProfileFamily P D F := by
  exact rigidProfileFamily_tail P D R F hF

def deltaStarZero (P : Params) (D : ClosureData P) : DeltaStarData P D :=
  DeltaStarData.mk 0

@[simp] theorem deltaStarZero_value (P : Params) (D : ClosureData P) :
    deltaStarValue P D (deltaStarZero P D) = 0 := rfl

theorem not_positive_deltaStarZero (P : Params) (D : ClosureData P) :
    ¬ PositiveDeltaStar P D (deltaStarZero P D) := by
  simp [deltaStarZero, PositiveDeltaStar, deltaStarValue]

def deltaStarSucc (P : Params) (D : ClosureData P) (X : DeltaStarData P D) : DeltaStarData P D :=
  DeltaStarData.mk (Nat.succ (deltaStarValue P D X))

@[simp] theorem deltaStarSucc_value (P : Params) (D : ClosureData P) (X : DeltaStarData P D) :
    deltaStarValue P D (deltaStarSucc P D X) = Nat.succ (deltaStarValue P D X) := rfl

theorem positive_deltaStarSucc (P : Params) (D : ClosureData P) (X : DeltaStarData P D) :
    PositiveDeltaStar P D (deltaStarSucc P D X) := by
  simp [PositiveDeltaStar, deltaStarSucc, deltaStarValue]

theorem rigidDeltaStarPositive_or_not (P : Params) (D : ClosureData P)
    (X : RigidDeltaStarPackage P D) :
    rigidDeltaStarPositive P D X ∨ ¬ rigidDeltaStarPositive P D X := by
  exact Classical.em _

end GapClosure
end CaseC
end Lehmer