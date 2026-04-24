-- FILE: Lean/Lehmer/CaseC/GapClosure/KmaxGap.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.NonIntegrality

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure KmaxData (P : Params) (D : ClosureData P) where
  value : ℕ
  positive : 0 < value

@[simp] theorem KmaxData.value_mk
    (P : Params) (D : ClosureData P) (v : ℕ) (hv : 0 < v) :
    (KmaxData.mk v hv : KmaxData P D).value = v := rfl

@[simp] theorem KmaxData.positive_mk
    (P : Params) (D : ClosureData P) (v : ℕ) (hv : 0 < v) :
    (KmaxData.mk v hv : KmaxData P D).positive = hv := rfl

def kmaxValue (P : Params) (D : ClosureData P) (K : KmaxData P D) : ℕ :=
  K.value

@[simp] theorem kmaxValue_def
    (P : Params) (D : ClosureData P) (K : KmaxData P D) :
    kmaxValue P D K = K.value := rfl

theorem kmaxValue_pos
    (P : Params) (D : ClosureData P) (K : KmaxData P D) :
    0 < kmaxValue P D K := by
  exact K.positive

structure PositiveGapData (P : Params) (D : ClosureData P) where
  familyPackage : NonIntegralityFamilyPackage P D
  gapValue : ℕ
  positive : 0 < gapValue

@[simp] theorem PositiveGapData.familyPackage_mk
    (P : Params) (D : ClosureData P)
    (F : NonIntegralityFamilyPackage P D) (g : ℕ) (hg : 0 < g) :
    (PositiveGapData.mk F g hg).familyPackage = F := rfl

@[simp] theorem PositiveGapData.gapValue_mk
    (P : Params) (D : ClosureData P)
    (F : NonIntegralityFamilyPackage P D) (g : ℕ) (hg : 0 < g) :
    (PositiveGapData.mk F g hg).gapValue = g := rfl

@[simp] theorem PositiveGapData.positive_mk
    (P : Params) (D : ClosureData P)
    (F : NonIntegralityFamilyPackage P D) (g : ℕ) (hg : 0 < g) :
    (PositiveGapData.mk F g hg).positive = hg := rfl

def positiveGapValue (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) : ℕ :=
  G.gapValue

@[simp] theorem positiveGapValue_def
    (P : Params) (D : ClosureData P) (G : PositiveGapData P D) :
    positiveGapValue P D G = G.gapValue := rfl

theorem positiveGapValue_pos
    (P : Params) (D : ClosureData P) (G : PositiveGapData P D) :
    0 < positiveGapValue P D G := by
  exact G.positive

def positiveGapFamily (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) : SupportProfileFamily :=
  G.familyPackage.family

@[simp] theorem positiveGapFamily_def
    (P : Params) (D : ClosureData P) (G : PositiveGapData P D) :
    positiveGapFamily P D G = G.familyPackage.family := rfl

theorem positiveGapFamily_mem_hasWitness
    (P : Params) (D : ClosureData P) (G : PositiveGapData P D) :
    ∀ R, R ∈ positiveGapFamily P D G → hasNonIntegralityWitness P D R := by
  intro R hR
  exact NonIntegralityFamilyPackage.mem_hasWitness (P := P) (D := D) G.familyPackage R hR

theorem positiveGapFamily_mem_rigid
    (P : Params) (D : ClosureData P) (G : PositiveGapData P D) :
    ∀ R, R ∈ positiveGapFamily P D G → RigidProfile P D R := by
  intro R hR
  exact NonIntegralityFamilyPackage.mem_rigid (P := P) (D := D) G.familyPackage R hR

theorem positiveGapFamily_mem_measure_pos
    (P : Params) (D : ClosureData P) (G : PositiveGapData P D) :
    ∀ R, R ∈ positiveGapFamily P D G → ∃ m : ℕ, 0 < m := by
  intro R hR
  exact NonIntegralityFamilyPackage.mem_measure_pos (P := P) (D := D) G.familyPackage R hR

structure ClosureCapCandidate (P : Params) (D : ClosureData P) where
  value : ℕ
  positive : 0 < value

@[simp] theorem ClosureCapCandidate.value_mk
    (P : Params) (D : ClosureData P) (v : ℕ) (hv : 0 < v) :
    (ClosureCapCandidate.mk v hv : ClosureCapCandidate P D).value = v := rfl

@[simp] theorem ClosureCapCandidate.positive_mk
    (P : Params) (D : ClosureData P) (v : ℕ) (hv : 0 < v) :
    (ClosureCapCandidate.mk v hv : ClosureCapCandidate P D).positive = hv := rfl

def closureCapCandidateValue (P : Params) (D : ClosureData P)
    (C : ClosureCapCandidate P D) : ℕ :=
  C.value

@[simp] theorem closureCapCandidateValue_def
    (P : Params) (D : ClosureData P) (C : ClosureCapCandidate P D) :
    closureCapCandidateValue P D C = C.value := rfl

theorem closureCapCandidateValue_pos
    (P : Params) (D : ClosureData P) (C : ClosureCapCandidate P D) :
    0 < closureCapCandidateValue P D C := by
  exact C.positive

structure KmaxGapPackage (P : Params) (D : ClosureData P) where
  gap : PositiveGapData P D
  kmax : KmaxData P D
  closureCap : ClosureCapCandidate P D

@[simp] theorem KmaxGapPackage.gap_mk
    (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) (K : KmaxData P D) (C : ClosureCapCandidate P D) :
    (KmaxGapPackage.mk G K C).gap = G := rfl

@[simp] theorem KmaxGapPackage.kmax_mk
    (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) (K : KmaxData P D) (C : ClosureCapCandidate P D) :
    (KmaxGapPackage.mk G K C).kmax = K := rfl

@[simp] theorem KmaxGapPackage.closureCap_mk
    (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) (K : KmaxData P D) (C : ClosureCapCandidate P D) :
    (KmaxGapPackage.mk G K C).closureCap = C := rfl

def kmaxGapFamily (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : SupportProfileFamily :=
  positiveGapFamily P D X.gap

@[simp] theorem kmaxGapFamily_def
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    kmaxGapFamily P D X = positiveGapFamily P D X.gap := rfl

def kmaxGapValue (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : ℕ :=
  positiveGapValue P D X.gap

@[simp] theorem kmaxGapValue_def
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    kmaxGapValue P D X = positiveGapValue P D X.gap := rfl

def kmaxGapKmaxValue (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : ℕ :=
  kmaxValue P D X.kmax

@[simp] theorem kmaxGapKmaxValue_def
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    kmaxGapKmaxValue P D X = kmaxValue P D X.kmax := rfl

def kmaxGapClosureCapValue (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : ℕ :=
  closureCapCandidateValue P D X.closureCap

@[simp] theorem kmaxGapClosureCapValue_def
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    kmaxGapClosureCapValue P D X = closureCapCandidateValue P D X.closureCap := rfl

theorem kmaxGapValue_pos
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    0 < kmaxGapValue P D X := by
  exact X.gap.positive

theorem kmaxGapKmaxValue_pos
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    0 < kmaxGapKmaxValue P D X := by
  exact X.kmax.positive

theorem kmaxGapClosureCapValue_pos
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    0 < kmaxGapClosureCapValue P D X := by
  exact X.closureCap.positive

theorem kmaxGapFamily_mem_hasWitness
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X → hasNonIntegralityWitness P D R := by
  intro R hR
  exact positiveGapFamily_mem_hasWitness P D X.gap R hR

theorem kmaxGapFamily_mem_rigid
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X → RigidProfile P D R := by
  intro R hR
  exact positiveGapFamily_mem_rigid P D X.gap R hR

theorem kmaxGapFamily_mem_measure_pos
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X → ∃ m : ℕ, 0 < m := by
  intro R hR
  exact positiveGapFamily_mem_measure_pos P D X.gap R hR

def KmaxGapReady (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : Prop :=
  0 < kmaxGapValue P D X ∧
  0 < kmaxGapKmaxValue P D X ∧
  0 < kmaxGapClosureCapValue P D X

@[simp] theorem KmaxGapReady_def
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    KmaxGapReady P D X =
      (0 < kmaxGapValue P D X ∧
       0 < kmaxGapKmaxValue P D X ∧
       0 < kmaxGapClosureCapValue P D X) := rfl

theorem kmaxGapReady
    (P : Params) (D : ClosureData P) (X : KmaxGapPackage P D) :
    KmaxGapReady P D X := by
  exact ⟨kmaxGapValue_pos P D X, kmaxGapKmaxValue_pos P D X, kmaxGapClosureCapValue_pos P D X⟩

def mkKmaxData (P : Params) (D : ClosureData P)
    (v : ℕ) (hv : 0 < v) : KmaxData P D :=
  KmaxData.mk v hv

@[simp] theorem mkKmaxData_value
    (P : Params) (D : ClosureData P) (v : ℕ) (hv : 0 < v) :
    (mkKmaxData P D v hv).value = v := rfl

def mkPositiveGapData (P : Params) (D : ClosureData P)
    (F : NonIntegralityFamilyPackage P D) (g : ℕ) (hg : 0 < g) :
    PositiveGapData P D :=
  PositiveGapData.mk F g hg

@[simp] theorem mkPositiveGapData_gapValue
    (P : Params) (D : ClosureData P)
    (F : NonIntegralityFamilyPackage P D) (g : ℕ) (hg : 0 < g) :
    (mkPositiveGapData P D F g hg).gapValue = g := rfl

def mkClosureCapCandidate (P : Params) (D : ClosureData P)
    (v : ℕ) (hv : 0 < v) : ClosureCapCandidate P D :=
  ClosureCapCandidate.mk v hv

@[simp] theorem mkClosureCapCandidate_value
    (P : Params) (D : ClosureData P) (v : ℕ) (hv : 0 < v) :
    (mkClosureCapCandidate P D v hv).value = v := rfl

def mkKmaxGapPackage (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) (K : KmaxData P D) (C : ClosureCapCandidate P D) :
    KmaxGapPackage P D :=
  KmaxGapPackage.mk G K C

@[simp] theorem mkKmaxGapPackage_gap
    (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) (K : KmaxData P D) (C : ClosureCapCandidate P D) :
    (mkKmaxGapPackage P D G K C).gap = G := rfl

@[simp] theorem mkKmaxGapPackage_kmax
    (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) (K : KmaxData P D) (C : ClosureCapCandidate P D) :
    (mkKmaxGapPackage P D G K C).kmax = K := rfl

@[simp] theorem mkKmaxGapPackage_closureCap
    (P : Params) (D : ClosureData P)
    (G : PositiveGapData P D) (K : KmaxData P D) (C : ClosureCapCandidate P D) :
    (mkKmaxGapPackage P D G K C).closureCap = C := rfl

end GapClosure
end CaseC
end Lehmer