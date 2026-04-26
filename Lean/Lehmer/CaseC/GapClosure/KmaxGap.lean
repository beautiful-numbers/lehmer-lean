-- FILE: Lean/Lehmer/CaseC/GapClosure/KmaxGap.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
- Lehmer.CaseC.GapClosure.Omegahat : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.DeltaStar
import Lehmer.CaseC.GapClosure.Omegahat

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

structure PositiveGapData
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F) where
  delta : DeltaStarData P D F hF

def positiveGapValue
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF) : ℚ :=
  deltaStarValue P D F hF G.delta

@[simp] theorem positiveGapValue_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF) :
    positiveGapValue P D F hF G =
      deltaStarValue P D F hF G.delta := rfl

theorem positiveGapValue_pos
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF) :
    0 < positiveGapValue P D F hF G := by
  exact deltaStar_positive P D F hF G.delta

theorem positiveGap_le_member_gap
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (R : SupportProfile)
    (hR : R ∈ F) :
    positiveGapValue P D F hF G ≤
      profileRigidityGapValue P D R (hF R hR) := by
  exact deltaStar_le_profile_gap P D F hF G.delta R hR

structure ClosureCapCandidate
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF) where
  value : ℕ
  positive : 0 < value
  atLeastClosureCap : cap P D ≤ value
  atLeastClosureN : D.N ≤ value
  kmaxControlled :
    kmaxValue P D F hF K ≤
      (value : ℚ) * positiveGapValue P D F hF G

def closureCapCandidateValue
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) : ℕ :=
  C.value

@[simp] theorem closureCapCandidateValue_def
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    closureCapCandidateValue P D F hF G K C = C.value := rfl

theorem closureCapCandidate_pos
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    0 < closureCapCandidateValue P D F hF G K C := by
  exact C.positive

theorem closureCapCandidate_atLeastCap
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    cap P D ≤ closureCapCandidateValue P D F hF G K C := by
  exact C.atLeastClosureCap

theorem closureCapCandidate_atLeastClosureN
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    D.N ≤ closureCapCandidateValue P D F hF G K C := by
  exact C.atLeastClosureN

theorem closureCapCandidate_kmaxControlled
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    kmaxValue P D F hF K ≤
      (closureCapCandidateValue P D F hF G K C : ℚ) *
        positiveGapValue P D F hF G := by
  exact C.kmaxControlled

structure KmaxGapPackage
    (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  rigid : RigidProfileFamily P D family
  nonIntegrality : NonIntegralityWitnessFamily P D family
  gap : PositiveGapData P D family rigid
  kmax : KmaxData P D family rigid
  closureCap : ClosureCapCandidate P D family rigid gap kmax

def KmaxGapPackage.nonIntegralityFamilyPackage
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    NonIntegralityFamilyPackage P D :=
  { family := X.family
    witnesses := X.nonIntegrality }

def kmaxGapFamily
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : SupportProfileFamily :=
  X.family

@[simp] theorem kmaxGapFamily_def
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    kmaxGapFamily P D X = X.family := rfl

def kmaxGapRigid
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    RigidProfileFamily P D (kmaxGapFamily P D X) :=
  X.rigid

@[simp] theorem kmaxGapRigid_def
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    kmaxGapRigid P D X = X.rigid := rfl

def kmaxGapPositiveValue
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : ℚ :=
  positiveGapValue P D X.family X.rigid X.gap

@[simp] theorem kmaxGapPositiveValue_def
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    kmaxGapPositiveValue P D X =
      positiveGapValue P D X.family X.rigid X.gap := rfl

def kmaxGapKmaxValue
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : ℚ :=
  kmaxValue P D X.family X.rigid X.kmax

@[simp] theorem kmaxGapKmaxValue_def
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    kmaxGapKmaxValue P D X =
      kmaxValue P D X.family X.rigid X.kmax := rfl

def kmaxGapClosureCapValue
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : ℕ :=
  closureCapCandidateValue P D X.family X.rigid X.gap X.kmax X.closureCap

@[simp] theorem kmaxGapClosureCapValue_def
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    kmaxGapClosureCapValue P D X =
      closureCapCandidateValue P D X.family X.rigid X.gap X.kmax X.closureCap := rfl

theorem kmaxGap_delta_positive
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    0 < kmaxGapPositiveValue P D X := by
  exact positiveGapValue_pos P D X.family X.rigid X.gap

theorem kmaxGap_kmax_positive
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    0 < kmaxGapKmaxValue P D X := by
  exact kmax_positive P D X.family X.rigid X.kmax

theorem kmaxGap_closureCap_positive
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    0 < kmaxGapClosureCapValue P D X := by
  exact closureCapCandidate_pos P D X.family X.rigid X.gap X.kmax X.closureCap

theorem kmaxGap_closureCap_atLeastCap
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    cap P D ≤ kmaxGapClosureCapValue P D X := by
  exact closureCapCandidate_atLeastCap P D X.family X.rigid X.gap X.kmax X.closureCap

theorem kmaxGap_closureCap_atLeastClosureN
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    D.N ≤ kmaxGapClosureCapValue P D X := by
  exact closureCapCandidate_atLeastClosureN P D X.family X.rigid X.gap X.kmax X.closureCap

theorem kmaxGap_kmaxControlled
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    kmaxGapKmaxValue P D X ≤
      (kmaxGapClosureCapValue P D X : ℚ) *
        kmaxGapPositiveValue P D X := by
  exact closureCapCandidate_kmaxControlled P D X.family X.rigid X.gap X.kmax X.closureCap

def kmaxGapFamily_mem_rigid
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X → RigidProfile P D R := by
  intro R hR
  exact X.rigid R hR

theorem kmaxGapFamily_mem_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact RigidProfile.preAdmissible P D R (X.rigid R hR)

theorem kmaxGapFamily_mem_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact RigidProfile.admissibleAtLevel P D R (X.rigid R hR)

theorem kmaxGapFamily_mem_locksB
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact RigidProfile.locksB P D R (X.rigid R hR)

theorem kmaxGapFamily_mem_hasWitness
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      hasNonIntegralityWitness P D R := by
  intro R hR
  exact ⟨X.nonIntegrality R hR⟩

theorem kmaxGapFamily_mem_nonIntegral
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.supportNonIntegral (profileSupport R) := by
  intro R hR
  exact (X.nonIntegrality R hR).nonIntegral

theorem kmaxGapFamily_mem_index_le_kmax
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      profileSupportIndex R ≤ kmaxGapKmaxValue P D X := by
  intro R hR
  exact profileIndex_le_kmax P D X.family X.rigid X.kmax R hR

theorem kmaxGapFamily_mem_delta_le_gap
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, ∀ hR : R ∈ kmaxGapFamily P D X,
      kmaxGapPositiveValue P D X ≤
        profileRigidityGapValue P D R
          ((kmaxGapFamily_mem_rigid P D X) R hR) := by
  intro R hR
  exact positiveGap_le_member_gap P D X.family X.rigid X.gap R hR

def KmaxGapReady
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) : Prop :=
  0 < kmaxGapPositiveValue P D X ∧
  0 < kmaxGapKmaxValue P D X ∧
  0 < kmaxGapClosureCapValue P D X ∧
  cap P D ≤ kmaxGapClosureCapValue P D X ∧
  D.N ≤ kmaxGapClosureCapValue P D X ∧
  kmaxGapKmaxValue P D X ≤
    (kmaxGapClosureCapValue P D X : ℚ) *
      kmaxGapPositiveValue P D X

@[simp] theorem KmaxGapReady_def
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    KmaxGapReady P D X =
      (0 < kmaxGapPositiveValue P D X ∧
      0 < kmaxGapKmaxValue P D X ∧
      0 < kmaxGapClosureCapValue P D X ∧
      cap P D ≤ kmaxGapClosureCapValue P D X ∧
      D.N ≤ kmaxGapClosureCapValue P D X ∧
      kmaxGapKmaxValue P D X ≤
        (kmaxGapClosureCapValue P D X : ℚ) *
          kmaxGapPositiveValue P D X) := rfl

theorem kmaxGapReady
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    KmaxGapReady P D X := by
  exact ⟨
    kmaxGap_delta_positive P D X,
    kmaxGap_kmax_positive P D X,
    kmaxGap_closureCap_positive P D X,
    kmaxGap_closureCap_atLeastCap P D X,
    kmaxGap_closureCap_atLeastClosureN P D X,
    kmaxGap_kmaxControlled P D X
  ⟩

def kmaxGap_member_rigid_readable
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      RigidProfile P D R := by
  intro R hR
  exact kmaxGapFamily_mem_rigid P D X R hR

theorem kmaxGap_member_preAdmissible_readable
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact kmaxGapFamily_mem_preAdmissible P D X R hR

theorem kmaxGap_member_admissibleAtLevel_readable
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact kmaxGapFamily_mem_admissibleAtLevel P D X R hR

theorem kmaxGap_member_locksB_readable
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact kmaxGapFamily_mem_locksB P D X R hR

theorem kmaxGap_member_nonIntegral_readable
    (P : Params) (D : ClosureData P)
    (X : KmaxGapPackage P D) :
    ∀ R, R ∈ kmaxGapFamily P D X →
      Certificate.supportNonIntegral (profileSupport R) := by
  intro R hR
  exact kmaxGapFamily_mem_nonIntegral P D X R hR

def mkPositiveGapData
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    PositiveGapData P D F hF :=
  { delta := δ }

@[simp] theorem mkPositiveGapData_delta
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (δ : DeltaStarData P D F hF) :
    (mkPositiveGapData P D F hF δ).delta = δ := rfl

def mkClosureCapCandidate
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (v : ℕ)
    (hv : 0 < v)
    (hCap : cap P D ≤ v)
    (hN : D.N ≤ v)
    (hControl :
      kmaxValue P D F hF K ≤
        (v : ℚ) * positiveGapValue P D F hF G) :
    ClosureCapCandidate P D F hF G K :=
  { value := v
    positive := hv
    atLeastClosureCap := hCap
    atLeastClosureN := hN
    kmaxControlled := hControl }

@[simp] theorem mkClosureCapCandidate_value
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (v : ℕ)
    (hv : 0 < v)
    (hCap : cap P D ≤ v)
    (hN : D.N ≤ v)
    (hControl :
      kmaxValue P D F hF K ≤
        (v : ℚ) * positiveGapValue P D F hF G) :
    (mkClosureCapCandidate P D F hF G K v hv hCap hN hControl).value = v := rfl

def mkKmaxGapPackage
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (hNI : NonIntegralityWitnessFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    KmaxGapPackage P D :=
  { family := F
    rigid := hF
    nonIntegrality := hNI
    gap := G
    kmax := K
    closureCap := C }

@[simp] theorem mkKmaxGapPackage_family
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (hNI : NonIntegralityWitnessFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    (mkKmaxGapPackage P D F hF hNI G K C).family = F := rfl

@[simp] theorem mkKmaxGapPackage_rigid
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (hNI : NonIntegralityWitnessFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    (mkKmaxGapPackage P D F hF hNI G K C).rigid = hF := rfl

@[simp] theorem mkKmaxGapPackage_nonIntegrality
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (hNI : NonIntegralityWitnessFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    (mkKmaxGapPackage P D F hF hNI G K C).nonIntegrality = hNI := rfl

@[simp] theorem mkKmaxGapPackage_gap
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (hNI : NonIntegralityWitnessFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    (mkKmaxGapPackage P D F hF hNI G K C).gap = G := rfl

@[simp] theorem mkKmaxGapPackage_kmax
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (hNI : NonIntegralityWitnessFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    (mkKmaxGapPackage P D F hF hNI G K C).kmax = K := rfl

@[simp] theorem mkKmaxGapPackage_closureCap
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily)
    (hF : RigidProfileFamily P D F)
    (hNI : NonIntegralityWitnessFamily P D F)
    (G : PositiveGapData P D F hF)
    (K : KmaxData P D F hF)
    (C : ClosureCapCandidate P D F hF G K) :
    (mkKmaxGapPackage P D F hF hNI G K C).closureCap = C := rfl

end GapClosure
end CaseC
end Lehmer