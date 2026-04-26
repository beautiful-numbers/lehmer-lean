-- FILE: Lean/Lehmer/CaseC/GapClosure/Rigidity.lean

/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.Certificate.Format : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.Certificate.Format

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic
open Lehmer.Pipeline

def profileSupportIndex (R : SupportProfile) : ℚ :=
  Certificate.supportIndex (profileSupport R)

@[simp] theorem profileSupportIndex_def (R : SupportProfile) :
    profileSupportIndex R = Certificate.supportIndex (profileSupport R) := rfl

def profileSupportN (R : SupportProfile) : ℕ :=
  Certificate.supportN (profileSupport R)

@[simp] theorem profileSupportN_def (R : SupportProfile) :
    profileSupportN R = Certificate.supportN (profileSupport R) := rfl

def profileSupportL (R : SupportProfile) : ℕ :=
  Certificate.supportL (profileSupport R)

@[simp] theorem profileSupportL_def (R : SupportProfile) :
    profileSupportL R = Certificate.supportL (profileSupport R) := rfl

def profileSupportPhi (R : SupportProfile) : ℕ :=
  Certificate.supportPhi (profileSupport R)

@[simp] theorem profileSupportPhi_def (R : SupportProfile) :
    profileSupportPhi R = Certificate.supportPhi (profileSupport R) := rfl

structure LocalRigidityGap
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) where
  gapValue : ℚ
  gapPositive : 0 < gapValue
  supportPreAdmissible :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)

@[simp] theorem LocalRigidityGap.gapValue_mk
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (g : ℚ)
    (hg : 0 < g)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)) :
    (LocalRigidityGap.mk g hg hPre).gapValue = g := rfl

@[simp] theorem LocalRigidityGap.gapPositive_mk
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (g : ℚ)
    (hg : 0 < g)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)) :
    (LocalRigidityGap.mk g hg hPre).gapPositive = hg := rfl

@[simp] theorem LocalRigidityGap.supportPreAdmissible_mk
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (g : ℚ)
    (hg : 0 < g)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D (profileSupport R)) :
    (LocalRigidityGap.mk g hg hPre).supportPreAdmissible = hPre := rfl

theorem LocalRigidityGap.in_truncated
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    ProfileInTruncatedFamily P D R := by
  exact (profileInTruncatedFamily_iff P D R).mpr
    (Certificate.preCaseCAdmissible_inTruncatedDomain
      P D (profileSupport R) G.supportPreAdmissible)

theorem LocalRigidityGap.supportBelow
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    ProfileBelow D.N R := by
  exact (LocalRigidityGap.in_truncated P D R G).1

theorem LocalRigidityGap.withinOmega
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    ProfileWithinOmega D.omegaHat R := by
  exact (LocalRigidityGap.in_truncated P D R G).2

theorem LocalRigidityGap.preAdmissible
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact G.supportPreAdmissible

theorem LocalRigidityGap.admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_admissible
    P D (profileSupport R) G.supportPreAdmissible

theorem LocalRigidityGap.preLocksC
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.PreLocksC P D (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_preLocksC
    P D (profileSupport R) G.supportPreAdmissible

theorem LocalRigidityGap.locksB
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.LocksB (level P) (profileSupport R) := by
  exact Certificate.preLocksC_to_locksB
    P D (profileSupport R)
    (LocalRigidityGap.preLocksC P D R G)

theorem LocalRigidityGap.rough
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.RoughAtLevel (level P) (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_rough
    P D (profileSupport R) G.supportPreAdmissible

theorem LocalRigidityGap.oddPrime
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.IsOddPrimeSupport (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_oddPrime
    P D (profileSupport R) G.supportPreAdmissible

theorem LocalRigidityGap.globalLock
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.GlobalLock (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_globalLock
    P D (profileSupport R) G.supportPreAdmissible

theorem LocalRigidityGap.lowPrimeLocks
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    Certificate.LowPrimePowerLocks (level P) (profileSupport R) := by
  exact Certificate.preCaseCAdmissible_lowPrimeLocks
    P D (profileSupport R) G.supportPreAdmissible

theorem LocalRigidityGap.gap_pos
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    0 < G.gapValue := by
  exact G.gapPositive

structure RigidProfile
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) where
  localGap : LocalRigidityGap P D R

@[simp] theorem RigidProfile.localGap_mk
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (G : LocalRigidityGap P D R) :
    (RigidProfile.mk G).localGap = G := rfl

theorem RigidProfile.in_truncated
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    ProfileInTruncatedFamily P D R := by
  exact LocalRigidityGap.in_truncated P D R H.localGap

theorem RigidProfile.supportBelow
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    ProfileBelow D.N R := by
  exact LocalRigidityGap.supportBelow P D R H.localGap

theorem RigidProfile.withinOmega
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    ProfileWithinOmega D.omegaHat R := by
  exact LocalRigidityGap.withinOmega P D R H.localGap

theorem RigidProfile.preAdmissible
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact LocalRigidityGap.preAdmissible P D R H.localGap

theorem RigidProfile.admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  exact LocalRigidityGap.admissibleAtLevel P D R H.localGap

theorem RigidProfile.preLocksC
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.PreLocksC P D (profileSupport R) := by
  exact LocalRigidityGap.preLocksC P D R H.localGap

theorem RigidProfile.locksB
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.LocksB (level P) (profileSupport R) := by
  exact LocalRigidityGap.locksB P D R H.localGap

theorem RigidProfile.rough
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.RoughAtLevel (level P) (profileSupport R) := by
  exact LocalRigidityGap.rough P D R H.localGap

theorem RigidProfile.oddPrime
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.IsOddPrimeSupport (profileSupport R) := by
  exact LocalRigidityGap.oddPrime P D R H.localGap

theorem RigidProfile.globalLock
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.GlobalLock (profileSupport R) := by
  exact LocalRigidityGap.globalLock P D R H.localGap

theorem RigidProfile.lowPrimeLocks
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    Certificate.LowPrimePowerLocks (level P) (profileSupport R) := by
  exact LocalRigidityGap.lowPrimeLocks P D R H.localGap

def RigidProfile.gapValue
    (P : Params) (_D : ClosureData P)
    (_R : SupportProfile)
    (H : RigidProfile P _D _R) : ℚ :=
  H.localGap.gapValue

@[simp] theorem RigidProfile.gapValue_def
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    H.gapValue P D R = H.localGap.gapValue := rfl

theorem RigidProfile.gapPositive
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (H : RigidProfile P D R) :
    0 < H.gapValue P D R := by
  exact H.localGap.gapPositive

def RigidProfileNonIntegrality
    (P : Params) (_D : ClosureData P)
    (R : SupportProfile) : Prop :=
  Certificate.supportNonIntegral (profileSupport R)

@[simp] theorem RigidProfileNonIntegrality_def
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) :
    RigidProfileNonIntegrality P D R =
      Certificate.supportNonIntegral (profileSupport R) := rfl

structure RigidNonIntegralityPackage
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) where
  rigid : RigidProfile P D R
  nonIntegral : RigidProfileNonIntegrality P D R

theorem RigidNonIntegralityPackage.preAdmissible
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (X : RigidNonIntegralityPackage P D R) :
    Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  exact RigidProfile.preAdmissible P D R X.rigid

theorem RigidNonIntegralityPackage.admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (X : RigidNonIntegralityPackage P D R) :
    Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  exact RigidProfile.admissibleAtLevel P D R X.rigid

theorem RigidNonIntegralityPackage.locksB
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (X : RigidNonIntegralityPackage P D R) :
    Certificate.LocksB (level P) (profileSupport R) := by
  exact RigidProfile.locksB P D R X.rigid

theorem RigidNonIntegralityPackage.supportNonIntegral
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (X : RigidNonIntegralityPackage P D R) :
    Certificate.supportNonIntegral (profileSupport R) := by
  exact X.nonIntegral

theorem RigidNonIntegralityPackage.in_truncated
    (P : Params) (D : ClosureData P)
    (R : SupportProfile)
    (X : RigidNonIntegralityPackage P D R) :
    ProfileInTruncatedFamily P D R := by
  exact RigidProfile.in_truncated P D R X.rigid

def transportLocalRigidityGap
    (P : Params) (D : ClosureData P)
    {R T : SupportProfile}
    (h : profileSupport R = profileSupport T)
    (G : LocalRigidityGap P D R) :
    LocalRigidityGap P D T := by
  cases profile_eq_of_support_eq h
  exact G

@[simp] theorem transportLocalRigidityGap_gapValue
    (P : Params) (D : ClosureData P)
    {R T : SupportProfile}
    (h : profileSupport R = profileSupport T)
    (G : LocalRigidityGap P D R) :
    (transportLocalRigidityGap P D h G).gapValue = G.gapValue := by
  cases profile_eq_of_support_eq h
  rfl

def transportRigidProfile
    (P : Params) (D : ClosureData P)
    {R T : SupportProfile}
    (h : profileSupport R = profileSupport T)
    (H : RigidProfile P D R) :
    RigidProfile P D T :=
  { localGap := transportLocalRigidityGap P D h H.localGap }

@[simp] theorem transportRigidProfile_gapValue
    (P : Params) (D : ClosureData P)
    {R T : SupportProfile}
    (h : profileSupport R = profileSupport T)
    (H : RigidProfile P D R) :
    (transportRigidProfile P D h H).localGap.gapValue =
      H.localGap.gapValue := by
  cases profile_eq_of_support_eq h
  rfl

def rigidProfile_of_support_eq
    (P : Params) (D : ClosureData P) {R T : SupportProfile} :
    profileSupport R = profileSupport T →
    RigidProfile P D R →
    RigidProfile P D T := by
  intro hRT hR
  exact transportRigidProfile P D hRT hR

def RigidProfileFamily
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) : Type :=
  ∀ R, R ∈ F → RigidProfile P D R

def rigidProfileFamily_nil
    (P : Params) (D : ClosureData P) :
    RigidProfileFamily P D [] := by
  intro R hR
  simp at hR

def rigidProfileFamily_head
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfileFamily P D (R :: F) → RigidProfile P D R := by
  intro h
  exact h R (by simp)

def rigidProfileFamily_tail
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfileFamily P D (R :: F) → RigidProfileFamily P D F := by
  intro h T hT
  exact h T (by simp [hT])

noncomputable def rigidProfileFamily_cons_intro
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    RigidProfile P D R →
    RigidProfileFamily P D F →
    RigidProfileFamily P D (R :: F) := by
  intro hR hF T hT
  by_cases hEq : T = R
  · cases hEq
    exact hR
  · have hTF : T ∈ F := by
      have hMem : T = R ∨ T ∈ F := by
        simpa using hT
      exact Or.resolve_left hMem hEq
    exact hF T hTF

def rigidProfileFamily_mem
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    RigidProfileFamily P D F → ∀ R, R ∈ F → RigidProfile P D R := by
  intro hF R hR
  exact hF R hR

def rigidProfileFamily_of_pointwise
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    (∀ R, R ∈ F → RigidProfile P D R) → RigidProfileFamily P D F := by
  intro h
  exact h

theorem rigidProfileFamily_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    RigidProfileFamily P D F →
      FamilyAllInTruncatedFamily P D F := by
  intro hF R hR
  exact RigidProfile.in_truncated P D R (hF R hR)

theorem rigidProfileFamily_member_preAdmissible
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    RigidProfileFamily P D F →
      ∀ R, R ∈ F →
        Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro hF R hR
  exact RigidProfile.preAdmissible P D R (hF R hR)

theorem rigidProfileFamily_member_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    RigidProfileFamily P D F →
      ∀ R, R ∈ F →
        Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro hF R hR
  exact RigidProfile.admissibleAtLevel P D R (hF R hR)

theorem rigidProfileFamily_member_locksB
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) :
    RigidProfileFamily P D F →
      ∀ R, R ∈ F →
        Certificate.LocksB (level P) (profileSupport R) := by
  intro hF R hR
  exact RigidProfile.locksB P D R (hF R hR)

def rigidFamilyHead? (P : Params) (_D : ClosureData P) (F : SupportProfileFamily) :
    Option SupportProfile :=
  familyHead? F

@[simp] theorem rigidFamilyHead?_def
    (P : Params) (D : ClosureData P) (F : SupportProfileFamily) :
    rigidFamilyHead? P D F = familyHead? F := rfl

@[simp] theorem rigidFamilyHead?_nil
    (P : Params) (D : ClosureData P) :
    rigidFamilyHead? P D [] = none := rfl

@[simp] theorem rigidFamilyHead?_cons
    (P : Params) (D : ClosureData P)
    (R : SupportProfile) (F : SupportProfileFamily) :
    rigidFamilyHead? P D (R :: F) = some R := rfl

theorem rigidFamily_exhaustive (F : SupportProfileFamily) :
    F = [] ∨ ∃ R G, F = R :: G := by
  exact supportProfileFamily_exhaustive F

structure RigidPackage
    (P : Params) (D : ClosureData P) where
  family : SupportProfileFamily
  rigid : RigidProfileFamily P D family

@[simp] theorem RigidPackage.family_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (h : RigidProfileFamily P D F) :
    (RigidPackage.mk F h).family = F := rfl

@[simp] theorem RigidPackage.rigid_mk
    (P : Params) (D : ClosureData P)
    (F : SupportProfileFamily) (h : RigidProfileFamily P D F) :
    (RigidPackage.mk F h).rigid = h := rfl

def rigidPackageHead?
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) : Option SupportProfile :=
  familyHead? X.family

@[simp] theorem rigidPackageHead?_def
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    rigidPackageHead? P D X = familyHead? X.family := rfl

def rigidPackage_member_rigid
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    ∀ R, R ∈ X.family → RigidProfile P D R := by
  intro R hR
  exact X.rigid R hR

theorem rigidPackage_member_truncated
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    ∀ R, R ∈ X.family → ProfileInTruncatedFamily P D R := by
  intro R hR
  exact RigidProfile.in_truncated P D R (X.rigid R hR)

theorem rigidPackage_member_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    ∀ R, R ∈ X.family →
      Certificate.PreCaseCAdmissibleSupport P D (profileSupport R) := by
  intro R hR
  exact RigidProfile.preAdmissible P D R (X.rigid R hR)

theorem rigidPackage_member_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    ∀ R, R ∈ X.family →
      Certificate.AdmissibleSupportAtLevel (level P) (profileSupport R) := by
  intro R hR
  exact RigidProfile.admissibleAtLevel P D R (X.rigid R hR)

theorem rigidPackage_member_locksB
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    ∀ R, R ∈ X.family →
      Certificate.LocksB (level P) (profileSupport R) := by
  intro R hR
  exact RigidProfile.locksB P D R (X.rigid R hR)

theorem rigidPackage_family_allInTruncatedFamily
    (P : Params) (D : ClosureData P)
    (X : RigidPackage P D) :
    FamilyAllInTruncatedFamily P D X.family := by
  exact rigidProfileFamily_allInTruncatedFamily P D X.family X.rigid

end GapClosure
end CaseC
end Lehmer