-- FILE: Lean/Lehmer/CaseC/Certificate/Format.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

inductive LocalClosureKind where
  | emptiness
  | exclusion
  | finiteReduction
deriving DecidableEq

@[simp] theorem localClosureKind_emptiness_ne_exclusion :
    LocalClosureKind.emptiness ≠ LocalClosureKind.exclusion := by
  decide

@[simp] theorem localClosureKind_emptiness_ne_finiteReduction :
    LocalClosureKind.emptiness ≠ LocalClosureKind.finiteReduction := by
  decide

@[simp] theorem localClosureKind_exclusion_ne_emptiness :
    LocalClosureKind.exclusion ≠ LocalClosureKind.emptiness := by
  decide

@[simp] theorem localClosureKind_exclusion_ne_finiteReduction :
    LocalClosureKind.exclusion ≠ LocalClosureKind.finiteReduction := by
  decide

@[simp] theorem localClosureKind_finiteReduction_ne_emptiness :
    LocalClosureKind.finiteReduction ≠ LocalClosureKind.emptiness := by
  decide

@[simp] theorem localClosureKind_finiteReduction_ne_exclusion :
    LocalClosureKind.finiteReduction ≠ LocalClosureKind.exclusion := by
  decide

abbrev ChildPrefixes := List Prefix

def supportN (S : Support) : ℕ :=
  Lehmer.Basic.supportProd S

@[simp] theorem supportN_def (S : Support) :
    supportN S = Lehmer.Basic.supportProd S := rfl

def supportL (S : Support) : ℕ :=
  Lehmer.Basic.supportLcm S

@[simp] theorem supportL_def (S : Support) :
    supportL S = Lehmer.Basic.supportLcm S := rfl

def supportPhi (S : Support) : ℕ :=
  S.prod (fun p => p - 1)

@[simp] theorem supportPhi_def (S : Support) :
    supportPhi S = S.prod (fun p => p - 1) := rfl

def supportIndex (S : Support) : ℚ :=
  (supportN S : ℚ) / (supportPhi S : ℚ)

@[simp] theorem supportIndex_def (S : Support) :
    supportIndex S = (supportN S : ℚ) / (supportPhi S : ℚ) := rfl

def supportLockQuotient (S : Support) : ℚ :=
  ((supportN S - 1 : ℕ) : ℚ) / (supportL S : ℚ)

@[simp] theorem supportLockQuotient_def (S : Support) :
    supportLockQuotient S =
      ((supportN S - 1 : ℕ) : ℚ) / (supportL S : ℚ) := rfl

def supportNonIntegral (S : Support) : Prop :=
  ∀ z : ℤ, supportIndex S ≠ (z : ℚ)

@[simp] theorem supportNonIntegral_def (S : Support) :
    supportNonIntegral S = (∀ z : ℤ, supportIndex S ≠ (z : ℚ)) := rfl

def primeExponentInNat (ell m : ℕ) : ℕ :=
  m.factorization ell

@[simp] theorem primeExponentInNat_def
    (ell m : ℕ) :
    primeExponentInNat ell m = m.factorization ell := rfl

def lowPrimeExponent (ell : ℕ) (S : Support) : ℕ :=
  S.sum (fun p => primeExponentInNat ell (p - 1))

@[simp] theorem lowPrimeExponent_def
    (ell : ℕ) (S : Support) :
    lowPrimeExponent ell S =
      S.sum (fun p => primeExponentInNat ell (p - 1)) := rfl

def IsOddPrimeSupport (S : Support) : Prop :=
  ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2

@[simp] theorem IsOddPrimeSupport_def (S : Support) :
    IsOddPrimeSupport S = (∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) := rfl

def RoughAtLevel (y : ℕ) (S : Support) : Prop :=
  ∀ p ∈ S, y ≤ p

@[simp] theorem RoughAtLevel_def (y : ℕ) (S : Support) :
    RoughAtLevel y S = (∀ p ∈ S, y ≤ p) := rfl

def GlobalLock (S : Support) : Prop :=
  supportL S ∣ supportN S - 1

@[simp] theorem GlobalLock_def (S : Support) :
    GlobalLock S = (supportL S ∣ supportN S - 1) := rfl

def LowPrimePowerLocks (y : ℕ) (S : Support) : Prop :=
  ∀ ell : ℕ,
    Nat.Prime ell →
    ell ≤ y →
    ell ^ lowPrimeExponent ell S ∣ supportN S - 1

@[simp] theorem LowPrimePowerLocks_def (y : ℕ) (S : Support) :
    LowPrimePowerLocks y S =
      (∀ ell : ℕ,
        Nat.Prime ell →
        ell ≤ y →
        ell ^ lowPrimeExponent ell S ∣ supportN S - 1) := rfl

def AdmissibleSupportAtLevel (y : ℕ) (S : Support) : Prop :=
  RoughAtLevel y S ∧
  IsOddPrimeSupport S ∧
  GlobalLock S ∧
  LowPrimePowerLocks y S

@[simp] theorem AdmissibleSupportAtLevel_def (y : ℕ) (S : Support) :
    AdmissibleSupportAtLevel y S =
      (RoughAtLevel y S ∧
        IsOddPrimeSupport S ∧
        GlobalLock S ∧
        LowPrimePowerLocks y S) := rfl

theorem admissible_rough
    (y : ℕ) (S : Support)
    (h : AdmissibleSupportAtLevel y S) :
    RoughAtLevel y S := h.1

theorem admissible_oddPrime
    (y : ℕ) (S : Support)
    (h : AdmissibleSupportAtLevel y S) :
    IsOddPrimeSupport S := h.2.1

theorem admissible_globalLock
    (y : ℕ) (S : Support)
    (h : AdmissibleSupportAtLevel y S) :
    GlobalLock S := h.2.2.1

theorem admissible_lowPrimeLocks
    (y : ℕ) (S : Support)
    (h : AdmissibleSupportAtLevel y S) :
    LowPrimePowerLocks y S := h.2.2.2

structure DerivedLockImplication (S : Support) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  dividesLock :
    modulus ∣ supportN S - 1

structure LocksBData (y : ℕ) (S : Support) where
  admissible : AdmissibleSupportAtLevel y S
  inheritedGlobal :
    ∀ m : ℕ,
      m ∣ supportL S →
      m ∣ supportN S - 1
  inheritedLowPrime :
    ∀ ell a : ℕ,
      Nat.Prime ell →
      ell ≤ y →
      a ≤ lowPrimeExponent ell S →
      ell ^ a ∣ supportN S - 1
  derivedLocks : List (DerivedLockImplication S)

def LocksB (y : ℕ) (S : Support) : Prop :=
  Nonempty (LocksBData y S)

@[simp] theorem LocksB_def (y : ℕ) (S : Support) :
    LocksB y S = Nonempty (LocksBData y S) := rfl

structure PreLocksCData
    (P : Params) (D : ClosureData P)
    (S : Support) where
  base : LocksBData (level P) S

def PreLocksC
    (P : Params) (D : ClosureData P)
    (S : Support) : Prop :=
  Nonempty (PreLocksCData P D S)

@[simp] theorem PreLocksC_def
    (P : Params) (D : ClosureData P) (S : Support) :
    PreLocksC P D S = Nonempty (PreLocksCData P D S) := rfl

def preLocksC_base
    (P : Params) (D : ClosureData P) (S : Support)
    (h : PreLocksCData P D S) :
    LocksBData (level P) S := h.base

theorem preLocksC_to_locksB
    (P : Params) (D : ClosureData P) (S : Support)
    (h : PreLocksC P D S) :
    LocksB (level P) S := by
  rcases h with ⟨d⟩
  exact ⟨d.base⟩

structure CapDependentLockImplication
    (P : Params) (D : ClosureData P)
    (S : Support) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  usesCap : supportN S ≤ cap P D
  dividesLock :
    modulus ∣ supportN S - 1

structure LocksCData
    (P : Params) (D : ClosureData P)
    (S : Support) where
  base : LocksBData (level P) S
  belowCap : supportN S ≤ cap P D
  withinOmega : supportCard S ≤ omegaBound P D
  capLocks : List (CapDependentLockImplication P D S)

def LocksC (P : Params) (D : ClosureData P) (S : Support) : Prop :=
  Nonempty (LocksCData P D S)

@[simp] theorem LocksC_def (P : Params) (D : ClosureData P) (S : Support) :
    LocksC P D S = Nonempty (LocksCData P D S) := rfl

def locksC_base
    (P : Params) (D : ClosureData P) (S : Support)
    (h : LocksCData P D S) :
    LocksBData (level P) S := h.base

theorem locksC_belowCap
    (P : Params) (D : ClosureData P) (S : Support)
    (h : LocksCData P D S) :
    supportN S ≤ cap P D := h.belowCap

theorem locksC_withinOmega
    (P : Params) (D : ClosureData P) (S : Support)
    (h : LocksCData P D S) :
    supportCard S ≤ omegaBound P D := h.withinOmega

theorem locksC_to_preLocksC
    (P : Params) (D : ClosureData P) (S : Support)
    (h : LocksC P D S) :
    PreLocksC P D S := by
  rcases h with ⟨d⟩
  exact ⟨{ base := d.base }⟩

theorem locksC_to_locksB
    (P : Params) (D : ClosureData P) (S : Support)
    (h : LocksC P D S) :
    LocksB (level P) S := by
  exact preLocksC_to_locksB P D S (locksC_to_preLocksC P D S h)

structure CaseCGapBootstrapData
    (P : Params) (D : ClosureData P) where
  deltaStar : ℚ
  deltaStar_pos : 0 < deltaStar
  kmax : ℚ
  kmax_pos : 0 < kmax
  closureNumeratorBound :
    kmax ≤ (cap P D : ℚ) * deltaStar
  omegaCheck :
    omegaBound P D < width P
  capPositive :
    0 < cap P D

def PreCaseCAdmissibleSupport
    (P : Params) (D : ClosureData P)
    (S : Support) : Prop :=
  InTruncatedDomain P D S ∧
  AdmissibleSupportAtLevel (level P) S ∧
  PreLocksC P D S

@[simp] theorem PreCaseCAdmissibleSupport_def
    (P : Params) (D : ClosureData P)
    (S : Support) :
    PreCaseCAdmissibleSupport P D S =
      (InTruncatedDomain P D S ∧
        AdmissibleSupportAtLevel (level P) S ∧
        PreLocksC P D S) := rfl

theorem preCaseCAdmissible_inTruncatedDomain
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : PreCaseCAdmissibleSupport P D S) :
    InTruncatedDomain P D S := h.1

theorem preCaseCAdmissible_admissible
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : PreCaseCAdmissibleSupport P D S) :
    AdmissibleSupportAtLevel (level P) S := h.2.1

theorem preCaseCAdmissible_preLocksC
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : PreCaseCAdmissibleSupport P D S) :
    PreLocksC P D S := h.2.2

theorem preCaseCAdmissible_rough
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : PreCaseCAdmissibleSupport P D S) :
    RoughAtLevel (level P) S := by
  exact admissible_rough
    (level P) S
    (preCaseCAdmissible_admissible P D S h)

theorem preCaseCAdmissible_oddPrime
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : PreCaseCAdmissibleSupport P D S) :
    IsOddPrimeSupport S := by
  exact admissible_oddPrime
    (level P) S
    (preCaseCAdmissible_admissible P D S h)

theorem preCaseCAdmissible_globalLock
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : PreCaseCAdmissibleSupport P D S) :
    GlobalLock S := by
  exact admissible_globalLock
    (level P) S
    (preCaseCAdmissible_admissible P D S h)

theorem preCaseCAdmissible_lowPrimeLocks
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : PreCaseCAdmissibleSupport P D S) :
    LowPrimePowerLocks (level P) S := by
  exact admissible_lowPrimeLocks
    (level P) S
    (preCaseCAdmissible_admissible P D S h)

def CaseCAdmissibleSupport
    (P : Params) (D : ClosureData P)
    (S : Support) : Prop :=
  InTruncatedDomain P D S ∧
  AdmissibleSupportAtLevel (level P) S ∧
  LocksC P D S ∧
  supportN S ≤ cap P D ∧
  supportCard S ≤ width P

@[simp] theorem CaseCAdmissibleSupport_def
    (P : Params) (D : ClosureData P)
    (S : Support) :
    CaseCAdmissibleSupport P D S =
      (InTruncatedDomain P D S ∧
        AdmissibleSupportAtLevel (level P) S ∧
        LocksC P D S ∧
        supportN S ≤ cap P D ∧
        supportCard S ≤ width P) := rfl

theorem caseCAdmissible_inTruncatedDomain
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : CaseCAdmissibleSupport P D S) :
    InTruncatedDomain P D S := h.1

theorem caseCAdmissible_admissible
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : CaseCAdmissibleSupport P D S) :
    AdmissibleSupportAtLevel (level P) S := h.2.1

theorem caseCAdmissible_locksC
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : CaseCAdmissibleSupport P D S) :
    LocksC P D S := h.2.2.1

theorem caseCAdmissible_belowCap
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : CaseCAdmissibleSupport P D S) :
    supportN S ≤ cap P D := h.2.2.2.1

theorem caseCAdmissible_card_le_width
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : CaseCAdmissibleSupport P D S) :
    supportCard S ≤ width P := h.2.2.2.2

theorem caseCAdmissible_of_pre
    (P : Params) (D : ClosureData P)
    (S : Support)
    (hPre : PreCaseCAdmissibleSupport P D S)
    (hLocksC : LocksC P D S)
    (hCap : supportN S ≤ cap P D)
    (hWidth : supportCard S ≤ width P) :
    CaseCAdmissibleSupport P D S := by
  exact ⟨
    preCaseCAdmissible_inTruncatedDomain P D S hPre,
    preCaseCAdmissible_admissible P D S hPre,
    hLocksC,
    hCap,
    hWidth
  ⟩

theorem caseCAdmissible_to_pre
    (P : Params) (D : ClosureData P)
    (S : Support)
    (h : CaseCAdmissibleSupport P D S) :
    PreCaseCAdmissibleSupport P D S := by
  exact ⟨
    caseCAdmissible_inTruncatedDomain P D S h,
    caseCAdmissible_admissible P D S h,
    locksC_to_preLocksC P D S
      (caseCAdmissible_locksC P D S h)
  ⟩

def PrefixSupport (pref : Prefix) : Support :=
  pref.support

@[simp] theorem PrefixSupport_def (pref : Prefix) :
    PrefixSupport pref = pref.support := rfl

def ExtensionByPrime (S : Support) (p : ℕ) : Support :=
  insert p S

@[simp] theorem ExtensionByPrime_def (S : Support) (p : ℕ) :
    ExtensionByPrime S p = insert p S := rfl

def IsNewPrimeExtension (S : Support) (p : ℕ) : Prop :=
  Nat.Prime p ∧
  p ∉ S ∧
  ∀ q ∈ S, q < p

@[simp] theorem IsNewPrimeExtension_def (S : Support) (p : ℕ) :
    IsNewPrimeExtension S p =
      (Nat.Prime p ∧
        p ∉ S ∧
        ∀ q ∈ S, q < p) := rfl

def CandInfinity
    (y : ℕ) (S : Support) (p : ℕ) : Prop :=
  IsNewPrimeExtension S p ∧
  AdmissibleSupportAtLevel y (ExtensionByPrime S p) ∧
  LocksB y (ExtensionByPrime S p)

@[simp] theorem CandInfinity_def
    (y : ℕ) (S : Support) (p : ℕ) :
    CandInfinity y S p =
      (IsNewPrimeExtension S p ∧
        AdmissibleSupportAtLevel y (ExtensionByPrime S p) ∧
        LocksB y (ExtensionByPrime S p)) := rfl

def CandN
    (P : Params) (D : ClosureData P)
    (S : Support) (p : ℕ) : Prop :=
  CandInfinity (level P) S p ∧
  p ≤ cap P D ∧
  LocksC P D (ExtensionByPrime S p)

@[simp] theorem CandN_def
    (P : Params) (D : ClosureData P)
    (S : Support) (p : ℕ) :
    CandN P D S p =
      (CandInfinity (level P) S p ∧
        p ≤ cap P D ∧
        LocksC P D (ExtensionByPrime S p)) := rfl

def CandNEmpty
    (P : Params) (D : ClosureData P)
    (S : Support) : Prop :=
  ∀ p : ℕ, ¬ CandN P D S p

@[simp] theorem CandNEmpty_def
    (P : Params) (D : ClosureData P)
    (S : Support) :
    CandNEmpty P D S = (∀ p : ℕ, ¬ CandN P D S p) := rfl

def IsMinimalCandN
    (P : Params) (D : ClosureData P)
    (S : Support) (p : ℕ) : Prop :=
  CandN P D S p ∧
  ∀ q : ℕ, CandN P D S q → p ≤ q

@[simp] theorem IsMinimalCandN_def
    (P : Params) (D : ClosureData P)
    (S : Support) (p : ℕ) :
    IsMinimalCandN P D S p =
      (CandN P D S p ∧
        ∀ q : ℕ, CandN P D S q → p ≤ q) := rfl

def TruncatedExtensionCompleteness
    (P : Params) (D : ClosureData P)
    (S : Support) : Prop :=
  ∀ S' : Support,
    CaseCAdmissibleSupport P D S' →
    S ⊂ S' →
    (∀ p ∈ S', p ∉ S → p ≤ cap P D) →
    ∃ p : ℕ,
      p ∈ S' ∧
      p ∉ S ∧
      IsMinimalCandN P D S p

@[simp] theorem TruncatedExtensionCompleteness_def
    (P : Params) (D : ClosureData P)
    (S : Support) :
    TruncatedExtensionCompleteness P D S =
      (∀ S' : Support,
        CaseCAdmissibleSupport P D S' →
        S ⊂ S' →
        (∀ p ∈ S', p ∉ S → p ≤ cap P D) →
        ∃ p : ℕ,
          p ∈ S' ∧
          p ∉ S ∧
          IsMinimalCandN P D S p) := rfl

def PrefixCoversSupport (p : Prefix) (S : Support) : Prop :=
  S ∈ Cylinder p

@[simp] theorem PrefixCoversSupport_def
    (p : Prefix) (S : Support) :
    PrefixCoversSupport p S = (S ∈ Cylinder p) := rfl

def ChildPrefixesCoverSupport
    (children : ChildPrefixes) (S : Support) : Prop :=
  ∃ child : Prefix,
    child ∈ children ∧ PrefixCoversSupport child S

@[simp] theorem ChildPrefixesCoverSupport_def
    (children : ChildPrefixes) (S : Support) :
    ChildPrefixesCoverSupport children S =
      (∃ child : Prefix,
        child ∈ children ∧ PrefixCoversSupport child S) := rfl

def RootPrefix (P : Params) : Prefix :=
  Prefix.mk {level P}

@[simp] theorem RootPrefix_support (P : Params) :
    (RootPrefix P).support = {level P} := rfl

def RootCoversDomain
    (P : Params) (D : ClosureData P) : Prop :=
  ∀ S : Support,
    CaseCAdmissibleSupport P D S →
    PrefixCoversSupport (RootPrefix P) S

@[simp] theorem RootCoversDomain_def
    (P : Params) (D : ClosureData P) :
    RootCoversDomain P D =
      (∀ S : Support,
        CaseCAdmissibleSupport P D S →
        PrefixCoversSupport (RootPrefix P) S) := rfl

inductive ExclusionKind where
  | nonIntegrality
  | globalLockFailure
  | lowPrimeLockFailure
  | capFailure
  | omegaFailure
  | candNFailure
deriving DecidableEq

def ExclusionKindViolation
    (P : Params) (D : ClosureData P)
    (k : ExclusionKind) (S : Support) : Prop :=
  match k with
  | .nonIntegrality =>
      supportNonIntegral S
  | .globalLockFailure =>
      ¬ GlobalLock S
  | .lowPrimeLockFailure =>
      ¬ LowPrimePowerLocks (level P) S
  | .capFailure =>
      ¬ supportN S ≤ cap P D
  | .omegaFailure =>
      ¬ supportCard S ≤ omegaBound P D
  | .candNFailure =>
      CandNEmpty P D S

theorem exclusionKindViolation_contradicts_admissible
    (P : Params) (D : ClosureData P)
    (k : ExclusionKind) (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hV : ExclusionKindViolation P D k S)
    (hCandClosed :
      k = ExclusionKind.candNFailure →
        CandNEmpty P D S →
        False)
    (hNonInt :
      k = ExclusionKind.nonIntegrality →
        supportNonIntegral S →
        False) :
    False := by
  cases k with
  | nonIntegrality =>
      exact hNonInt rfl hV
  | globalLockFailure =>
      exact hV
        (admissible_globalLock
          (level P) S
          (caseCAdmissible_admissible P D S hAdm))
  | lowPrimeLockFailure =>
      exact hV
        (admissible_lowPrimeLocks
          (level P) S
          (caseCAdmissible_admissible P D S hAdm))
  | capFailure =>
      exact hV (caseCAdmissible_belowCap P D S hAdm)
  | omegaFailure =>
      exact hV (caseCAdmissible_inTruncatedDomain P D S hAdm).2
  | candNFailure =>
      exact hCandClosed rfl hV

structure EmptinessData
    (P : Params) (D : ClosureData P)
    (pref : Prefix) where
  noAdmissibleSupport :
    ∀ S : Support,
      CaseCAdmissibleSupport P D S →
      PrefixCoversSupport pref S →
      False

structure ExclusionData
    (P : Params) (D : ClosureData P)
    (pref : Prefix) where
  kind : ExclusionKind
  violationHolds :
    ∀ S : Support,
      CaseCAdmissibleSupport P D S →
      PrefixCoversSupport pref S →
      ExclusionKindViolation P D kind S

structure FiniteReductionData
    (P : Params) (D : ClosureData P)
    (pref : Prefix) where
  children : ChildPrefixes
  childrenCover :
    ∀ S : Support,
      CaseCAdmissibleSupport P D S →
      PrefixCoversSupport pref S →
      ChildPrefixesCoverSupport children S
  descentMeasure : Prefix → ℕ
  childDescends :
    ∀ child : Prefix,
      child ∈ children →
      descentMeasure child < descentMeasure pref

inductive LocalClosureData
    (P : Params) (D : ClosureData P)
    (pref : Prefix) : Type where
  | emptiness :
      EmptinessData P D pref →
      LocalClosureData P D pref
  | exclusion :
      ExclusionData P D pref →
      LocalClosureData P D pref
  | finiteReduction :
      FiniteReductionData P D pref →
      LocalClosureData P D pref

def LocalClosureData.kind
    {P : Params} {D : ClosureData P} {pref : Prefix} :
    LocalClosureData P D pref → LocalClosureKind
  | .emptiness _ => LocalClosureKind.emptiness
  | .exclusion _ => LocalClosureKind.exclusion
  | .finiteReduction _ => LocalClosureKind.finiteReduction

def LocalClosureData.children
    {P : Params} {D : ClosureData P} {pref : Prefix} :
    LocalClosureData P D pref → ChildPrefixes
  | .emptiness _ => []
  | .exclusion _ => []
  | .finiteReduction d => d.children

@[simp] theorem LocalClosureData.kind_emptiness
    {P : Params} {D : ClosureData P} {pref : Prefix}
    (d : EmptinessData P D pref) :
    (LocalClosureData.emptiness d).kind = LocalClosureKind.emptiness := rfl

@[simp] theorem LocalClosureData.kind_exclusion
    {P : Params} {D : ClosureData P} {pref : Prefix}
    (d : ExclusionData P D pref) :
    (LocalClosureData.exclusion d).kind = LocalClosureKind.exclusion := rfl

@[simp] theorem LocalClosureData.kind_finiteReduction
    {P : Params} {D : ClosureData P} {pref : Prefix}
    (d : FiniteReductionData P D pref) :
    (LocalClosureData.finiteReduction d).kind = LocalClosureKind.finiteReduction := rfl

@[simp] theorem LocalClosureData.children_emptiness
    {P : Params} {D : ClosureData P} {pref : Prefix}
    (d : EmptinessData P D pref) :
    (LocalClosureData.emptiness d).children = [] := rfl

@[simp] theorem LocalClosureData.children_exclusion
    {P : Params} {D : ClosureData P} {pref : Prefix}
    (d : ExclusionData P D pref) :
    (LocalClosureData.exclusion d).children = [] := rfl

@[simp] theorem LocalClosureData.children_finiteReduction
    {P : Params} {D : ClosureData P} {pref : Prefix}
    (d : FiniteReductionData P D pref) :
    (LocalClosureData.finiteReduction d).children = d.children := rfl

structure RecordData
    (P : Params) (D : ClosureData P) where
  pref : Prefix
  closure : LocalClosureData P D pref

def recordKind
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : LocalClosureKind :=
  r.closure.kind

@[simp] theorem recordKind_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    recordKind r = r.closure.kind := rfl

def recordChildren
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : ChildPrefixes :=
  r.closure.children

@[simp] theorem recordChildren_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    recordChildren r = r.closure.children := rfl

def recordCylinder
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Set Support :=
  Cylinder r.pref

@[simp] theorem recordCylinder_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    recordCylinder r = Cylinder r.pref := rfl

def recordCoversSupport
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) : Prop :=
  PrefixCoversSupport r.pref S

@[simp] theorem recordCoversSupport_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) :
    recordCoversSupport r S = PrefixCoversSupport r.pref S := rfl

theorem emptinessData_closes_support
    (P : Params) (D : ClosureData P)
    (pref : Prefix)
    (d : EmptinessData P D pref)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : PrefixCoversSupport pref S) :
    False := by
  exact d.noAdmissibleSupport S hAdm hCov

theorem exclusionData_produces_violation
    (P : Params) (D : ClosureData P)
    (pref : Prefix)
    (d : ExclusionData P D pref)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : PrefixCoversSupport pref S) :
    ExclusionKindViolation P D d.kind S := by
  exact d.violationHolds S hAdm hCov

theorem exclusionData_closes_support
    (P : Params) (D : ClosureData P)
    (pref : Prefix)
    (d : ExclusionData P D pref)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : PrefixCoversSupport pref S)
    (hCandClosed :
      d.kind = ExclusionKind.candNFailure →
        CandNEmpty P D S →
        False)
    (hNonInt :
      d.kind = ExclusionKind.nonIntegrality →
        supportNonIntegral S →
        False) :
    False := by
  exact exclusionKindViolation_contradicts_admissible
    P D d.kind S hAdm
    (d.violationHolds S hAdm hCov)
    hCandClosed hNonInt

theorem finiteReductionData_routes_support_to_child
    (P : Params) (D : ClosureData P)
    (pref : Prefix)
    (d : FiniteReductionData P D pref)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : PrefixCoversSupport pref S) :
    ChildPrefixesCoverSupport d.children S := by
  exact d.childrenCover S hAdm hCov

theorem finiteReductionData_child_descends
    (P : Params) (D : ClosureData P)
    (pref child : Prefix)
    (d : FiniteReductionData P D pref)
    (hChild : child ∈ d.children) :
    d.descentMeasure child < d.descentMeasure pref := by
  exact d.childDescends child hChild

abbrev RecordFamily
    (P : Params) (D : ClosureData P) :=
  List (RecordData P D)

def CertificateCoversSupport
    (P : Params) (D : ClosureData P)
    (records : RecordFamily P D)
    (S : Support) : Prop :=
  ∃ r : RecordData P D,
    r ∈ records ∧
    recordCoversSupport r S

@[simp] theorem CertificateCoversSupport_def
    (P : Params) (D : ClosureData P)
    (records : RecordFamily P D)
    (S : Support) :
    CertificateCoversSupport P D records S =
      (∃ r : RecordData P D,
        r ∈ records ∧
        recordCoversSupport r S) := rfl

structure GlobalCertificate
    (P : Params) (D : ClosureData P) where
  records : RecordFamily P D
  gapBootstrap : CaseCGapBootstrapData P D
  rootCovers : RootCoversDomain P D
  coversDomain :
    ∀ S : Support,
      CaseCAdmissibleSupport P D S →
      CertificateCoversSupport P D records S

def certificateRecords
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D) : RecordFamily P D :=
  C.records

@[simp] theorem certificateRecords_def
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D) :
    certificateRecords C = C.records := rfl

def certificatePrefixes
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D) : List Prefix :=
  C.records.map (fun r => r.pref)

@[simp] theorem certificatePrefixes_def
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D) :
    certificatePrefixes C = C.records.map (fun r => r.pref) := rfl

theorem globalCertificate_covers_support
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    CertificateCoversSupport P D C.records S := by
  exact C.coversDomain S hAdm

def mkEmptinessRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : EmptinessData P D p) :
    RecordData P D :=
  { pref := p, closure := LocalClosureData.emptiness d }

def mkExclusionRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : ExclusionData P D p) :
    RecordData P D :=
  { pref := p, closure := LocalClosureData.exclusion d }

def mkFiniteReductionRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : FiniteReductionData P D p) :
    RecordData P D :=
  { pref := p, closure := LocalClosureData.finiteReduction d }

@[simp] theorem recordKind_mkEmptinessRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : EmptinessData P D p) :
    recordKind (mkEmptinessRecord P D p d) = LocalClosureKind.emptiness := rfl

@[simp] theorem recordKind_mkExclusionRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : ExclusionData P D p) :
    recordKind (mkExclusionRecord P D p d) = LocalClosureKind.exclusion := rfl

@[simp] theorem recordKind_mkFiniteReductionRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : FiniteReductionData P D p) :
    recordKind (mkFiniteReductionRecord P D p d) = LocalClosureKind.finiteReduction := rfl

@[simp] theorem recordChildren_mkEmptinessRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : EmptinessData P D p) :
    recordChildren (mkEmptinessRecord P D p d) = [] := rfl

@[simp] theorem recordChildren_mkExclusionRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : ExclusionData P D p) :
    recordChildren (mkExclusionRecord P D p d) = [] := rfl

@[simp] theorem recordChildren_mkFiniteReductionRecord
    (P : Params) (D : ClosureData P)
    (p : Prefix)
    (d : FiniteReductionData P D p) :
    recordChildren (mkFiniteReductionRecord P D p d) = d.children := rfl

end Certificate
end CaseC
end Lehmer