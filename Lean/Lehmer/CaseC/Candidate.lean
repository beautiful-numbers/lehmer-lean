-- FILE: Lean/Lehmer/CaseC/Candidate.lean
/-
IMPORT CLASSIFICATION

Lehmer.Prelude : meta
Lehmer.Basic.Defs : def
Lehmer.CaseC.Spec : def
Lehmer.CaseC.StateMachine.State : def thm
Lehmer.CaseC.StateMachine.Domain : def thm
Lehmer.CaseC.Certificate.Format : def thm
Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.StateMachine.State
import Lehmer.CaseC.StateMachine.Domain
import Lehmer.CaseC.Certificate.Format
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC

open Lehmer.Basic
open Lehmer.Pipeline

def candidateSupport (n : ℕ) : Support :=
  Lehmer.Basic.primeSupport n

@[simp] theorem candidateSupport_def (n : ℕ) :
    candidateSupport n = Lehmer.Basic.primeSupport n := rfl

def candidateState (P : Params) (n : ℕ) : State P :=
  State.mk (candidateSupport n)

@[simp] theorem candidateState_support (P : Params) (n : ℕ) :
    (candidateState P n).support = candidateSupport n := rfl

@[simp] theorem candidateState_mk (P : Params) (n : ℕ) :
    candidateState P n = State.mk (candidateSupport n) := rfl

def CandidateRealizesSupport (n : ℕ) (S : Support) : Prop :=
  candidateSupport n = S

@[simp] theorem CandidateRealizesSupport_def (n : ℕ) (S : Support) :
    CandidateRealizesSupport n S = (candidateSupport n = S) := rfl

def CandidateRealizesState (P : Params) (n : ℕ) (U : State P) : Prop :=
  CandidateRealizesSupport n U.support

@[simp] theorem CandidateRealizesState_def (P : Params) (n : ℕ) (U : State P) :
    CandidateRealizesState P n U = CandidateRealizesSupport n U.support := rfl

theorem candidate_realizes_candidateSupport
    (n : ℕ) :
    CandidateRealizesSupport n (candidateSupport n) := by
  rfl

theorem candidate_realizes_candidateState
    (P : Params) (n : ℕ) :
    CandidateRealizesState P n (candidateState P n) := by
  rfl

def CandidateSupportBelowClosureData
    (P : Params) (D : ClosureData P) (n : ℕ) : Prop :=
  SupportBelow D.N (candidateSupport n)

@[simp] theorem CandidateSupportBelowClosureData_def
    (P : Params) (D : ClosureData P) (n : ℕ) :
    CandidateSupportBelowClosureData P D n =
      SupportBelow D.N (candidateSupport n) := rfl

def CandidateSupportWithinOmega
    (P : Params) (D : ClosureData P) (n : ℕ) : Prop :=
  SupportWithinOmega D.omegaHat (candidateSupport n)

@[simp] theorem CandidateSupportWithinOmega_def
    (P : Params) (D : ClosureData P) (n : ℕ) :
    CandidateSupportWithinOmega P D n =
      SupportWithinOmega D.omegaHat (candidateSupport n) := rfl

def CandidateInTruncatedDomain
    (P : Params) (D : ClosureData P) (n : ℕ) : Prop :=
  CandidateSupportBelowClosureData P D n ∧
    CandidateSupportWithinOmega P D n

@[simp] theorem CandidateInTruncatedDomain_def
    (P : Params) (D : ClosureData P) (n : ℕ) :
    CandidateInTruncatedDomain P D n =
      (CandidateSupportBelowClosureData P D n ∧
        CandidateSupportWithinOmega P D n) := rfl

theorem candidateState_stateSupport
    (P : Params) (n : ℕ) :
    StateMachine.stateSupport P (candidateState P n) = candidateSupport n := by
  rfl

theorem candidateState_stateCard
    (P : Params) (n : ℕ) :
    StateMachine.stateCard P (candidateState P n) =
      supportCard (candidateSupport n) := by
  rfl

theorem candidateState_statePrefix
    (P : Params) (n : ℕ) :
    StateMachine.statePrefix P (candidateState P n) =
      Prefix.mk (candidateSupport n) := by
  rfl

theorem candidateState_has_self_prefix
    (P : Params) (n : ℕ) :
    StateMachine.stateHasPrefix P (Prefix.mk (candidateSupport n)) (candidateState P n) := by
  simp [StateMachine.stateHasPrefix, IsPrefixOf]

theorem candidateState_support_below
    (P : Params) (D : ClosureData P) {n : ℕ}
    (hDom : CandidateInTruncatedDomain P D n) :
    SupportBelow D.N (candidateSupport n) := by
  exact hDom.1

theorem candidateState_support_within_omega
    (P : Params) (D : ClosureData P) {n : ℕ}
    (hDom : CandidateInTruncatedDomain P D n) :
    SupportWithinOmega D.omegaHat (candidateSupport n) := by
  exact hDom.2

theorem candidateState_inDomain_of_candidateInTruncatedDomain
    (P : Params) (D : ClosureData P) {n : ℕ}
    (hDom : CandidateInTruncatedDomain P D n) :
    StateMachine.InDomain P D (candidateState P n) := by
  exact StateMachine.inDomain_intro P D (candidateState P n)
    (by
      simpa [candidateState_stateSupport] using
        candidateState_support_below P D hDom)
    (by
      simpa [candidateState_stateSupport] using
        candidateState_support_within_omega P D hDom)

def candidateDomainState
    (P : Params) (D : ClosureData P) (n : ℕ)
    (hDom : CandidateInTruncatedDomain P D n) :
    StateMachine.DomainState P D :=
  StateMachine.DomainState.mk
    (candidateState P n)
    (candidateState_inDomain_of_candidateInTruncatedDomain P D hDom)

@[simp] theorem candidateDomainState_val
    (P : Params) (D : ClosureData P) (n : ℕ)
    (hDom : CandidateInTruncatedDomain P D n) :
    (candidateDomainState P D n hDom).val = candidateState P n := rfl

structure CaseCPivotAlignment (P : Params) where
  pivot_eq_level :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      pivotOf n = level P
  widthCalibration : True

theorem CaseCPivotAlignment.pivot_eq_level_apply
    (P : Params)
    (A : CaseCPivotAlignment P)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    pivotOf n = level P := by
  exact A.pivot_eq_level hL hC

theorem CaseCPivotAlignment.widthCalibration_holds
    (P : Params)
    (A : CaseCPivotAlignment P) :
    True := by
  exact A.widthCalibration

structure CaseCAdmissibilityFromLehmer
    (P : Params) where
  oddSquarefree :
    ∀ {n : ℕ},
      LehmerComposite n →
      Certificate.IsOddPrimeSupport (candidateSupport n)
  rough_at_pivot :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.RoughAtLevel (level P) (candidateSupport n)
  global_lock :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.GlobalLock (candidateSupport n)
  low_prime_locks :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.LowPrimePowerLocks (level P) (candidateSupport n)

theorem admissibleSupportAtLevel_of_caseCLehmer
    (P : Params)
    (A : CaseCAdmissibilityFromLehmer P)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.AdmissibleSupportAtLevel
      (level P) (candidateSupport n) := by
  exact ⟨
    A.rough_at_pivot hL hC,
    A.oddSquarefree hL,
    A.global_lock hL hC,
    A.low_prime_locks hL hC
  ⟩

structure CaseCLockSoundnessFromPaper
    (P : Params) (D : ClosureData P) where
  locksB_of_candidate :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.LocksB (level P) (candidateSupport n)
  locksC_of_candidate :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.LocksC P D (candidateSupport n)

theorem locksB_of_caseCLehmer
    (P : Params) (D : ClosureData P)
    (L : CaseCLockSoundnessFromPaper P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.LocksB (level P) (candidateSupport n) := by
  exact L.locksB_of_candidate hL hC

theorem locksC_of_caseCLehmer
    (P : Params) (D : ClosureData P)
    (L : CaseCLockSoundnessFromPaper P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.LocksC P D (candidateSupport n) := by
  exact L.locksC_of_candidate hL hC

structure CaseCBootstrapBounds
    (P : Params) (D : ClosureData P) where
  cap_is_validated : True
  supportProd_below_cap :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.supportN (candidateSupport n) ≤ cap P D
  supportBelow_cap :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      SupportBelow D.N (candidateSupport n)
  supportWithinOmega :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      SupportWithinOmega D.omegaHat (candidateSupport n)
  omegaHat_lt_width :
    omegaBound P D < width P

theorem CaseCBootstrapBounds.cap_validated
    (P : Params) (D : ClosureData P)
    (B : CaseCBootstrapBounds P D) :
    True := by
  exact B.cap_is_validated

theorem card_le_width_of_bootstrap
    (P : Params) (D : ClosureData P)
    (B : CaseCBootstrapBounds P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    supportCard (candidateSupport n) ≤ width P := by
  exact le_trans (B.supportWithinOmega hL hC)
    (Nat.le_of_lt B.omegaHat_lt_width)

structure CaseCCandidatePaperData
    (P : Params) (D : ClosureData P) where
  pivot :
    CaseCPivotAlignment P
  admissibility :
    CaseCAdmissibilityFromLehmer P
  locks :
    CaseCLockSoundnessFromPaper P D
  bootstrap :
    CaseCBootstrapBounds P D

theorem CaseCCandidatePaperData.pivot_eq_level
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePaperData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    pivotOf n = level P := by
  exact A.pivot.pivot_eq_level hL hC

theorem CaseCCandidatePaperData.in_truncated_domain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePaperData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    InTruncatedDomain P D (candidateSupport n) := by
  exact ⟨
    A.bootstrap.supportBelow_cap hL hC,
    A.bootstrap.supportWithinOmega hL hC
  ⟩

theorem CaseCCandidatePaperData.candidateInTruncatedDomain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePaperData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    CandidateInTruncatedDomain P D n := by
  exact ⟨
    A.bootstrap.supportBelow_cap hL hC,
    A.bootstrap.supportWithinOmega hL hC
  ⟩

theorem CaseCCandidatePaperData.state_inDomain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePaperData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    StateMachine.InDomain P D (candidateState P n) := by
  exact candidateState_inDomain_of_candidateInTruncatedDomain
    P D (A.candidateInTruncatedDomain P D hL hC)

theorem caseCCandidateAdmissible_of_paperData
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePaperData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.CaseCAdmissibleSupport P D (candidateSupport n) := by
  exact ⟨
    ⟨
      A.bootstrap.supportBelow_cap hL hC,
      A.bootstrap.supportWithinOmega hL hC
    ⟩,
    admissibleSupportAtLevel_of_caseCLehmer P A.admissibility hL hC,
    A.locks.locksC_of_candidate hL hC,
    A.bootstrap.supportProd_below_cap hL hC,
    card_le_width_of_bootstrap P D A.bootstrap hL hC
  ⟩

theorem CaseCCandidatePaperData.caseCAdmissibleSupport
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePaperData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.CaseCAdmissibleSupport P D (candidateSupport n) := by
  exact caseCCandidateAdmissible_of_paperData P D A hL hC

structure CaseCCandidateAdmissibilityPackage
    (P : Params) (D : ClosureData P) where
  admissible :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.CaseCAdmissibleSupport P D (candidateSupport n)

def CaseCCandidateAdmissibilityPackage.ofPaperData
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePaperData P D) :
    CaseCCandidateAdmissibilityPackage P D :=
  { admissible := by
      intro n hL hC
      exact caseCCandidateAdmissible_of_paperData P D A hL hC }

theorem CaseCCandidateAdmissibilityPackage.apply
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.CaseCAdmissibleSupport P D (candidateSupport n) := by
  exact A.admissible hL hC

theorem CaseCCandidateAdmissibilityPackage.in_truncated_domain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    InTruncatedDomain P D (candidateSupport n) := by
  exact Certificate.caseCAdmissible_inTruncatedDomain
    P D (candidateSupport n)
    (CaseCCandidateAdmissibilityPackage.apply P D A hL hC)

theorem CaseCCandidateAdmissibilityPackage.candidateInTruncatedDomain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    CandidateInTruncatedDomain P D n := by
  have hT :
      InTruncatedDomain P D (candidateSupport n) :=
    CaseCCandidateAdmissibilityPackage.in_truncated_domain
      P D A hL hC
  exact hT

theorem CaseCCandidateAdmissibilityPackage.state_inDomain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    StateMachine.InDomain P D (candidateState P n) := by
  exact candidateState_inDomain_of_candidateInTruncatedDomain
    P D
    (CaseCCandidateAdmissibilityPackage.candidateInTruncatedDomain
      P D A hL hC)

def candidateSupport_caseCAdmissibleFromPackage
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.CaseCAdmissibleSupport P D (candidateSupport n) :=
  CaseCCandidateAdmissibilityPackage.apply P D A hL hC

def candidateInTruncatedDomainFromPackage
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    CandidateInTruncatedDomain P D n :=
  CaseCCandidateAdmissibilityPackage.candidateInTruncatedDomain
    P D A hL hC

def candidateDomainStateOfCaseC
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    StateMachine.DomainState P D :=
  candidateDomainState P D n
    (candidateInTruncatedDomainFromPackage P D A hL hC)

@[simp] theorem candidateDomainStateOfCaseC_val
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    (candidateDomainStateOfCaseC P D A hL hC).val =
      candidateState P n := rfl

end CaseC
end Lehmer