-- FILE: Lean/Lehmer/CaseC/Main.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Candidate : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.CaseC.GapClosure.KmaxGap : def thm
- Lehmer.CaseC.GapClosure.GapToClosure : def thm
- Lehmer.CaseC.StateMachine.ResidualClosure : def thm
- Lehmer.CaseC.Certificate.Main : def thm
- Lehmer.CaseC.Certificate.VerifiedRecordSoundness : def thm
- Lehmer.CaseC.TerminalContradiction : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Candidate
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.KmaxGap
import Lehmer.CaseC.GapClosure.GapToClosure
import Lehmer.CaseC.StateMachine.ResidualClosure
import Lehmer.CaseC.Certificate.Main
import Lehmer.CaseC.Certificate.VerifiedRecordSoundness
import Lehmer.CaseC.TerminalContradiction
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC

open Lehmer.Basic
open Lehmer.Pipeline

def CaseCImpossible : Prop :=
  ∀ n : ℕ, LehmerComposite n → InCaseC n → False

@[simp] theorem CaseCImpossible_def :
    CaseCImpossible =
      (∀ n : ℕ, LehmerComposite n → InCaseC n → False) := rfl

structure CaseCMainPackage (P : Params) (D : ClosureData P) where
  nonIntegrality :
    GapClosure.NonIntegralityFamilyPackage P D
  gapToClosure :
    GapClosure.GapToClosurePackage P D
  nonIntegralityMatchesGap :
    nonIntegrality.family =
      GapClosure.gapClosureFamily P D
        (GapClosure.GapToClosurePackage.gap P D gapToClosure)
  residual :
    StateMachine.ResidualClosurePackage P D
  residualTerminalContext :
    StateMachine.ResidualTerminalClosureContext P D
  candidatePreAdmissibility :
    CaseCCandidatePreAdmissibilityPackage P D
  candidateFullAdmissibility :
    CaseCCandidateFullAdmissibilityPackage P D
  certificate :
    CaseCCertificateData P D
  verifiedRecordSoundnessContext :
    Certificate.VerifiedRecordSoundnessContext P D

@[simp] theorem CaseCMainPackage.nonIntegrality_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).nonIntegrality = NI := rfl

@[simp] theorem CaseCMainPackage.gapToClosure_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).gapToClosure = G := rfl

@[simp] theorem CaseCMainPackage.residual_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).residual = R := rfl

@[simp] theorem CaseCMainPackage.residualTerminalContext_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).residualTerminalContext = Γ := rfl

@[simp] theorem CaseCMainPackage.candidatePreAdmissibility_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).candidatePreAdmissibility =
      Apre := rfl

@[simp] theorem CaseCMainPackage.candidateFullAdmissibility_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).candidateFullAdmissibility =
      Afull := rfl

@[simp] theorem CaseCMainPackage.certificate_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).certificate = C := rfl

@[simp] theorem CaseCMainPackage.verifiedRecordSoundnessContext_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCMainPackage.mk NI G hNI R Γ Apre Afull C VΓ).verifiedRecordSoundnessContext = VΓ := rfl

def caseCMainGapToClosure
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    GapClosure.GapToClosurePackage P D :=
  X.gapToClosure

@[simp] theorem caseCMainGapToClosure_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainGapToClosure P D X = X.gapToClosure := rfl

def caseCMainGap
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    GapClosure.GapClosurePackage P D :=
  GapClosure.GapToClosurePackage.gap P D X.gapToClosure

@[simp] theorem caseCMainGap_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainGap P D X =
      GapClosure.GapToClosurePackage.gap P D X.gapToClosure := rfl

def caseCMainResidualClosure
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    StateMachine.ResidualClosurePackage P D :=
  X.residual

@[simp] theorem caseCMainResidualClosure_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainResidualClosure P D X = X.residual := rfl

def caseCMainResidualTerminalContext
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    StateMachine.ResidualTerminalClosureContext P D :=
  X.residualTerminalContext

@[simp] theorem caseCMainResidualTerminalContext_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainResidualTerminalContext P D X =
      X.residualTerminalContext := rfl

def caseCMainTerminalClosureContext
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCTerminalClosureContext P D :=
  CaseCTerminalClosureContext.ofResidual P D X.residualTerminalContext

@[simp] theorem caseCMainTerminalClosureContext_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainTerminalClosureContext P D X =
      CaseCTerminalClosureContext.ofResidual P D X.residualTerminalContext := rfl

def caseCMainCandidatePreAdmissibility
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCCandidatePreAdmissibilityPackage P D :=
  X.candidatePreAdmissibility

@[simp] theorem caseCMainCandidatePreAdmissibility_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainCandidatePreAdmissibility P D X =
      X.candidatePreAdmissibility := rfl

def caseCMainCandidateFullAdmissibility
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCCandidateFullAdmissibilityPackage P D :=
  X.candidateFullAdmissibility

@[simp] theorem caseCMainCandidateFullAdmissibility_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainCandidateFullAdmissibility P D X =
      X.candidateFullAdmissibility := rfl

def caseCMainCertificateData
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCCertificateData P D :=
  X.certificate

@[simp] theorem caseCMainCertificateData_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainCertificateData P D X = X.certificate := rfl

def caseCMainVerifiedRecordSoundnessContext
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    Certificate.VerifiedRecordSoundnessContext P D :=
  X.verifiedRecordSoundnessContext

@[simp] theorem caseCMainVerifiedRecordSoundnessContext_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainVerifiedRecordSoundnessContext P D X = X.verifiedRecordSoundnessContext := rfl

def caseCMainTerminalData
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCTerminalData P D :=
  { gap := X.gapToClosure
    residual := X.residual
    candidatePreAdmissibility := X.candidatePreAdmissibility
    candidateFullAdmissibility := X.candidateFullAdmissibility
    closureContext := CaseCTerminalClosureContext.ofResidual P D X.residualTerminalContext
    certificate := X.certificate
    verifiedRecordSoundnessContext := X.verifiedRecordSoundnessContext }

@[simp] theorem caseCMainTerminalData_gap
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (caseCMainTerminalData P D X).gap = X.gapToClosure := rfl

@[simp] theorem caseCMainTerminalData_residual
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (caseCMainTerminalData P D X).residual = X.residual := rfl

@[simp] theorem caseCMainTerminalData_candidatePreAdmissibility
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (caseCMainTerminalData P D X).candidatePreAdmissibility =
      X.candidatePreAdmissibility := rfl

@[simp] theorem caseCMainTerminalData_candidateFullAdmissibility
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (caseCMainTerminalData P D X).candidateFullAdmissibility =
      X.candidateFullAdmissibility := rfl

@[simp] theorem caseCMainTerminalData_certificate
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (caseCMainTerminalData P D X).certificate = X.certificate := rfl

@[simp] theorem caseCMainTerminalData_verifiedRecordSoundnessContext
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (caseCMainTerminalData P D X).verifiedRecordSoundnessContext = X.verifiedRecordSoundnessContext := rfl

def CaseCMainReady
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : Prop :=
  GapClosure.GapToClosureReady P D X.gapToClosure ∧
  StateMachine.ResidualClosed P D X.residual.state ∧
  True

@[simp] theorem CaseCMainReady_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCMainReady P D X =
      (GapClosure.GapToClosureReady P D X.gapToClosure ∧
        StateMachine.ResidualClosed P D X.residual.state ∧
        True) := rfl

theorem caseCMainReady
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCMainReady P D X := by
  exact ⟨
    GapClosure.gapToClosureReady P D X.gapToClosure,
    X.residual.closed,
    trivial
  ⟩

theorem caseCMain_gap_ready
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    GapClosure.GapToClosureReady P D X.gapToClosure := by
  exact GapClosure.gapToClosureReady P D X.gapToClosure

theorem caseCMain_omega_lt_width
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    GapClosure.gapClosureOmegahatValue P D
      (GapClosure.GapToClosurePackage.gap P D X.gapToClosure) < width P := by
  exact GapClosure.GapToClosurePackage.gap_omegahat_lt_width P D X.gapToClosure

theorem caseCMain_bound_atLeastCap
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    cap P D ≤
      GapClosure.gapClosureBoundValue P D
        (GapClosure.GapToClosurePackage.gap P D X.gapToClosure) := by
  exact GapClosure.GapToClosurePackage.gap_bound_atLeastCap P D X.gapToClosure

theorem caseCMain_bound_atLeastClosureN
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    D.N ≤
      GapClosure.gapClosureBoundValue P D
        (GapClosure.GapToClosurePackage.gap P D X.gapToClosure) := by
  exact GapClosure.GapToClosurePackage.gap_bound_atLeastClosureN P D X.gapToClosure

theorem caseCMain_omegahat_matches_closureData
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D)
    (hMatch :
      GapClosure.truncatedGapOmegahatMatchesClosureData
        P D
        (GapClosure.GapToClosurePackage.gap P D X.gapToClosure).data.data.data) :
    D.omegaHat =
      GapClosure.gapClosureOmegahatValue P D
        (GapClosure.GapToClosurePackage.gap P D X.gapToClosure) := by
  exact GapClosure.GapClosurePackage.omegahat_matches_closureData
    P D (GapClosure.GapToClosurePackage.gap P D X.gapToClosure) hMatch

def caseCMainGapFamily
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    GapClosure.SupportProfileFamily :=
  GapClosure.gapClosureFamily P D (caseCMainGap P D X)

@[simp] theorem caseCMainGapFamily_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainGapFamily P D X =
      GapClosure.gapClosureFamily P D (caseCMainGap P D X) := rfl

theorem caseCMainGapFamily_mem_hasWitness
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ R, R ∈ caseCMainGapFamily P D X →
      GapClosure.hasNonIntegralityWitness P D R := by
  intro R hR
  have hR' : R ∈ X.nonIntegrality.family := by
    rw[X.nonIntegralityMatchesGap]
    simpa [caseCMainGapFamily, caseCMainGap] using hR
  exact ⟨X.nonIntegrality.witnesses R hR'⟩

def caseCMainGapFamily_mem_rigid
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ R, R ∈ caseCMainGapFamily P D X →
      GapClosure.RigidProfile P D R := by
  intro R hR
  exact GapClosure.GapClosurePackage.member_rigid
    P D (caseCMainGap P D X) R hR

theorem caseCMainGapFamily_mem_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ R, R ∈ caseCMainGapFamily P D X →
      Certificate.PreCaseCAdmissibleSupport P D (GapClosure.profileSupport R) := by
  intro R hR
  exact GapClosure.GapClosurePackage.member_preAdmissible
    P D (caseCMainGap P D X) R hR

theorem caseCMainGapFamily_mem_admissibleAtLevel
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ R, R ∈ caseCMainGapFamily P D X →
      Certificate.AdmissibleSupportAtLevel (level P) (GapClosure.profileSupport R) := by
  intro R hR
  exact GapClosure.GapClosurePackage.member_admissibleAtLevel
    P D (caseCMainGap P D X) R hR

theorem caseCMainGapFamily_mem_locksB
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ R, R ∈ caseCMainGapFamily P D X →
      Certificate.LocksB (level P) (GapClosure.profileSupport R) := by
  intro R hR
  exact GapClosure.GapClosurePackage.member_locksB
    P D (caseCMainGap P D X) R hR

theorem caseCMainResidualClosed
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    StateMachine.ResidualClosed P D X.residual.state := by
  exact X.residual.closed

def caseCMainCertificate
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    Certificate.GlobalCertificate P D :=
  X.certificate.certificate

@[simp] theorem caseCMainCertificate_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainCertificate P D X = X.certificate.certificate := rfl

def caseCMainVerifiedRecords
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    Certificate.VerifiedCertificateRecords P D
      (caseCMainCertificate P D X) :=
  X.certificate.verifiedRecords

@[simp] theorem caseCMainVerifiedRecords_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainVerifiedRecords P D X =
      X.certificate.verifiedRecords := rfl

def caseCMainCertificateHead?
    (P : Params) (D : ClosureData P)
    (_X : CaseCMainPackage P D) : Option (Certificate.RecordData P D) :=
  none

@[simp] theorem caseCMainCertificateHead?_def
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainCertificateHead? P D X = none := rfl

theorem caseCMainCertificate_excludes_candidate
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  exact CaseCTerminalData.certificate_closes_candidate
    P D (caseCMainTerminalData P D X) hL hC

theorem CaseCMainPackage.impossible_pointwise
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  exact false_of_terminalData P D (caseCMainTerminalData P D X) hL hC

theorem caseCMain_terminalContradiction
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  exact false_of_terminalData
    P D (caseCMainTerminalData P D X) hL hC

theorem caseCImpossible_of_mainPackage
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCImpossible := by
  intro n hL hC
  exact CaseCMainPackage.impossible_pointwise P D X hL hC

theorem caseCMain_impossible_from_package
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCImpossible := by
  intro n hL hC
  exact caseCMain_terminalContradiction P D X hL hC

theorem not_inCaseC_of_LehmerComposite_from_package
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  intro hC
  exact CaseCMainPackage.impossible_pointwise P D X hL hC

def mkCaseCMainPackage
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    CaseCMainPackage P D :=
  { nonIntegrality := NI
    gapToClosure := G
    nonIntegralityMatchesGap := hNI
    residual := R
    residualTerminalContext := Γ
    candidatePreAdmissibility := Apre
    candidateFullAdmissibility := Afull
    certificate := C
    verifiedRecordSoundnessContext := VΓ }

@[simp] theorem mkCaseCMainPackage_nonIntegrality
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).nonIntegrality = NI := rfl

@[simp] theorem mkCaseCMainPackage_gapToClosure
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).gapToClosure = G := rfl

@[simp] theorem mkCaseCMainPackage_residual
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).residual = R := rfl

@[simp] theorem mkCaseCMainPackage_residualTerminalContext
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).residualTerminalContext = Γ := rfl

@[simp] theorem mkCaseCMainPackage_candidatePreAdmissibility
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).candidatePreAdmissibility =
      Apre := rfl

@[simp] theorem mkCaseCMainPackage_candidateFullAdmissibility
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).candidateFullAdmissibility =
      Afull := rfl

@[simp] theorem mkCaseCMainPackage_certificate
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).certificate = C := rfl

@[simp] theorem mkCaseCMainPackage_verifiedRecordSoundnessContext
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (G : GapClosure.GapToClosurePackage P D)
    (hNI :
      NI.family =
        GapClosure.gapClosureFamily P D
          (GapClosure.GapToClosurePackage.gap P D G))
    (R : StateMachine.ResidualClosurePackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (mkCaseCMainPackage P D NI G hNI R Γ Apre Afull C VΓ).verifiedRecordSoundnessContext = VΓ := rfl

theorem caseC_impossible_from_package
    (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  exact CaseCMainPackage.impossible_pointwise P D X hL hC

end CaseC
end Lehmer