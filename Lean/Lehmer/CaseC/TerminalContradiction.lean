-- FILE: Lean/Lehmer/CaseC/TerminalContradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Candidate : def thm
- Lehmer.CaseC.GapClosure.GapToClosure : def thm
- Lehmer.CaseC.StateMachine.ResidualClosure : def thm
- Lehmer.CaseC.Certificate.Format : def thm
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.VerifiedRecordSoundness : def thm
- Lehmer.CaseC.Certificate.TerminalSoundness : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Candidate
import Lehmer.CaseC.GapClosure.GapToClosure
import Lehmer.CaseC.StateMachine.ResidualClosure
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.VerifiedRecordSoundness
import Lehmer.CaseC.Certificate.TerminalSoundness
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC

open Lehmer.Basic
open Lehmer.Pipeline

structure CaseCCandidatePreAdmissibilityPackage
    (P : Params) (D : ClosureData P) where
  preAdmissible :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n)

theorem CaseCCandidatePreAdmissibilityPackage.apply
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePreAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n) := by
  exact A.preAdmissible hL hC

theorem CaseCCandidatePreAdmissibilityPackage.in_truncated_domain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidatePreAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    InTruncatedDomain P D (candidateSupport n) := by
  exact Certificate.preCaseCAdmissible_inTruncatedDomain
    P D (candidateSupport n)
    (CaseCCandidatePreAdmissibilityPackage.apply P D A hL hC)

structure CaseCCandidateFullAdmissibilityPackage
    (P : Params) (D : ClosureData P) where
  fullAdmissible :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      Certificate.CaseCAdmissibleSupport P D (candidateSupport n)

theorem CaseCCandidateFullAdmissibilityPackage.apply
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateFullAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.CaseCAdmissibleSupport P D (candidateSupport n) := by
  exact A.fullAdmissible hL hC

theorem CaseCCandidateFullAdmissibilityPackage.in_truncated_domain
    (P : Params) (D : ClosureData P)
    (A : CaseCCandidateFullAdmissibilityPackage P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    InTruncatedDomain P D (candidateSupport n) := by
  exact Certificate.caseCAdmissible_inTruncatedDomain
    P D (candidateSupport n)
    (CaseCCandidateFullAdmissibilityPackage.apply P D A hL hC)

structure CaseCTerminalClosureContext
    (P : Params) (D : ClosureData P) where
  nonIntegralityClosed :
    ∀ S : Support,
      Certificate.PreCaseCAdmissibleSupport P D S →
      Certificate.supportNonIntegral S →
      False
  candNClosed :
    ∀ S : Support,
      Certificate.PreCaseCAdmissibleSupport P D S →
      Certificate.CandNEmpty P D S →
      False
  childClosed :
    ∀ child : Prefix,
      ∀ S : Support,
        Certificate.PreCaseCAdmissibleSupport P D S →
        Certificate.PrefixCoversSupport child S →
        False

def CaseCTerminalClosureContext.ofResidual
    (P : Params) (D : ClosureData P)
    (Γ : StateMachine.ResidualTerminalClosureContext P D) :
    CaseCTerminalClosureContext P D :=
  { nonIntegralityClosed := Γ.nonIntegralityClosed
    candNClosed := Γ.candNClosed
    childClosed := Γ.childClosed }

@[simp] theorem CaseCTerminalClosureContext.ofResidual_nonIntegrality
    (P : Params) (D : ClosureData P)
    (Γ : StateMachine.ResidualTerminalClosureContext P D) :
    (CaseCTerminalClosureContext.ofResidual P D Γ).nonIntegralityClosed =
      Γ.nonIntegralityClosed := rfl

@[simp] theorem CaseCTerminalClosureContext.ofResidual_candN
    (P : Params) (D : ClosureData P)
    (Γ : StateMachine.ResidualTerminalClosureContext P D) :
    (CaseCTerminalClosureContext.ofResidual P D Γ).candNClosed =
      Γ.candNClosed := rfl

@[simp] theorem CaseCTerminalClosureContext.ofResidual_child
    (P : Params) (D : ClosureData P)
    (Γ : StateMachine.ResidualTerminalClosureContext P D) :
    (CaseCTerminalClosureContext.ofResidual P D Γ).childClosed =
      Γ.childClosed := rfl

theorem CaseCTerminalClosureContext.close_nonIntegrality
    (P : Params) (D : ClosureData P)
    (Γ : CaseCTerminalClosureContext P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hNon : Certificate.supportNonIntegral S) :
    False := by
  exact Γ.nonIntegralityClosed S hPre hNon

theorem CaseCTerminalClosureContext.close_candN
    (P : Params) (D : ClosureData P)
    (Γ : CaseCTerminalClosureContext P D)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hEmpty : Certificate.CandNEmpty P D S) :
    False := by
  exact Γ.candNClosed S hPre hEmpty

theorem CaseCTerminalClosureContext.close_child
    (P : Params) (D : ClosureData P)
    (Γ : CaseCTerminalClosureContext P D)
    (child : Prefix)
    (S : Support)
    (hPre : Certificate.PreCaseCAdmissibleSupport P D S)
    (hCov : Certificate.PrefixCoversSupport child S) :
    False := by
  exact Γ.childClosed child S hPre hCov

structure CaseCCertificateData
    (P : Params) (D : ClosureData P) where
  certificate : Certificate.GlobalCertificate P D
  verifiedRecords :
    Certificate.VerifiedCertificateRecords P D certificate

theorem CaseCCertificateData.covers_preAdmissible_candidate
    (P : Params) (D : ClosureData P)
    (C : CaseCCertificateData P D)
    {n : ℕ}
    (_hPre : Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n))
    (hFull :
      Certificate.CaseCAdmissibleSupport P D (candidateSupport n)) :
    Certificate.GlobalCertificateCoversState P D
      C.certificate (candidateState P n) := by
  exact Certificate.globalCertificate_covers_admissible_state
    P D C.certificate (candidateState P n) hFull

structure CaseCTerminalData
    (P : Params) (D : ClosureData P) where
  gap :
    GapClosure.GapToClosurePackage P D
  residual :
    StateMachine.ResidualClosurePackage P D
  candidatePreAdmissibility :
    CaseCCandidatePreAdmissibilityPackage P D
  candidateFullAdmissibility :
    CaseCCandidateFullAdmissibilityPackage P D
  closureContext :
    CaseCTerminalClosureContext P D
  certificate :
    CaseCCertificateData P D
  verifiedRecordSoundnessContext :
    Certificate.VerifiedRecordSoundnessContext P D

theorem CaseCTerminalData.residual_closed
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    StateMachine.ResidualClosed P D X.residual.state := by
  exact X.residual.closed

theorem CaseCTerminalData.gap_ready
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    GapClosure.GapToClosureReady P D X.gap := by
  exact GapClosure.gapToClosureReady P D X.gap

theorem CaseCTerminalData.gap_omega_lt_width
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    GapClosure.gapClosureOmegahatValue P D
      (GapClosure.GapToClosurePackage.gap P D X.gap) < width P := by
  exact GapClosure.GapToClosurePackage.gap_omegahat_lt_width P D X.gap

theorem CaseCTerminalData.gap_bound_atLeastCap
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    cap P D ≤
      GapClosure.gapClosureBoundValue P D
        (GapClosure.GapToClosurePackage.gap P D X.gap) := by
  exact GapClosure.GapToClosurePackage.gap_bound_atLeastCap P D X.gap

theorem CaseCTerminalData.gap_bound_atLeastClosureN
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    D.N ≤
      GapClosure.gapClosureBoundValue P D
        (GapClosure.GapToClosurePackage.gap P D X.gap) := by
  exact GapClosure.GapToClosurePackage.gap_bound_atLeastClosureN P D X.gap

theorem CaseCTerminalData.gap_omegahat_matches_closureData
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    (hMatch :
      GapClosure.truncatedGapOmegahatMatchesClosureData
        P D (GapClosure.GapToClosurePackage.gap P D X.gap).data.data.data) :
    D.omegaHat =
      GapClosure.gapClosureOmegahatValue P D
        (GapClosure.GapToClosurePackage.gap P D X.gap) := by
  exact GapClosure.GapClosurePackage.omegahat_matches_closureData
    P D (GapClosure.GapToClosurePackage.gap P D X.gap) hMatch

theorem CaseCTerminalData.candidate_preAdmissible
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n) := by
  exact CaseCCandidatePreAdmissibilityPackage.apply
    P D X.candidatePreAdmissibility hL hC

theorem CaseCTerminalData.candidate_fullAdmissible
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.CaseCAdmissibleSupport P D (candidateSupport n) := by
  exact CaseCCandidateFullAdmissibilityPackage.apply
    P D X.candidateFullAdmissibility hL hC

theorem CaseCTerminalData.candidate_in_truncated_domain
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    InTruncatedDomain P D (candidateSupport n) := by
  exact Certificate.preCaseCAdmissible_inTruncatedDomain
    P D (candidateSupport n)
    (CaseCTerminalData.candidate_preAdmissible P D X hL hC)

theorem CaseCTerminalData.candidateInTruncatedDomain
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    CandidateInTruncatedDomain P D n := by
  exact CaseCTerminalData.candidate_in_truncated_domain P D X hL hC

theorem CaseCTerminalData.candidate_covered_by_certificate
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    Certificate.GlobalCertificateCoversState P D
      X.certificate.certificate (candidateState P n) := by
  have hFull :
      Certificate.CaseCAdmissibleSupport P D (candidateSupport n) :=
    CaseCTerminalData.candidate_fullAdmissible P D X hL hC
  exact Certificate.globalCertificate_covers_admissible_state
    P D X.certificate.certificate (candidateState P n) hFull

theorem CaseCTerminalData.certificate_closes_candidate
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  have hPre :
      Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n) :=
    CaseCTerminalData.candidate_preAdmissible P D X hL hC
  have hFull :
      Certificate.CaseCAdmissibleSupport P D (candidateSupport n) :=
    CaseCTerminalData.candidate_fullAdmissible P D X hL hC
  have hDom : CandidateInTruncatedDomain P D n := by
    have hTrunc : InTruncatedDomain P D (candidateSupport n) :=
      Certificate.preCaseCAdmissible_inTruncatedDomain
        P D (candidateSupport n) hPre
    exact hTrunc
  have hCover :
      Certificate.GlobalCertificateCoversState P D
        X.certificate.certificate (candidateState P n) := by
    exact Certificate.globalCertificate_covers_admissible_state
      P D X.certificate.certificate (candidateState P n) hFull
  exact Certificate.verifiedCertificateRecords_excludes_covered_candidate
    P D X.verifiedRecordSoundnessContext
    X.certificate.certificate X.certificate.verifiedRecords
    hL hC hFull hCover

theorem false_of_terminalData
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  exact CaseCTerminalData.certificate_closes_candidate P D X hL hC

theorem false_of_gap_residual_certificate
    (P : Params) (D : ClosureData P)
    (G : GapClosure.GapToClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (Γ : CaseCTerminalClosureContext P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  let X : CaseCTerminalData P D :=
    { gap := G
      residual := R
      candidatePreAdmissibility := Apre
      candidateFullAdmissibility := Afull
      closureContext := Γ
      certificate := C
      verifiedRecordSoundnessContext := VΓ }
  exact false_of_terminalData P D X hL hC

def CaseCTerminalData.ofResidualContext
    (P : Params) (D : ClosureData P)
    (G : GapClosure.GapToClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    CaseCTerminalData P D :=
  { gap := G
    residual := R
    candidatePreAdmissibility := Apre
    candidateFullAdmissibility := Afull
    closureContext := CaseCTerminalClosureContext.ofResidual P D Γ
    certificate := C
    verifiedRecordSoundnessContext := VΓ }

@[simp] theorem CaseCTerminalData.ofResidualContext_gap
    (P : Params) (D : ClosureData P)
    (G : GapClosure.GapToClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCTerminalData.ofResidualContext P D G R Apre Afull Γ C VΓ).gap = G := rfl

@[simp] theorem CaseCTerminalData.ofResidualContext_residual
    (P : Params) (D : ClosureData P)
    (G : GapClosure.GapToClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCTerminalData.ofResidualContext P D G R Apre Afull Γ C VΓ).residual = R := rfl

@[simp] theorem CaseCTerminalData.ofResidualContext_candidatePreAdmissibility
    (P : Params) (D : ClosureData P)
    (G : GapClosure.GapToClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCTerminalData.ofResidualContext P D G R Apre Afull Γ C VΓ).candidatePreAdmissibility =
      Apre := rfl

@[simp] theorem CaseCTerminalData.ofResidualContext_candidateFullAdmissibility
    (P : Params) (D : ClosureData P)
    (G : GapClosure.GapToClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCTerminalData.ofResidualContext P D G R Apre Afull Γ C VΓ).candidateFullAdmissibility =
      Afull := rfl

@[simp] theorem CaseCTerminalData.ofResidualContext_certificate
    (P : Params) (D : ClosureData P)
    (G : GapClosure.GapToClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (Apre : CaseCCandidatePreAdmissibilityPackage P D)
    (Afull : CaseCCandidateFullAdmissibilityPackage P D)
    (Γ : StateMachine.ResidualTerminalClosureContext P D)
    (C : CaseCCertificateData P D)
    (VΓ : Certificate.VerifiedRecordSoundnessContext P D) :
    (CaseCTerminalData.ofResidualContext P D G R Apre Afull Γ C VΓ).certificate = C := rfl

def CaseCImpossibleFromTerminalData
    (P : Params) (D : ClosureData P)
    (_X : CaseCTerminalData P D) : Prop :=
  ∀ n : ℕ, LehmerComposite n → InCaseC n → False

@[simp] theorem CaseCImpossibleFromTerminalData_def
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    CaseCImpossibleFromTerminalData P D X =
      (∀ n : ℕ, LehmerComposite n → InCaseC n → False) := rfl

theorem caseCImpossible_of_terminalData
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    CaseCImpossibleFromTerminalData P D X := by
  intro n hL hC
  exact false_of_terminalData P D X hL hC

theorem false_of_terminalData_expanded
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  have hPre :
      Certificate.PreCaseCAdmissibleSupport P D (candidateSupport n) :=
    CaseCCandidatePreAdmissibilityPackage.apply
      P D X.candidatePreAdmissibility hL hC
  have hFull :
      Certificate.CaseCAdmissibleSupport P D (candidateSupport n) :=
    CaseCCandidateFullAdmissibilityPackage.apply
      P D X.candidateFullAdmissibility hL hC
  have hDom : CandidateInTruncatedDomain P D n := by
    have hTrunc : InTruncatedDomain P D (candidateSupport n) :=
      Certificate.preCaseCAdmissible_inTruncatedDomain
        P D (candidateSupport n) hPre
    exact hTrunc
  have hCover :
      Certificate.GlobalCertificateCoversState P D
        X.certificate.certificate (candidateState P n) := by
    exact Certificate.globalCertificate_covers_admissible_state
      P D X.certificate.certificate (candidateState P n) hFull
  exact Certificate.verifiedCertificateRecords_excludes_covered_candidate
    P D X.verifiedRecordSoundnessContext
    X.certificate.certificate X.certificate.verifiedRecords
    hL hC hFull hCover

def CaseCTerminalData.gap_package
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    GapClosure.GapToClosurePackage P D := by
  exact X.gap

def CaseCTerminalData.residual_package
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    StateMachine.ResidualClosurePackage P D := by
  exact X.residual

def CaseCTerminalData.certificate_data
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    CaseCCertificateData P D := by
  exact X.certificate

def CaseCTerminalData.preAdmissibility_package
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    CaseCCandidatePreAdmissibilityPackage P D := by
  exact X.candidatePreAdmissibility

def CaseCTerminalData.fullAdmissibility_package
    (P : Params) (D : ClosureData P)
    (X : CaseCTerminalData P D) :
    CaseCCandidateFullAdmissibilityPackage P D := by
  exact X.candidateFullAdmissibility

end CaseC
end Lehmer