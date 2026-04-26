-- FILE: Lean/Lehmer/CaseC/Certificate/TerminalSoundness.lean

/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Candidate : def thm
- Lehmer.CaseC.Certificate.Format : def thm
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.VerifiedRecordSoundness : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Candidate
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.VerifiedRecordSoundness
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic
open Lehmer.Pipeline

def CaseCCandidateAdmissible
    (P : Params) (D : ClosureData P)
    (n : ℕ) : Prop :=
  CaseCAdmissibleSupport P D (candidateSupport n)

@[simp] theorem CaseCCandidateAdmissible_def
    (P : Params) (D : ClosureData P)
    (n : ℕ) :
    CaseCCandidateAdmissible P D n =
      CaseCAdmissibleSupport P D (candidateSupport n) := rfl

theorem caseCCandidateAdmissible_support
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    CaseCAdmissibleSupport P D (candidateSupport n) := by
  exact hAdm

theorem caseCCandidateAdmissible_state_support
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    CaseCAdmissibleSupport P D (candidateState P n).support := by
  exact hAdm

theorem caseCCandidateAdmissible_inTruncatedDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    InTruncatedDomain P D (candidateSupport n) := by
  exact caseCAdmissible_inTruncatedDomain P D (candidateSupport n) hAdm

theorem caseCCandidateAdmissible_supportBelow
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    SupportBelow D.N (candidateSupport n) := by
  exact hAdm.1.1

theorem caseCCandidateAdmissible_withinOmega
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    SupportWithinOmega D.omegaHat (candidateSupport n) := by
  exact hAdm.1.2

theorem caseCCandidateAdmissible_candidateInTruncatedDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    CandidateInTruncatedDomain P D n := by
  exact ⟨
    caseCCandidateAdmissible_supportBelow P D hAdm,
    caseCCandidateAdmissible_withinOmega P D hAdm
  ⟩

theorem caseCCandidateAdmissible_stateInDomain
    (P : Params) (D : ClosureData P)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    StateMachine.InDomain P D (candidateState P n) := by
  exact candidateState_inDomain_of_candidateInTruncatedDomain
    P D (caseCCandidateAdmissible_candidateInTruncatedDomain P D hAdm)

structure CertificateTerminalInput
    (P : Params) (D : ClosureData P) where
  certificate : GlobalCertificate P D
  verifiedRecords : VerifiedCertificateRecords P D certificate
  soundnessContext : VerifiedRecordSoundnessContext P D

def CertificateTerminalInput.records
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D) :
    RecordFamily P D :=
  certificateRecords certInput.certificate

@[simp] theorem CertificateTerminalInput.records_def
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D) :
    certInput.records P D = certificateRecords certInput.certificate := rfl

theorem CertificateTerminalInput.covers_admissible_support
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    GlobalCertificateCoversSupport P D certInput.certificate S := by
  exact globalCertificate_covers_admissible_support
    P D certInput.certificate S hAdm

theorem CertificateTerminalInput.covers_admissible_state
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    GlobalCertificateCoversState P D certInput.certificate U := by
  exact globalCertificate_covers_admissible_state
    P D certInput.certificate U hAdm

theorem CertificateTerminalInput.covers_admissible_candidate
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    CandidateCoveredByCertificate P D certInput.certificate n := by
  exact globalCertificate_covers_admissible_state
    P D certInput.certificate (candidateState P n) hAdm

theorem CertificateTerminalInput.has_record_covering_candidate
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    ∃ r : RecordData P D,
      certificateHasRecord certInput.certificate r ∧
      RecordCoversState P D r (candidateState P n) := by
  have hCover : GlobalCertificateCoversState P D certInput.certificate (candidateState P n) :=
    CertificateTerminalInput.covers_admissible_candidate P D certInput hAdm
  exact hCover

theorem CertificateTerminalInput.has_record_covering_candidateSupport
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (hAdm : CaseCCandidateAdmissible P D n) :
    ∃ r : RecordData P D,
      certificateHasRecord certInput.certificate r ∧
      RecordCoversSupport r (candidateSupport n) := by
  have hCover : GlobalCertificateCoversSupport P D certInput.certificate (candidateSupport n) :=
    globalCertificate_covers_admissible_support
      P D certInput.certificate (candidateSupport n) hAdm
  exact hCover

theorem certificateTerminalInput_excludes_admissible_support
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    False := by
  exact verifiedCertificateRecords_excludes_admissible_support
    P D certInput.soundnessContext certInput.certificate certInput.verifiedRecords S hAdm

theorem certificateTerminalInput_excludes_admissible_state
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    False := by
  exact verifiedCertificateRecords_excludes_admissible_state
    P D certInput.soundnessContext certInput.certificate certInput.verifiedRecords U hAdm

theorem false_of_verified_certificate_for_candidate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (Γ : VerifiedRecordSoundnessContext P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n)
    (hAdm : CaseCCandidateAdmissible P D n) :
    False := by
  exact verifiedCertificateRecords_excludes_admissible_candidate
    P D Γ C hV hL hC hAdm

theorem certificateTerminalInput_excludes_admissible_candidate
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n)
    (hAdm : CaseCCandidateAdmissible P D n) :
    False := by
  exact false_of_verified_certificate_for_candidate
    P D certInput.certificate certInput.verifiedRecords certInput.soundnessContext hL hC hAdm

theorem certificateTerminalInput_excludes_admissible_candidate_expanded
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n)
    (hAdm : CaseCCandidateAdmissible P D n) :
    False := by
  have hCover :
      CandidateCoveredByCertificate P D certInput.certificate n := by
    exact CertificateTerminalInput.covers_admissible_candidate P D certInput hAdm
  exact verifiedCertificateRecords_excludes_covered_candidate
    P D certInput.soundnessContext certInput.certificate certInput.verifiedRecords
    hL hC hAdm hCover

theorem certificateTerminalInput_excludes_admissible_candidate_by_record
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (_hL : LehmerComposite n)
    (_hC : InCaseC n)
    (hAdm : CaseCCandidateAdmissible P D n) :
    False := by
  rcases CertificateTerminalInput.has_record_covering_candidate
      P D certInput hAdm with ⟨r, hr, hCov⟩
  have hRec : VerifiedRecordCertificate P D r :=
    certInput.verifiedRecords r hr
  exact verifiedRecordCertificate_closes_state
    P D certInput.soundnessContext r hRec
    (candidateState P n) hAdm hCov

theorem false_of_certificateTerminalInput
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n)
    (hAdm : CaseCCandidateAdmissible P D n) :
    False := by
  exact certificateTerminalInput_excludes_admissible_candidate
    P D certInput hL hC hAdm

theorem certificateTerminalInput_closes_admissible_caseC
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n)
    (hAdm : CaseCCandidateAdmissible P D n) :
    False := by
  exact false_of_certificateTerminalInput P D certInput hL hC hAdm

def CertificateClosesCaseCCandidates
    (P : Params) (D : ClosureData P)
    (_certInput : CertificateTerminalInput P D) : Prop :=
  ∀ n : ℕ,
    LehmerComposite n →
    InCaseC n →
    CaseCCandidateAdmissible P D n →
    False

@[simp] theorem CertificateClosesCaseCCandidates_def
    (P : Params) (D : ClosureData P)
    (_certInput : CertificateTerminalInput P D) :
    CertificateClosesCaseCCandidates P D _certInput =
      (∀ n : ℕ,
        LehmerComposite n →
        InCaseC n →
        CaseCCandidateAdmissible P D n →
        False) := rfl

theorem certificateTerminalInput_closes_caseC_candidates
    (P : Params) (D : ClosureData P)
    (certInput : CertificateTerminalInput P D) :
    CertificateClosesCaseCCandidates P D certInput := by
  intro n hL hC hAdm
  exact false_of_certificateTerminalInput P D certInput hL hC hAdm

def mkCertificateTerminalInput
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (Γ : VerifiedRecordSoundnessContext P D) :
    CertificateTerminalInput P D :=
  { certificate := C
    verifiedRecords := hV
    soundnessContext := Γ }

@[simp] theorem mkCertificateTerminalInput_certificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (Γ : VerifiedRecordSoundnessContext P D) :
    (mkCertificateTerminalInput P D C hV Γ).certificate = C := rfl

@[simp] theorem mkCertificateTerminalInput_verifiedRecords
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (Γ : VerifiedRecordSoundnessContext P D) :
    (mkCertificateTerminalInput P D C hV Γ).verifiedRecords = hV := rfl

@[simp] theorem mkCertificateTerminalInput_soundnessContext
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (Γ : VerifiedRecordSoundnessContext P D) :
    (mkCertificateTerminalInput P D C hV Γ).soundnessContext = Γ := rfl

end Certificate
end CaseC
end Lehmer