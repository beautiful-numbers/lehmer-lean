-- FILE: Lean/Lehmer/Audit/CaseCReconstruction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.BranchData : def thm
- Lehmer.Audit.CaseC.Params : def thm
- Lehmer.Audit.CaseC.ClosureData : def thm
- Lehmer.Audit.CaseC.NonIntegrality : def thm
- Lehmer.Audit.CaseC.KmaxGap : def thm
- Lehmer.Audit.CaseC.GapClosure : def thm
- Lehmer.Audit.CaseC.ResidualClosure : def thm
- Lehmer.Audit.CaseC.Certificate : def thm
- Lehmer.Audit.CaseC.Exhaustivity : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.BranchData
import Lehmer.Audit.CaseC.Params
import Lehmer.Audit.CaseC.ClosureData
import Lehmer.Audit.CaseC.NonIntegrality
import Lehmer.Audit.CaseC.KmaxGap
import Lehmer.Audit.CaseC.GapClosure
import Lehmer.Audit.CaseC.ResidualClosure
import Lehmer.Audit.CaseC.Certificate
import Lehmer.Audit.CaseC.Exhaustivity

namespace Lehmer
namespace CaseC

def caseCParamsOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Params :=
  Lehmer.Audit.CaseC.auditCaseCParamsOf hC

@[simp] theorem caseCParamsOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCParamsOf hC =
      Lehmer.Audit.CaseC.auditCaseCParamsOf hC := rfl

def caseCClosureDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.ClosureData (caseCParamsOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCClosureDataOf hC

@[simp] theorem caseCClosureDataOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCClosureDataOf hC =
      Lehmer.Audit.CaseC.auditCaseCClosureDataOf hC := rfl

def caseCNonIntegralityOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCNonIntegralityOf hC

@[simp] theorem caseCNonIntegralityOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCNonIntegralityOf hC =
      Lehmer.Audit.CaseC.auditCaseCNonIntegralityOf hC := rfl

def caseCKmaxGapOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.KmaxGapPackage
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCKmaxGapOf hC

@[simp] theorem caseCKmaxGapOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCKmaxGapOf hC =
      Lehmer.Audit.CaseC.auditCaseCKmaxGapOf hC := rfl

def caseCGapToClosureOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.GapToClosurePackage
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCGapToClosureOf hC

@[simp] theorem caseCGapToClosureOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCGapToClosureOf hC =
      Lehmer.Audit.CaseC.auditCaseCGapToClosureOf hC := rfl

def caseCGapClosureOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.GapClosurePackage
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  (caseCGapToClosureOf hC).gap

@[simp] theorem caseCGapClosureOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCGapClosureOf hC = (caseCGapToClosureOf hC).gap := rfl

def caseCResidualStateOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualState
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCResidualStateOf hC

@[simp] theorem caseCResidualStateOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCResidualStateOf hC =
      Lehmer.Audit.CaseC.auditCaseCResidualStateOf hC := rfl

def caseCResidualClosureOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCResidualClosureOfInCaseC hC

@[simp] theorem caseCResidualClosureOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCResidualClosureOf hC =
      Lehmer.Audit.CaseC.auditCaseCResidualClosureOfInCaseC hC := rfl

def caseCCertificateMainPackageOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Certificate.CertificateMainPackage :=
  Lehmer.Audit.CaseC.auditCaseCCertificateMainPackageOf hC

@[simp] theorem caseCCertificateMainPackageOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCCertificateMainPackageOf hC =
      Lehmer.Audit.CaseC.auditCaseCCertificateMainPackageOf hC := rfl

end CaseC
end Lehmer

namespace Lehmer
namespace Audit

structure AuditCaseCReconstructionPieces (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  paramsData :
    Lehmer.Audit.CaseC.AuditCaseCParamsData n
  closureData :
    Lehmer.Audit.CaseC.AuditCaseCClosureData n
  nonIntegralityData :
    Lehmer.Audit.CaseC.AuditCaseCNonIntegralityData n
  kmaxGapData :
    Lehmer.Audit.CaseC.AuditCaseCKmaxGapData n
  gapClosureMarker :
    Lehmer.Audit.CaseC.AuditCaseCGapClosureUnavailable
  gapToClosure :
    Lehmer.CaseC.GapClosure.GapToClosurePackage
      (Lehmer.Audit.CaseC.auditCaseCParamsOf inCaseC)
      (Lehmer.Audit.CaseC.auditCaseCClosureDataOf inCaseC)
  residual :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (Lehmer.Audit.CaseC.auditCaseCParamsOf inCaseC)
      (Lehmer.Audit.CaseC.auditCaseCClosureDataOf inCaseC)
  certificate :
    Lehmer.CaseC.Certificate.CertificateMainPackage
  exhaustivityData :
    Lehmer.Audit.CaseC.CaseCExhaustivityData n

def auditCaseCReconstructionPiecesOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCReconstructionPieces n :=
  AuditCaseCReconstructionPieces.mk
    hC
    (Lehmer.Audit.CaseC.auditCaseCParamsDataOf hC)
    (Lehmer.Audit.CaseC.auditCaseCClosureDataDataOf hC)
    (Lehmer.Audit.CaseC.auditCaseCNonIntegralityDataOf hC)
    (Lehmer.Audit.CaseC.auditCaseCKmaxGapDataOf hC)
    Lehmer.Audit.CaseC.auditCaseCGapClosureUnavailable
    (Lehmer.Audit.CaseC.auditCaseCGapToClosureOf hC)
    (Lehmer.Audit.CaseC.auditCaseCResidualClosureOfInCaseC hC)
    (Lehmer.Audit.CaseC.auditCaseCCertificateMainPackageOf hC)
    (Lehmer.Audit.CaseC.caseCExhaustivityDataOf hC)

@[simp] theorem auditCaseCReconstructionPiecesOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_paramsData
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).paramsData =
      Lehmer.Audit.CaseC.auditCaseCParamsDataOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_closureData
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).closureData =
      Lehmer.Audit.CaseC.auditCaseCClosureDataDataOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_nonIntegralityData
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).nonIntegralityData =
      Lehmer.Audit.CaseC.auditCaseCNonIntegralityDataOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_kmaxGapData
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).kmaxGapData =
      Lehmer.Audit.CaseC.auditCaseCKmaxGapDataOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_gapClosureMarker
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).gapClosureMarker =
      Lehmer.Audit.CaseC.auditCaseCGapClosureUnavailable := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_gapToClosure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).gapToClosure =
      Lehmer.Audit.CaseC.auditCaseCGapToClosureOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_residual
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).residual =
      Lehmer.Audit.CaseC.auditCaseCResidualClosureOfInCaseC hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_certificate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).certificate =
      Lehmer.Audit.CaseC.auditCaseCCertificateMainPackageOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_exhaustivityData
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).exhaustivityData =
      Lehmer.Audit.CaseC.caseCExhaustivityDataOf hC := rfl

theorem AuditCaseCReconstructionPieces.in_caseC
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.Pipeline.InCaseC n := by
  exact X.inCaseC

def AuditCaseCReconstructionPieces.params
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.Params :=
  X.paramsData.params

@[simp] theorem AuditCaseCReconstructionPieces.params_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.params = X.paramsData.params := rfl

def AuditCaseCReconstructionPieces.closureDataPackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.Audit.CaseC.AuditCaseCClosureData n :=
  X.closureData

@[simp] theorem AuditCaseCReconstructionPieces.closureDataPackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.closureDataPackage = X.closureData := rfl

def AuditCaseCReconstructionPieces.nonIntegralityPackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      X.nonIntegralityData.params
      X.nonIntegralityData.closure :=
  X.nonIntegralityData.nonIntegrality

@[simp] theorem AuditCaseCReconstructionPieces.nonIntegralityPackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.nonIntegralityPackage = X.nonIntegralityData.nonIntegrality := rfl

def AuditCaseCReconstructionPieces.kmaxGapPackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.GapClosure.KmaxGapPackage
      X.kmaxGapData.params
      X.kmaxGapData.closure :=
  X.kmaxGapData.kmaxGap

@[simp] theorem AuditCaseCReconstructionPieces.kmaxGapPackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.kmaxGapPackage = X.kmaxGapData.kmaxGap := rfl

def AuditCaseCReconstructionPieces.gapToClosurePackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.GapClosure.GapToClosurePackage
      (Lehmer.Audit.CaseC.auditCaseCParamsOf X.inCaseC)
      (Lehmer.Audit.CaseC.auditCaseCClosureDataOf X.inCaseC) :=
  X.gapToClosure

@[simp] theorem AuditCaseCReconstructionPieces.gapToClosurePackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.gapToClosurePackage = X.gapToClosure := rfl

def AuditCaseCReconstructionPieces.gapClosurePackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.GapClosure.GapClosurePackage
      (Lehmer.Audit.CaseC.auditCaseCParamsOf X.inCaseC)
      (Lehmer.Audit.CaseC.auditCaseCClosureDataOf X.inCaseC) :=
  X.gapToClosure.gap

@[simp] theorem AuditCaseCReconstructionPieces.gapClosurePackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.gapClosurePackage = X.gapToClosure.gap := rfl

def AuditCaseCReconstructionPieces.residualPackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (Lehmer.Audit.CaseC.auditCaseCParamsOf X.inCaseC)
      (Lehmer.Audit.CaseC.auditCaseCClosureDataOf X.inCaseC) :=
  X.residual

@[simp] theorem AuditCaseCReconstructionPieces.residualPackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.residualPackage = X.residual := rfl

def AuditCaseCReconstructionPieces.certificatePackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.Certificate.CertificateMainPackage :=
  X.certificate

@[simp] theorem AuditCaseCReconstructionPieces.certificatePackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.certificatePackage = X.certificate := rfl

def AuditCaseCReconstructionPieces.exhaustivityPackage
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.Audit.CaseC.CaseCExhaustivityData n :=
  X.exhaustivityData

@[simp] theorem AuditCaseCReconstructionPieces.exhaustivityPackage_def
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.exhaustivityPackage = X.exhaustivityData := rfl

def CaseCReconstructionTotal : Prop :=
  ∀ n : ℕ,
    Lehmer.Pipeline.InCaseC n →
      ∃ X : AuditCaseCReconstructionPieces n, True

@[simp] theorem CaseCReconstructionTotal_def :
    CaseCReconstructionTotal =
      (∀ n : ℕ,
        Lehmer.Pipeline.InCaseC n →
          ∃ X : AuditCaseCReconstructionPieces n, True) := rfl

theorem caseC_reconstruction_total :
    CaseCReconstructionTotal := by
  intro n hC
  exact ⟨auditCaseCReconstructionPiecesOf hC, trivial⟩

theorem exists_caseCReconstructionPieces_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ X : AuditCaseCReconstructionPieces n, True := by
  exact ⟨auditCaseCReconstructionPiecesOf hC, trivial⟩

theorem auditCaseCReconstructionPiecesOf_level
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).closureData.level =
      Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCReconstructionPiecesOf_width
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).closureData.width =
      Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCReconstructionPiecesOf_cap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).closureData.cap =
      Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCReconstructionPiecesOf_omegaBound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).closureData.omegaBound =
      Lehmer.Pipeline.pivotOf n := by
  rfl

theorem AuditCaseCReconstructionPieces.level_ge_YA
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.Pipeline.YA ≤ X.closureData.level := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.level_ge_YA X.closureData

theorem AuditCaseCReconstructionPieces.width_ge_YA
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.Pipeline.YA ≤ X.closureData.width := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.width_ge_YA X.closureData

theorem AuditCaseCReconstructionPieces.cap_ge_YA
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.Pipeline.YA ≤ X.closureData.cap := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.cap_ge_YA X.closureData

theorem AuditCaseCReconstructionPieces.omegaBound_ge_YA
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.Pipeline.YA ≤ X.closureData.omegaBound := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.omegaBound_ge_YA X.closureData

theorem AuditCaseCReconstructionPieces.level_lt_YC
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.closureData.level < Lehmer.Pipeline.YC := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.level_lt_YC X.closureData

theorem AuditCaseCReconstructionPieces.width_lt_YC
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.closureData.width < Lehmer.Pipeline.YC := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.width_lt_YC X.closureData

theorem AuditCaseCReconstructionPieces.cap_lt_YC
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.closureData.cap < Lehmer.Pipeline.YC := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.cap_lt_YC X.closureData

theorem AuditCaseCReconstructionPieces.omegaBound_lt_YC
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    X.closureData.omegaBound < Lehmer.Pipeline.YC := by
  exact Lehmer.Audit.CaseC.AuditCaseCClosureData.omegaBound_lt_YC X.closureData

theorem AuditCaseCReconstructionPieces.gapToClosure_available
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Nonempty
      (Lehmer.CaseC.GapClosure.GapToClosurePackage
        (Lehmer.Audit.CaseC.auditCaseCParamsOf X.inCaseC)
        (Lehmer.Audit.CaseC.auditCaseCClosureDataOf X.inCaseC)) := by
  exact ⟨X.gapToClosure⟩

theorem AuditCaseCReconstructionPieces.residual_closed
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (Lehmer.Audit.CaseC.auditCaseCParamsOf X.inCaseC)
      (Lehmer.Audit.CaseC.auditCaseCClosureDataOf X.inCaseC)
      X.residual.state := by
  exact X.residual.closed

theorem AuditCaseCReconstructionPieces.certificate_checked
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      X.certificate.certificate := by
  exact X.certificate.checked

theorem AuditCaseCReconstructionPieces.certificate_sound
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      X.certificate.certificate := by
  exact X.certificate.sound

theorem AuditCaseCReconstructionPieces.certificate_complete
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      X.certificate.certificate := by
  exact X.certificate.complete

theorem AuditCaseCReconstructionPieces.certificate_coverageReady
    {n : ℕ} (X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      X.certificate.certificate := by
  exact X.certificate.coverageReady

theorem exists_caseCReconstructionPieces_strong
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ X : AuditCaseCReconstructionPieces n,
      X.inCaseC = hC ∧
      X.closureData.level = Lehmer.Pipeline.pivotOf n ∧
      X.closureData.width = Lehmer.Pipeline.pivotOf n ∧
      X.closureData.cap = Lehmer.Pipeline.pivotOf n ∧
      X.closureData.omegaBound = Lehmer.Pipeline.pivotOf n ∧
      Lehmer.CaseC.StateMachine.ResidualClosed
        (Lehmer.Audit.CaseC.auditCaseCParamsOf X.inCaseC)
        (Lehmer.Audit.CaseC.auditCaseCClosureDataOf X.inCaseC)
        X.residual.state ∧
      Lehmer.CaseC.Certificate.CertificateMainChecked
        X.certificate.certificate := by
  refine ⟨auditCaseCReconstructionPiecesOf hC, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact AuditCaseCReconstructionPieces.residual_closed
      (auditCaseCReconstructionPiecesOf hC)
  · exact AuditCaseCReconstructionPieces.certificate_checked
      (auditCaseCReconstructionPiecesOf hC)

end Audit
end Lehmer