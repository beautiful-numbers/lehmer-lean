-- FILE: Lean/Lehmer/Audit/CaseC/Certificate.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Main : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Audit.CaseC.Params : def thm
- Lehmer.Audit.CaseC.ClosureData : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Main
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Audit.CaseC.Params
import Lehmer.Audit.CaseC.ClosureData

namespace Lehmer
namespace Audit
namespace CaseC

def auditCaseCGlobalCertificate :
    Lehmer.CaseC.Certificate.GlobalCertificate :=
  Lehmer.CaseC.Certificate.GlobalCertificate.mk []

@[simp] theorem auditCaseCGlobalCertificate_records :
    Lehmer.CaseC.Certificate.certificateRecords
      auditCaseCGlobalCertificate = [] := rfl

theorem auditCaseCGlobalCertificate_checked :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      auditCaseCGlobalCertificate := by
  exact Lehmer.CaseC.Certificate.globallyCheckedCertificate_nil

def auditCaseCCheckerGlobalPackage :
    Lehmer.CaseC.Certificate.CheckerGlobalPackage :=
  Lehmer.CaseC.Certificate.CheckerGlobalPackage.mk
    auditCaseCGlobalCertificate
    auditCaseCGlobalCertificate_checked

@[simp] theorem auditCaseCCheckerGlobalPackage_certificate :
    auditCaseCCheckerGlobalPackage.certificate =
      auditCaseCGlobalCertificate := rfl

@[simp] theorem auditCaseCCheckerGlobalPackage_checked :
    auditCaseCCheckerGlobalPackage.checked =
      auditCaseCGlobalCertificate_checked := rfl

def auditCaseCCertificateMainPackage :
    Lehmer.CaseC.Certificate.CertificateMainPackage :=
  Lehmer.CaseC.Certificate.mkCertificateMainPackage
    auditCaseCCheckerGlobalPackage

@[simp] theorem auditCaseCCertificateMainPackage_global :
    auditCaseCCertificateMainPackage.global =
      auditCaseCCheckerGlobalPackage := rfl

@[simp] theorem auditCaseCCertificateMainPackage_certificate :
    auditCaseCCertificateMainPackage.certificate =
      auditCaseCGlobalCertificate := rfl

@[simp] theorem auditCaseCCertificateMainPackage_checked :
    auditCaseCCertificateMainPackage.checked =
      auditCaseCGlobalCertificate_checked := rfl

def auditCaseCCertificateMainPackageOf
    {n : ℕ} (_hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Certificate.CertificateMainPackage :=
  auditCaseCCertificateMainPackage

@[simp] theorem auditCaseCCertificateMainPackageOf_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    auditCaseCCertificateMainPackageOf hC =
      auditCaseCCertificateMainPackage := rfl

@[simp] theorem auditCaseCCertificateMainPackageOf_certificate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCCertificateMainPackageOf hC).certificate =
      auditCaseCGlobalCertificate := rfl

structure AuditCaseCCertificateData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  certificate :
    Lehmer.CaseC.Certificate.CertificateMainPackage

@[simp] theorem AuditCaseCCertificateData.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage) :
    (AuditCaseCCertificateData.mk hC C).inCaseC = hC := rfl

@[simp] theorem AuditCaseCCertificateData.certificate_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage) :
    (AuditCaseCCertificateData.mk hC C).certificate = C := rfl

def auditCaseCCertificateDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCCertificateData n :=
  AuditCaseCCertificateData.mk hC
    (auditCaseCCertificateMainPackageOf hC)

@[simp] theorem auditCaseCCertificateDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCCertificateDataOf hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCCertificateDataOf_certificate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCCertificateDataOf hC).certificate =
      auditCaseCCertificateMainPackageOf hC := rfl

theorem auditCaseCCertificateMainPackage_checked_prop :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      auditCaseCCertificateMainPackage.certificate := by
  exact auditCaseCCertificateMainPackage.checked

theorem auditCaseCCertificateMainPackage_sound :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      auditCaseCCertificateMainPackage.certificate := by
  exact auditCaseCCertificateMainPackage.sound

theorem auditCaseCCertificateMainPackage_complete :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      auditCaseCCertificateMainPackage.certificate := by
  exact auditCaseCCertificateMainPackage.complete

theorem auditCaseCCertificateMainPackage_coverageReady :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      auditCaseCCertificateMainPackage.certificate := by
  exact auditCaseCCertificateMainPackage.coverageReady

theorem auditCaseCCertificateMainPackageOf_checked
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      (auditCaseCCertificateMainPackageOf hC).certificate := by
  exact (auditCaseCCertificateMainPackageOf hC).checked

theorem auditCaseCCertificateMainPackageOf_sound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      (auditCaseCCertificateMainPackageOf hC).certificate := by
  exact (auditCaseCCertificateMainPackageOf hC).sound

theorem auditCaseCCertificateMainPackageOf_complete
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      (auditCaseCCertificateMainPackageOf hC).certificate := by
  exact (auditCaseCCertificateMainPackageOf hC).complete

theorem auditCaseCCertificateMainPackageOf_coverageReady
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      (auditCaseCCertificateMainPackageOf hC).certificate := by
  exact (auditCaseCCertificateMainPackageOf hC).coverageReady

structure CaseCCertificateAuditRouting where
  package :
    Lehmer.CaseC.Certificate.CertificateMainPackage

@[simp] theorem CaseCCertificateAuditRouting.package_mk
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage) :
    (CaseCCertificateAuditRouting.mk C).package = C := rfl

def CaseCCertificateAuditRouting.certificate
    (R : CaseCCertificateAuditRouting) :
    Lehmer.CaseC.Certificate.GlobalCertificate :=
  R.package.certificate

@[simp] theorem CaseCCertificateAuditRouting.certificate_def
    (R : CaseCCertificateAuditRouting) :
    R.certificate = R.package.certificate := rfl

theorem CaseCCertificateAuditRouting.checked
    (R : CaseCCertificateAuditRouting) :
    Lehmer.CaseC.Certificate.CertificateMainChecked R.certificate := by
  simpa [CaseCCertificateAuditRouting.certificate_def] using R.package.checked

theorem CaseCCertificateAuditRouting.sound
    (R : CaseCCertificateAuditRouting) :
    Lehmer.CaseC.Certificate.GloballySoundCertificate R.certificate := by
  simpa [CaseCCertificateAuditRouting.certificate_def] using R.package.sound

theorem CaseCCertificateAuditRouting.complete
    (R : CaseCCertificateAuditRouting) :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate R.certificate := by
  simpa [CaseCCertificateAuditRouting.certificate_def] using R.package.complete

theorem CaseCCertificateAuditRouting.coverageReady
    (R : CaseCCertificateAuditRouting) :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate R.certificate := by
  simpa [CaseCCertificateAuditRouting.certificate_def] using R.package.coverageReady

def caseCCertificateAuditRouting_of_package
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage) :
    CaseCCertificateAuditRouting :=
  CaseCCertificateAuditRouting.mk C

@[simp] theorem caseCCertificateAuditRouting_of_package_package
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage) :
    (caseCCertificateAuditRouting_of_package C).package = C := rfl

def caseCCertificateAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCCertificateAuditRouting :=
  caseCCertificateAuditRouting_of_package
    (auditCaseCCertificateMainPackageOf hC)

@[simp] theorem caseCCertificateAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCCertificateAuditRouting_of_inCaseC hC).package =
      auditCaseCCertificateMainPackageOf hC := rfl

@[simp] theorem caseCCertificateAuditRouting_of_inCaseC_certificate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCCertificateAuditRouting_of_inCaseC hC).certificate =
      auditCaseCGlobalCertificate := rfl

theorem caseCCertificateAuditRouting_sound
    (R : CaseCCertificateAuditRouting) :
    ∃ C : Lehmer.CaseC.Certificate.CertificateMainPackage, True := by
  exact ⟨R.package, trivial⟩

theorem exists_caseCCertificateAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ R : CaseCCertificateAuditRouting, True := by
  exact ⟨caseCCertificateAuditRouting_of_inCaseC hC, trivial⟩

def CaseCCertificateAuditAvailable
    {n : ℕ} (_hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty CaseCCertificateAuditRouting

theorem caseCCertificateAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCCertificateAuditAvailable hC := by
  exact ⟨caseCCertificateAuditRouting_of_inCaseC hC⟩

theorem CaseCCertificateAuditRouting.mem_sound
    (R : CaseCCertificateAuditRouting) :
    ∀ r,
      Lehmer.CaseC.Certificate.certificateHasRecord R.certificate r →
      Lehmer.CaseC.Certificate.LocallySoundRecord r := by
  intro r hr
  simpa [CaseCCertificateAuditRouting.certificate_def] using
    R.package.mem_sound r hr

theorem CaseCCertificateAuditRouting.mem_complete
    (R : CaseCCertificateAuditRouting) :
    ∀ r,
      Lehmer.CaseC.Certificate.certificateHasRecord R.certificate r →
      Lehmer.CaseC.Certificate.LocallyCompleteRecord r := by
  intro r hr
  simpa [CaseCCertificateAuditRouting.certificate_def] using
    R.package.mem_complete r hr

theorem CaseCCertificateAuditRouting.mem_checked
    (R : CaseCCertificateAuditRouting) :
    ∀ r,
      Lehmer.CaseC.Certificate.certificateHasRecord R.certificate r →
      Lehmer.CaseC.Certificate.LocallyCheckedRecord r := by
  intro r hr
  simpa [CaseCCertificateAuditRouting.certificate_def] using
    R.package.mem_checked r hr

end CaseC
end Audit
end Lehmer