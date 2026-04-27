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

def auditCaseCCertificateMainPackage
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.GlobalCertificate P D)
    (hV : Lehmer.CaseC.Certificate.VerifiedCertificateRecords P D C) :
    Lehmer.CaseC.Certificate.CertificateMainPackage P D :=
  Lehmer.CaseC.Certificate.mkCertificateMainPackage P D C hV

@[simp] theorem auditCaseCCertificateMainPackage_certificate
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.GlobalCertificate P D)
    (hV : Lehmer.CaseC.Certificate.VerifiedCertificateRecords P D C) :
    (auditCaseCCertificateMainPackage P D C hV).certificate = C := by
  rfl

@[simp] theorem auditCaseCCertificateMainPackage_verifiedRecords
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.GlobalCertificate P D)
    (hV : Lehmer.CaseC.Certificate.VerifiedCertificateRecords P D C) :
    (auditCaseCCertificateMainPackage P D C hV).verifiedRecords = hV := by
  rfl

@[simp] theorem auditCaseCCertificateMainPackage_checked
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.GlobalCertificate P D)
    (hV : Lehmer.CaseC.Certificate.VerifiedCertificateRecords P D C) :
    (auditCaseCCertificateMainPackage P D C hV).checked P D = hV := by
  rfl

@[simp] theorem auditCaseCCertificateMainPackage_verified
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.GlobalCertificate P D)
    (hV : Lehmer.CaseC.Certificate.VerifiedCertificateRecords P D C) :
    (auditCaseCCertificateMainPackage P D C hV).verified P D = hV := by
  rfl

@[simp] theorem auditCaseCCertificateMainPackage_records
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.GlobalCertificate P D)
    (hV : Lehmer.CaseC.Certificate.VerifiedCertificateRecords P D C) :
    (auditCaseCCertificateMainPackage P D C hV).records P D =
      Lehmer.CaseC.Certificate.certificateRecords C := by
  rfl

def auditCaseCGlobalCertificateOfPackage
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    Lehmer.CaseC.Certificate.GlobalCertificate P D :=
  X.certificate

@[simp] theorem auditCaseCGlobalCertificateOfPackage_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    auditCaseCGlobalCertificateOfPackage P D X = X.certificate := rfl

@[simp] theorem auditCaseCGlobalCertificateOfPackage_records
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    Lehmer.CaseC.Certificate.certificateRecords
      (auditCaseCGlobalCertificateOfPackage P D X) =
      X.records P D := by
  rfl

noncomputable def auditCaseCGlobalCertificateCheckedOfPackage
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      P D (auditCaseCGlobalCertificateOfPackage P D X) := by
  rw [auditCaseCGlobalCertificateOfPackage_def]
  exact X.checked P D

@[simp] theorem auditCaseCGlobalCertificateCheckedOfPackage_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    auditCaseCGlobalCertificateCheckedOfPackage P D X =
      X.checked P D := rfl

noncomputable def auditCaseCGlobalCertificateVerifiedOfPackage
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    Lehmer.CaseC.Certificate.VerifiedCertificateRecords
      P D (auditCaseCGlobalCertificateOfPackage P D X) := by
  rw [auditCaseCGlobalCertificateOfPackage_def]
  exact X.verified P D

@[simp] theorem auditCaseCGlobalCertificateVerifiedOfPackage_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    auditCaseCGlobalCertificateVerifiedOfPackage P D X =
      X.verified P D := rfl

noncomputable def auditCaseCCertificateMainPackageOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    Lehmer.CaseC.Certificate.CertificateMainPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  X

@[simp] theorem auditCaseCCertificateMainPackageOf_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    auditCaseCCertificateMainPackageOf hC X = X := rfl

@[simp] theorem auditCaseCCertificateMainPackageOf_certificate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateMainPackageOf hC X).certificate = X.certificate := rfl

@[simp] theorem auditCaseCCertificateMainPackageOf_verifiedRecords
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateMainPackageOf hC X).verifiedRecords = X.verifiedRecords := rfl

@[simp] theorem auditCaseCCertificateMainPackageOf_checked
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateMainPackageOf hC X).checked
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) =
      X.checked
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) := rfl

@[simp] theorem auditCaseCCertificateMainPackageOf_records
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateMainPackageOf hC X).records
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) =
      X.records
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) := rfl

structure AuditCaseCCertificateData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  params : Lehmer.CaseC.Params
  closure : Lehmer.CaseC.ClosureData params
  certificate :
    Lehmer.CaseC.Certificate.CertificateMainPackage params closure

@[simp] theorem AuditCaseCCertificateData.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (AuditCaseCCertificateData.mk hC P D C).inCaseC = hC := rfl

@[simp] theorem AuditCaseCCertificateData.params_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (AuditCaseCCertificateData.mk hC P D C).params = P := rfl

@[simp] theorem AuditCaseCCertificateData.closure_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (AuditCaseCCertificateData.mk hC P D C).closure = D := rfl

@[simp] theorem AuditCaseCCertificateData.certificate_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (AuditCaseCCertificateData.mk hC P D C).certificate = C := rfl

noncomputable def auditCaseCCertificateDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    AuditCaseCCertificateData n :=
  AuditCaseCCertificateData.mk hC
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X

@[simp] theorem auditCaseCCertificateDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateDataOf hC X).inCaseC = hC := rfl

@[simp] theorem auditCaseCCertificateDataOf_params
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateDataOf hC X).params = auditCaseCParamsOf hC := rfl

@[simp] theorem auditCaseCCertificateDataOf_closure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateDataOf hC X).closure = auditCaseCClosureDataOf hC := rfl

@[simp] theorem auditCaseCCertificateDataOf_certificate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (auditCaseCCertificateDataOf hC X).certificate = X := rfl

structure CaseCCertificateAuditRouting
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  package :
    Lehmer.CaseC.Certificate.CertificateMainPackage P D

@[simp] theorem CaseCCertificateAuditRouting.package_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (CaseCCertificateAuditRouting.mk C).package = C := rfl

def CaseCCertificateAuditRouting.certificate
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    Lehmer.CaseC.Certificate.GlobalCertificate P D :=
  R.package.certificate

@[simp] theorem CaseCCertificateAuditRouting.certificate_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    R.certificate P D = R.package.certificate := rfl

def CaseCCertificateAuditRouting.records
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    Lehmer.CaseC.Certificate.RecordFamily P D :=
  R.package.records P D

@[simp] theorem CaseCCertificateAuditRouting.records_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    R.records P D =
      Lehmer.CaseC.Certificate.certificateRecords (R.certificate P D) := by
  rfl

def CaseCCertificateAuditRouting.head?
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    Option (Lehmer.CaseC.Certificate.RecordData P D) :=
  R.package.head? P D

@[simp] theorem CaseCCertificateAuditRouting.head?_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    R.head? P D = R.package.head? P D := rfl

noncomputable def CaseCCertificateAuditRouting.checked
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      P D (R.certificate P D) := by
  rw [CaseCCertificateAuditRouting.certificate_def]
  exact R.package.checked P D

noncomputable def CaseCCertificateAuditRouting.verified
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    Lehmer.CaseC.Certificate.VerifiedCertificateRecords
      P D (R.certificate P D) := by
  rw [CaseCCertificateAuditRouting.certificate_def]
  exact R.package.verified P D

noncomputable def CaseCCertificateAuditRouting.mem_verified
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    ∀ r : Lehmer.CaseC.Certificate.RecordData P D,
      Lehmer.CaseC.Certificate.certificateHasRecord (R.certificate P D) r →
        Lehmer.CaseC.Certificate.VerifiedRecordCertificate P D r :=
  fun r hr => by
    rw [CaseCCertificateAuditRouting.certificate_def] at hr
    exact R.package.mem_verified P D r hr

def caseCCertificateAuditRouting_of_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    CaseCCertificateAuditRouting P D :=
  CaseCCertificateAuditRouting.mk C

@[simp] theorem caseCCertificateAuditRouting_of_package_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (caseCCertificateAuditRouting_of_package P D C).package = C := rfl

@[simp] theorem caseCCertificateAuditRouting_of_package_certificate
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (caseCCertificateAuditRouting_of_package P D C).certificate P D =
      C.certificate := rfl

@[simp] theorem caseCCertificateAuditRouting_of_package_records
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (C : Lehmer.CaseC.Certificate.CertificateMainPackage P D) :
    (caseCCertificateAuditRouting_of_package P D C).records P D =
      C.records P D := rfl

noncomputable def caseCCertificateAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    CaseCCertificateAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  caseCCertificateAuditRouting_of_package
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X

@[simp] theorem caseCCertificateAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (caseCCertificateAuditRouting_of_inCaseC hC X).package = X := rfl

@[simp] theorem caseCCertificateAuditRouting_of_inCaseC_certificate
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (caseCCertificateAuditRouting_of_inCaseC hC X).certificate
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) =
      X.certificate := rfl

@[simp] theorem caseCCertificateAuditRouting_of_inCaseC_records
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    (caseCCertificateAuditRouting_of_inCaseC hC X).records
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) =
      X.records
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) := rfl

theorem caseCCertificateAuditRouting_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    ∃ _C : Lehmer.CaseC.Certificate.CertificateMainPackage P D, True := by
  exact ⟨R.package, trivial⟩

theorem exists_caseCCertificateAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    ∃ _R : CaseCCertificateAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC), True := by
  exact ⟨caseCCertificateAuditRouting_of_inCaseC hC X, trivial⟩

def CaseCCertificateAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty
    (CaseCCertificateAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

@[simp] theorem CaseCCertificateAuditAvailable_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCCertificateAuditAvailable hC =
      Nonempty
        (CaseCCertificateAuditRouting
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC)) := rfl

theorem caseCCertificateAuditAvailable_of_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X :
      Lehmer.CaseC.Certificate.CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    CaseCCertificateAuditAvailable hC := by
  exact ⟨caseCCertificateAuditRouting_of_inCaseC hC X⟩

end CaseC
end Audit
end Lehmer