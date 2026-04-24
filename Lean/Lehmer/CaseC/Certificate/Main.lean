-- FILE: Lean/Lehmer/CaseC/Certificate/Main.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Priority : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.SoundnessLocal : def thm
- Lehmer.CaseC.Certificate.CompletenessLocal : def thm
- Lehmer.CaseC.Certificate.SoundnessGlobal : def thm
- Lehmer.CaseC.Certificate.CompletenessGlobal : def thm
- Lehmer.CaseC.Certificate.CheckerLocal : def thm
- Lehmer.CaseC.Certificate.CheckerGlobal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal
import Lehmer.CaseC.Certificate.CompletenessLocal
import Lehmer.CaseC.Certificate.SoundnessGlobal
import Lehmer.CaseC.Certificate.CompletenessGlobal
import Lehmer.CaseC.Certificate.CheckerLocal
import Lehmer.CaseC.Certificate.CheckerGlobal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def CertificateMainChecked (C : GlobalCertificate) : Prop :=
  GloballyCheckedCertificate C

@[simp] theorem CertificateMainChecked_def (C : GlobalCertificate) :
    CertificateMainChecked C = GloballyCheckedCertificate C := rfl

theorem certificateMainChecked_sound (C : GlobalCertificate) :
    CertificateMainChecked C → GloballySoundCertificate C := by
  intro h
  exact globallyCheckedCertificate_sound C h

theorem certificateMainChecked_complete (C : GlobalCertificate) :
    CertificateMainChecked C → GloballyCompleteCertificate C := by
  intro h
  exact globallyCheckedCertificate_complete C h

theorem certificateMainChecked_coverageReady (C : GlobalCertificate) :
    CertificateMainChecked C → CoverageReadyCertificate C := by
  intro h
  exact globallyCheckedCertificate_coverageReady C h

theorem certificateMain_mem_sound (C : GlobalCertificate) :
    CertificateMainChecked C →
      ∀ r, certificateHasRecord C r → LocallySoundRecord r := by
  intro h r hr
  exact globallyCheckedCertificate_mem_sound C h r hr

theorem certificateMain_mem_complete (C : GlobalCertificate) :
    CertificateMainChecked C →
      ∀ r, certificateHasRecord C r → LocallyCompleteRecord r := by
  intro h r hr
  exact globallyCheckedCertificate_mem_complete C h r hr

theorem certificateMain_mem_checked (C : GlobalCertificate) :
    CertificateMainChecked C →
      ∀ r, certificateHasRecord C r → LocallyCheckedRecord r := by
  intro h r hr
  exact ⟨certificateMain_mem_sound C h r hr, certificateMain_mem_complete C h r hr⟩

theorem certificateMain_exhaustive (C : GlobalCertificate) :
    CertificateMainChecked C ∨ ¬ CertificateMainChecked C := by
  exact Classical.em _

structure CertificateMainPackage where
  global : CheckerGlobalPackage

@[simp] theorem CertificateMainPackage.global_mk (G : CheckerGlobalPackage) :
    (CertificateMainPackage.mk G).global = G := rfl

def CertificateMainPackage.certificate (X : CertificateMainPackage) : GlobalCertificate :=
  X.global.certificate

@[simp] theorem CertificateMainPackage.certificate_def (X : CertificateMainPackage) :
    X.certificate = X.global.certificate := rfl

def CertificateMainPackage.checked (X : CertificateMainPackage) : CertificateMainChecked X.certificate :=
  X.global.checked

@[simp] theorem CertificateMainPackage.checked_def (X : CertificateMainPackage) :
    X.checked = X.global.checked := rfl

theorem CertificateMainPackage.sound (X : CertificateMainPackage) :
    GloballySoundCertificate X.certificate := by
  exact X.global.sound

theorem CertificateMainPackage.complete (X : CertificateMainPackage) :
    GloballyCompleteCertificate X.certificate := by
  exact X.global.complete

theorem CertificateMainPackage.coverageReady (X : CertificateMainPackage) :
    CoverageReadyCertificate X.certificate := by
  exact X.global.coverageReady

def CertificateMainPackage.records (X : CertificateMainPackage) : RecordFamily :=
  checkedCertificateRecords X.global

@[simp] theorem CertificateMainPackage.records_def (X : CertificateMainPackage) :
    X.records = checkedCertificateRecords X.global := rfl

theorem CertificateMainPackage.mem_sound (X : CertificateMainPackage) :
    ∀ r, certificateHasRecord X.certificate r → LocallySoundRecord r := by
  intro r hr
  exact X.global.mem_sound r hr

theorem CertificateMainPackage.mem_complete (X : CertificateMainPackage) :
    ∀ r, certificateHasRecord X.certificate r → LocallyCompleteRecord r := by
  intro r hr
  exact X.global.mem_complete r hr

theorem CertificateMainPackage.mem_checked (X : CertificateMainPackage) :
    ∀ r, certificateHasRecord X.certificate r → LocallyCheckedRecord r := by
  intro r hr
  exact ⟨X.mem_sound r hr, X.mem_complete r hr⟩

theorem CertificateMainPackage.record_mem_sound (X : CertificateMainPackage) :
    ∀ r, r ∈ X.records → LocallySoundRecord r := by
  intro r hr
  rw [CertificateMainPackage.records_def] at hr
  exact X.global.record_mem_sound r hr

theorem CertificateMainPackage.record_mem_complete (X : CertificateMainPackage) :
    ∀ r, r ∈ X.records → LocallyCompleteRecord r := by
  intro r hr
  rw [CertificateMainPackage.records_def] at hr
  exact X.global.record_mem_complete r hr

theorem CertificateMainPackage.record_mem_checked (X : CertificateMainPackage) :
    ∀ r, r ∈ X.records → LocallyCheckedRecord r := by
  intro r hr
  exact ⟨X.record_mem_sound r hr, X.record_mem_complete r hr⟩

def CertificateMainPackage.head? (X : CertificateMainPackage) : Option RecordData :=
  checkedCertificateHead? X.global

@[simp] theorem CertificateMainPackage.head?_def (X : CertificateMainPackage) :
    X.head? = checkedCertificateHead? X.global := rfl

theorem CertificateMainPackage.head?_nil
    (h : CertificateMainChecked (GlobalCertificate.mk [])) :
    (CertificateMainPackage.mk (CheckerGlobalPackage.mk (GlobalCertificate.mk []) h)).head? = none := by
  rfl

theorem CertificateMainPackage.head?_cons (r : RecordData) (rs : RecordFamily)
    (h : CertificateMainChecked (GlobalCertificate.mk (r :: rs))) :
    (CertificateMainPackage.mk (CheckerGlobalPackage.mk (GlobalCertificate.mk (r :: rs)) h)).head? = some r := by
  rfl

theorem CertificateMainPackage.head_sound (r : RecordData) (rs : RecordFamily)
    (h : CertificateMainChecked (GlobalCertificate.mk (r :: rs))) :
    LocallySoundRecord r := by
  exact CheckerGlobalPackage.head_sound r rs h

theorem CertificateMainPackage.head_complete (r : RecordData) (rs : RecordFamily)
    (h : CertificateMainChecked (GlobalCertificate.mk (r :: rs))) :
    LocallyCompleteRecord r := by
  exact CheckerGlobalPackage.head_complete r rs h

def CertificateMainPackage.headCheckedPackage (r : RecordData) (rs : RecordFamily)
    (h : CertificateMainChecked (GlobalCertificate.mk (r :: rs))) : CheckerLocalPackage :=
  mkLocallyCheckedRecord r
    (CertificateMainPackage.head_sound r rs h)
    (CertificateMainPackage.head_complete r rs h)

@[simp] theorem CertificateMainPackage.headCheckedPackage_record (r : RecordData) (rs : RecordFamily)
    (h : CertificateMainChecked (GlobalCertificate.mk (r :: rs))) :
    (CertificateMainPackage.headCheckedPackage r rs h).record = r := by
  rfl

theorem CertificateMainPackage.headCheckedPackage_checked (r : RecordData) (rs : RecordFamily)
    (h : CertificateMainChecked (GlobalCertificate.mk (r :: rs))) :
    LocallyCheckedRecord (CertificateMainPackage.headCheckedPackage r rs h).record := by
  exact (CertificateMainPackage.headCheckedPackage r rs h).checked

def mkCertificateMainPackage (G : CheckerGlobalPackage) : CertificateMainPackage :=
  CertificateMainPackage.mk G

@[simp] theorem mkCertificateMainPackage_global (G : CheckerGlobalPackage) :
    (mkCertificateMainPackage G).global = G := rfl

@[simp] theorem mkCertificateMainPackage_certificate (G : CheckerGlobalPackage) :
    (mkCertificateMainPackage G).certificate = G.certificate := rfl

@[simp] theorem mkCertificateMainPackage_checked (G : CheckerGlobalPackage) :
    (mkCertificateMainPackage G).checked = G.checked := rfl

end Certificate
end CaseC
end Lehmer