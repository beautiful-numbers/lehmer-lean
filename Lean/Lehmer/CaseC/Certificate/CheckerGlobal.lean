-- FILE: Lean/Lehmer/CaseC/Certificate/CheckerGlobal.lean
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

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def GloballyCheckedCertificate (C : GlobalCertificate) : Prop :=
  GloballySoundCertificate C ∧ GloballyCompleteCertificate C

@[simp] theorem GloballyCheckedCertificate_def (C : GlobalCertificate) :
    GloballyCheckedCertificate C =
      (GloballySoundCertificate C ∧ GloballyCompleteCertificate C) := rfl

theorem globallyCheckedCertificate_sound (C : GlobalCertificate) :
    GloballyCheckedCertificate C → GloballySoundCertificate C := by
  intro h
  exact h.1

theorem globallyCheckedCertificate_complete (C : GlobalCertificate) :
    GloballyCheckedCertificate C → GloballyCompleteCertificate C := by
  intro h
  exact h.2

theorem globallyCheckedCertificate_coverageReady (C : GlobalCertificate) :
    GloballyCheckedCertificate C → CoverageReadyCertificate C := by
  intro h
  exact h.2

theorem globallyCheckedCertificate_mem_sound (C : GlobalCertificate) :
    GloballyCheckedCertificate C →
      ∀ r, certificateHasRecord C r → LocallySoundRecord r := by
  intro h r hr
  exact globallySoundCertificate_mem C h.1 r hr

theorem globallyCheckedCertificate_mem_complete (C : GlobalCertificate) :
    GloballyCheckedCertificate C →
      ∀ r, certificateHasRecord C r → LocallyCompleteRecord r := by
  intro h r hr
  exact globallyCompleteCertificate_mem C h.2 r hr

theorem globallyCheckedCertificate_mem (C : GlobalCertificate) :
    GloballyCheckedCertificate C →
      ∀ r, certificateHasRecord C r →
        LocallySoundRecord r ∧ LocallyCompleteRecord r := by
  intro h r hr
  exact ⟨globallyCheckedCertificate_mem_sound C h r hr,
    globallyCheckedCertificate_mem_complete C h r hr⟩

theorem globallyCheckedCertificate_nil :
    GloballyCheckedCertificate (GlobalCertificate.mk []) := by
  constructor
  · exact globallySoundCertificate_nil
  · exact globallyCompleteCertificate_nil

theorem globallyCheckedCertificate_cons (r : RecordData) (rs : RecordFamily) :
    GloballyCheckedCertificate (GlobalCertificate.mk (r :: rs)) ↔
      (LocallySoundRecord r ∧ LocallyCompleteRecord r) ∧
        GloballyCheckedCertificate (GlobalCertificate.mk rs) := by
  constructor
  · intro h
    have hs := (globallySoundCertificate_cons r rs).mp h.1
    have hc := (globallyCompleteCertificate_cons r rs).mp h.2
    constructor
    · exact ⟨hs.1, hc.1⟩
    · exact ⟨hs.2, hc.2⟩
  · intro h
    rcases h with ⟨hhead, htail⟩
    constructor
    · exact (globallySoundCertificate_cons r rs).mpr ⟨hhead.1, htail.1⟩
    · exact (globallyCompleteCertificate_cons r rs).mpr ⟨hhead.2, htail.2⟩

theorem globallyCheckedCertificate_of_sound_complete (C : GlobalCertificate) :
    GloballySoundCertificate C →
    GloballyCompleteCertificate C →
    GloballyCheckedCertificate C := by
  intro hs hc
  exact ⟨hs, hc⟩

theorem globallyCheckedCertificate_exhaustive (C : GlobalCertificate) :
    GloballyCheckedCertificate C ∨ ¬ GloballyCheckedCertificate C := by
  exact Classical.em _

structure CheckerGlobalPackage where
  certificate : GlobalCertificate
  checked : GloballyCheckedCertificate certificate

@[simp] theorem CheckerGlobalPackage.certificate_mk
    (C : GlobalCertificate) (h : GloballyCheckedCertificate C) :
    (CheckerGlobalPackage.mk C h).certificate = C := rfl

@[simp] theorem CheckerGlobalPackage.checked_mk
    (C : GlobalCertificate) (h : GloballyCheckedCertificate C) :
    (CheckerGlobalPackage.mk C h).checked = h := rfl

theorem CheckerGlobalPackage.sound (X : CheckerGlobalPackage) :
    GloballySoundCertificate X.certificate := by
  exact globallyCheckedCertificate_sound X.certificate X.checked

theorem CheckerGlobalPackage.complete (X : CheckerGlobalPackage) :
    GloballyCompleteCertificate X.certificate := by
  exact globallyCheckedCertificate_complete X.certificate X.checked

theorem CheckerGlobalPackage.coverageReady (X : CheckerGlobalPackage) :
    CoverageReadyCertificate X.certificate := by
  exact globallyCheckedCertificate_coverageReady X.certificate X.checked

theorem CheckerGlobalPackage.mem_sound (X : CheckerGlobalPackage) :
    ∀ r, certificateHasRecord X.certificate r → LocallySoundRecord r := by
  intro r hr
  exact globallyCheckedCertificate_mem_sound X.certificate X.checked r hr

theorem CheckerGlobalPackage.mem_complete (X : CheckerGlobalPackage) :
    ∀ r, certificateHasRecord X.certificate r → LocallyCompleteRecord r := by
  intro r hr
  exact globallyCheckedCertificate_mem_complete X.certificate X.checked r hr

theorem CheckerGlobalPackage.mem (X : CheckerGlobalPackage) :
    ∀ r, certificateHasRecord X.certificate r →
      LocallySoundRecord r ∧ LocallyCompleteRecord r := by
  intro r hr
  exact globallyCheckedCertificate_mem X.certificate X.checked r hr

def checkedCertificateRecords (X : CheckerGlobalPackage) : RecordFamily :=
  certificateRecords X.certificate

@[simp] theorem checkedCertificateRecords_def (X : CheckerGlobalPackage) :
    checkedCertificateRecords X = certificateRecords X.certificate := rfl

theorem CheckerGlobalPackage.record_mem_sound (X : CheckerGlobalPackage) :
    ∀ r, r ∈ checkedCertificateRecords X → LocallySoundRecord r := by
  intro r hr
  rw [checkedCertificateRecords_def] at hr
  exact X.mem_sound r hr

theorem CheckerGlobalPackage.record_mem_complete (X : CheckerGlobalPackage) :
    ∀ r, r ∈ checkedCertificateRecords X → LocallyCompleteRecord r := by
  intro r hr
  rw [checkedCertificateRecords_def] at hr
  exact X.mem_complete r hr

theorem CheckerGlobalPackage.record_mem (X : CheckerGlobalPackage) :
    ∀ r, r ∈ checkedCertificateRecords X →
      LocallySoundRecord r ∧ LocallyCompleteRecord r := by
  intro r hr
  rw [checkedCertificateRecords_def] at hr
  exact X.mem r hr

def checkedCertificateHead? (X : CheckerGlobalPackage) : Option RecordData :=
  priorityHead? (checkedCertificateRecords X)

@[simp] theorem checkedCertificateHead?_def (X : CheckerGlobalPackage) :
    checkedCertificateHead? X = priorityHead? (checkedCertificateRecords X) := rfl

theorem checkedCertificateHead?_nil (h : GloballyCheckedCertificate (GlobalCertificate.mk [])) :
    checkedCertificateHead? (CheckerGlobalPackage.mk (GlobalCertificate.mk []) h) = none := by
  rfl

theorem checkedCertificateHead?_cons (r : RecordData) (rs : RecordFamily)
    (h : GloballyCheckedCertificate (GlobalCertificate.mk (r :: rs))) :
    checkedCertificateHead? (CheckerGlobalPackage.mk (GlobalCertificate.mk (r :: rs)) h) = some r := by
  rfl

theorem CheckerGlobalPackage.head_sound (r : RecordData) (rs : RecordFamily)
    (h : GloballyCheckedCertificate (GlobalCertificate.mk (r :: rs))) :
    LocallySoundRecord r := by
  exact (globallyCheckedCertificate_cons r rs).mp h |>.1.1

theorem CheckerGlobalPackage.head_complete (r : RecordData) (rs : RecordFamily)
    (h : GloballyCheckedCertificate (GlobalCertificate.mk (r :: rs))) :
    LocallyCompleteRecord r := by
  exact (globallyCheckedCertificate_cons r rs).mp h |>.1.2

theorem CheckerGlobalPackage.tail_checked (r : RecordData) (rs : RecordFamily)
    (h : GloballyCheckedCertificate (GlobalCertificate.mk (r :: rs))) :
    GloballyCheckedCertificate (GlobalCertificate.mk rs) := by
  exact (globallyCheckedCertificate_cons r rs).mp h |>.2

def mkCheckedCertificate (C : GlobalCertificate)
    (hs : GloballySoundCertificate C)
    (hc : GloballyCompleteCertificate C) : CheckerGlobalPackage :=
  CheckerGlobalPackage.mk C ⟨hs, hc⟩

@[simp] theorem mkCheckedCertificate_certificate (C : GlobalCertificate)
    (hs : GloballySoundCertificate C)
    (hc : GloballyCompleteCertificate C) :
    (mkCheckedCertificate C hs hc).certificate = C := rfl

@[simp] theorem mkCheckedCertificate_checked (C : GlobalCertificate)
    (hs : GloballySoundCertificate C)
    (hc : GloballyCompleteCertificate C) :
    (mkCheckedCertificate C hs hc).checked = ⟨hs, hc⟩ := rfl

end Certificate
end CaseC
end Lehmer