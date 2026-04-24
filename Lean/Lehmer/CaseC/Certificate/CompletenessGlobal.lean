-- FILE: Lean/Lehmer/CaseC/Certificate/CompletenessGlobal.lean
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

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def GloballyCompleteRecordFamily (R : RecordFamily) : Prop :=
  ∀ r : RecordData, r ∈ R → LocallyCompleteRecord r

@[simp] theorem GloballyCompleteRecordFamily_def (R : RecordFamily) :
    GloballyCompleteRecordFamily R =
      (∀ r : RecordData, r ∈ R → LocallyCompleteRecord r) := rfl

def GloballyCompleteCertificate (C : GlobalCertificate) : Prop :=
  GloballyCompleteRecordFamily (certificateRecords C)

@[simp] theorem GloballyCompleteCertificate_def (C : GlobalCertificate) :
    GloballyCompleteCertificate C =
      GloballyCompleteRecordFamily (certificateRecords C) := rfl

theorem globallyCompleteFamily_nil :
    GloballyCompleteRecordFamily [] := by
  intro r hr
  simp at hr

theorem globallyCompleteFamily_cons (r : RecordData) (rs : RecordFamily) :
    GloballyCompleteRecordFamily (r :: rs) ↔
      LocallyCompleteRecord r ∧ GloballyCompleteRecordFamily rs := by
  constructor
  · intro h
    constructor
    · exact h r (by simp)
    · intro s hs
      exact h s (by simp [hs])
  · intro h
    rcases h with ⟨hr, hrs⟩
    intro s hs
    simp at hs
    rcases hs with rfl | hs'
    · exact hr
    · exact hrs s hs'

theorem globallyCompleteCertificate_iff_family (C : GlobalCertificate) :
    GloballyCompleteCertificate C ↔
      GloballyCompleteRecordFamily (certificateRecords C) := by
  rfl

theorem globallyCompleteCertificate_nil :
    GloballyCompleteCertificate (GlobalCertificate.mk []) := by
  exact globallyCompleteFamily_nil

theorem globallyCompleteCertificate_cons (r : RecordData) (rs : RecordFamily) :
    GloballyCompleteCertificate (GlobalCertificate.mk (r :: rs)) ↔
      LocallyCompleteRecord r ∧
      GloballyCompleteCertificate (GlobalCertificate.mk rs) := by
  constructor
  · intro h
    constructor
    · exact h r (by simp [certificateRecords])
    · intro s hs
      exact h s (by
        simp [certificateRecords] at hs ⊢
        exact Or.inr hs)
  · intro h
    rcases h with ⟨hr, hrs⟩
    intro s hs
    simp [certificateRecords] at hs
    rcases hs with rfl | hs'
    · exact hr
    · exact hrs s hs'

theorem globallyCompleteFamily_mem (R : RecordFamily) :
    GloballyCompleteRecordFamily R →
      ∀ r, r ∈ R → LocallyCompleteRecord r := by
  intro h r hr
  exact h r hr

theorem globallyCompleteCertificate_mem (C : GlobalCertificate) :
    GloballyCompleteCertificate C →
      ∀ r, certificateHasRecord C r → LocallyCompleteRecord r := by
  intro hC r hr
  exact hC r hr

theorem globallyCompleteFamily_of_pointwise (R : RecordFamily) :
    (∀ r, r ∈ R → LocallyCompleteRecord r) →
      GloballyCompleteRecordFamily R := by
  intro h
  exact h

theorem globallyCompleteCertificate_of_pointwise (C : GlobalCertificate) :
    (∀ r, certificateHasRecord C r → LocallyCompleteRecord r) →
      GloballyCompleteCertificate C := by
  intro h r hr
  exact h r hr

theorem globallyCompleteFamily_head (r : RecordData) (rs : RecordFamily) :
    GloballyCompleteRecordFamily (r :: rs) → LocallyCompleteRecord r := by
  intro h
  exact (globallyCompleteFamily_cons r rs).mp h |>.1

theorem globallyCompleteFamily_tail (r : RecordData) (rs : RecordFamily) :
    GloballyCompleteRecordFamily (r :: rs) → GloballyCompleteRecordFamily rs := by
  intro h
  exact (globallyCompleteFamily_cons r rs).mp h |>.2

theorem globallyCompleteCertificate_head (r : RecordData) (rs : RecordFamily) :
    GloballyCompleteCertificate (GlobalCertificate.mk (r :: rs)) →
      LocallyCompleteRecord r := by
  intro h
  exact (globallyCompleteCertificate_cons r rs).mp h |>.1

theorem globallyCompleteCertificate_tail (r : RecordData) (rs : RecordFamily) :
    GloballyCompleteCertificate (GlobalCertificate.mk (r :: rs)) →
      GloballyCompleteCertificate (GlobalCertificate.mk rs) := by
  intro h
  exact (globallyCompleteCertificate_cons r rs).mp h |>.2

theorem globallyCompleteFamily_cons_intro (r : RecordData) (rs : RecordFamily) :
    LocallyCompleteRecord r →
    GloballyCompleteRecordFamily rs →
    GloballyCompleteRecordFamily (r :: rs) := by
  intro hr hrs
  exact (globallyCompleteFamily_cons r rs).mpr ⟨hr, hrs⟩

theorem globallyCompleteCertificate_cons_intro (r : RecordData) (rs : RecordFamily) :
    LocallyCompleteRecord r →
    GloballyCompleteCertificate (GlobalCertificate.mk rs) →
    GloballyCompleteCertificate (GlobalCertificate.mk (r :: rs)) := by
  intro hr h
  exact (globallyCompleteCertificate_cons r rs).mpr ⟨hr, h⟩

theorem globallyComplete_implies_globallySoundFamily (R : RecordFamily) :
    GloballyCompleteRecordFamily R → GloballySoundRecordFamily R := by
  intro h r hr
  exact locallyComplete_implies_locallySound r (h r hr)

theorem globallyComplete_implies_globallySoundCertificate (C : GlobalCertificate) :
    GloballyCompleteCertificate C → GloballySoundCertificate C := by
  intro h
  exact globallyComplete_implies_globallySoundFamily (certificateRecords C) h

theorem globallyCompleteCertificate_hasRecord_head (r : RecordData) (rs : RecordFamily) :
    GloballyCompleteCertificate (GlobalCertificate.mk (r :: rs)) →
      LocallyCompleteRecord r := by
  intro h
  exact globallyCompleteCertificate_mem (GlobalCertificate.mk (r :: rs)) h r
    (by simp [certificateRecords])

theorem globallyCompleteCertificate_hasRecord_tail (r s : RecordData) (rs : RecordFamily) :
    GloballyCompleteCertificate (GlobalCertificate.mk (r :: rs)) →
    s ∈ rs →
    LocallyCompleteRecord s := by
  intro h hs
  exact globallyCompleteCertificate_mem (GlobalCertificate.mk (r :: rs)) h s
    (by simp [certificateRecords, hs])

def CoverageReadyCertificate (C : GlobalCertificate) : Prop :=
  GloballyCompleteCertificate C

@[simp] theorem CoverageReadyCertificate_def (C : GlobalCertificate) :
    CoverageReadyCertificate C = GloballyCompleteCertificate C := rfl

theorem coverageReadyCertificate_implies_sound (C : GlobalCertificate) :
    CoverageReadyCertificate C → GloballySoundCertificate C := by
  intro h
  exact globallyComplete_implies_globallySoundCertificate C h

theorem coverageReadyCertificate_mem (C : GlobalCertificate) :
    CoverageReadyCertificate C →
      ∀ r, certificateHasRecord C r → LocallyCompleteRecord r := by
  intro h r hr
  exact globallyCompleteCertificate_mem C h r hr

theorem completeCertificate_coversSupport_readable (C : GlobalCertificate) (S : Support) :
    GloballyCompleteCertificate C →
    CertificateCoversSupport C S →
    CertificateCoversSupport C S := by
  intro _ h
  exact h

theorem completeCertificate_coversState_readable
    (P : Params) (C : GlobalCertificate) (U : State P) :
    GloballyCompleteCertificate C →
    CertificateCoversState P C U →
    CertificateCoversState P C U := by
  intro _ h
  exact h

structure CompletenessGlobalPackage where
  certificate : GlobalCertificate
  complete : GloballyCompleteCertificate certificate

@[simp] theorem CompletenessGlobalPackage.certificate_mk
    (C : GlobalCertificate) (h : GloballyCompleteCertificate C) :
    (CompletenessGlobalPackage.mk C h).certificate = C := rfl

@[simp] theorem CompletenessGlobalPackage.complete_mk
    (C : GlobalCertificate) (h : GloballyCompleteCertificate C) :
    (CompletenessGlobalPackage.mk C h).complete = h := rfl

def completeCertificateRecords (X : CompletenessGlobalPackage) : RecordFamily :=
  certificateRecords X.certificate

@[simp] theorem completeCertificateRecords_def (X : CompletenessGlobalPackage) :
    completeCertificateRecords X = certificateRecords X.certificate := rfl

theorem completePackage_mem (X : CompletenessGlobalPackage) :
    ∀ r, r ∈ completeCertificateRecords X → LocallyCompleteRecord r := by
  intro r hr
  rw [completeCertificateRecords_def] at hr
  exact globallyCompleteCertificate_mem X.certificate X.complete r hr

theorem completePackage_sound (X : CompletenessGlobalPackage) :
    GloballySoundCertificate X.certificate := by
  exact globallyComplete_implies_globallySoundCertificate X.certificate X.complete

theorem globallyCompleteFamily_exhaustive (R : RecordFamily) :
    GloballyCompleteRecordFamily R ∨ ¬ GloballyCompleteRecordFamily R := by
  exact Classical.em _

theorem globallyCompleteCertificate_exhaustive (C : GlobalCertificate) :
    GloballyCompleteCertificate C ∨ ¬ GloballyCompleteCertificate C := by
  exact Classical.em _

end Certificate
end CaseC
end Lehmer