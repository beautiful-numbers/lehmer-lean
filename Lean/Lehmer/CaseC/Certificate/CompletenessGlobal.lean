-- FILE: Lean/Lehmer/CaseC/Certificate/CompletenessGlobal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def thm
- Lehmer.CaseC.Certificate.Record : def thm
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
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal
import Lehmer.CaseC.Certificate.CompletenessLocal
import Lehmer.CaseC.Certificate.SoundnessGlobal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

-- Define CertificateCoversState to ensure the certificate covers the state
def CertificateCoversState
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) (U : State P) : Prop :=
  ∀ r : RecordData P D, r ∈ R → RecordCoversState P D r U

-- GloballyCompleteRecordFamily ensures all records in the family are locally complete
def GloballyCompleteRecordFamily
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) : Prop :=
  ∀ r : RecordData P D, r ∈ R → LocallyCompleteRecord r

@[simp] theorem GloballyCompleteRecordFamily_def
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    GloballyCompleteRecordFamily P D R =
      (∀ r : RecordData P D, r ∈ R → LocallyCompleteRecord r) := rfl

-- GloballyCompleteCertificate ensures the certificate is globally complete
def GloballyCompleteCertificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) : Prop :=
  GloballyCompleteRecordFamily P D (certificateRecords C)

@[simp] theorem GloballyCompleteCertificate_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballyCompleteCertificate P D C =
      GloballyCompleteRecordFamily P D (certificateRecords C) := rfl

theorem globallyCompleteFamily_nil
    (P : Params) (D : ClosureData P) :
    GloballyCompleteRecordFamily P D [] := by
  intro r hr
  simp at hr

theorem globallyCompleteFamily_cons
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    GloballyCompleteRecordFamily P D (r :: rs) ↔
      LocallyCompleteRecord r ∧ GloballyCompleteRecordFamily P D rs := by
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

theorem globallyCompleteCertificate_iff_family
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballyCompleteCertificate P D C ↔
      GloballyCompleteRecordFamily P D (certificateRecords C) := by
  rfl

theorem globallyCompleteFamily_mem
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    GloballyCompleteRecordFamily P D R →
      ∀ r : RecordData P D, r ∈ R → LocallyCompleteRecord r := by
  intro h r hr
  exact h r hr

theorem globallyCompleteCertificate_mem
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballyCompleteCertificate P D C →
      ∀ r : RecordData P D,
        certificateHasRecord C r → LocallyCompleteRecord r := by
  intro hC r hr
  exact hC r hr

theorem globallyCompleteFamily_of_pointwise
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    (∀ r : RecordData P D, r ∈ R → LocallyCompleteRecord r) →
      GloballyCompleteRecordFamily P D R := by
  intro h
  exact h

theorem globallyCompleteCertificate_of_pointwise
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    (∀ r : RecordData P D,
      certificateHasRecord C r → LocallyCompleteRecord r) →
      GloballyCompleteCertificate P D C := by
  intro h r hr
  exact h r hr

theorem globallyCompleteFamily_head
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    GloballyCompleteRecordFamily P D (r :: rs) →
      LocallyCompleteRecord r := by
  intro h
  exact (globallyCompleteFamily_cons P D r rs).mp h |>.1

theorem globallyCompleteFamily_tail
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    GloballyCompleteRecordFamily P D (r :: rs) →
      GloballyCompleteRecordFamily P D rs := by
  intro h
  exact (globallyCompleteFamily_cons P D r rs).mp h |>.2

theorem globallyCompleteFamily_cons_intro
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    LocallyCompleteRecord r →
    GloballyCompleteRecordFamily P D rs →
    GloballyCompleteRecordFamily P D (r :: rs) := by
  intro hr hrs
  exact (globallyCompleteFamily_cons P D r rs).mpr ⟨hr, hrs⟩

theorem globallyComplete_implies_globallySoundFamily
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    GloballyCompleteRecordFamily P D R →
      GloballySoundRecordFamily P D R := by
  intro h r hr
  exact locallyComplete_implies_locallySound r (h r hr)

theorem globallyComplete_implies_globallySoundCertificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballyCompleteCertificate P D C →
      GloballySoundCertificate P D C := by
  intro h
  exact globallyComplete_implies_globallySoundFamily
    P D (certificateRecords C) h

def CoverageReadyCertificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) : Prop :=
  GloballyCompleteCertificate P D C

@[simp] theorem CoverageReadyCertificate_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    CoverageReadyCertificate P D C =
      GloballyCompleteCertificate P D C := rfl

theorem coverageReadyCertificate_implies_sound
    (P : Params) {D : ClosureData P}
    (C : GlobalCertificate P D) :
    CoverageReadyCertificate P D C →
      GloballySoundCertificate P D C := by
  intro h
  exact globallyComplete_implies_globallySoundCertificate P D C h

theorem coverageReadyCertificate_mem
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    CoverageReadyCertificate P D C →
      ∀ r : RecordData P D,
        certificateHasRecord C r → LocallyCompleteRecord r := by
  intro h r hr
  exact globallyCompleteCertificate_mem P D C h r hr

theorem completeCertificate_coversSupport_readable
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) (S : Support) :
    GloballyCompleteCertificate P D C →
    CertificateCoversSupport P D (certificateRecords C) S →
    CertificateCoversSupport P D (certificateRecords C) S := by
  intro _ h
  exact h

theorem completeCertificate_coversState_readable
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) (U : State P) :
    GloballyCompleteCertificate P D C →
    CertificateCoversState P D (certificateRecords C) U →
    CertificateCoversState P D (certificateRecords C) U := by
  intro _ h
  exact h

structure CompletenessGlobalPackage
    (P : Params) (D : ClosureData P) where
  certificate : GlobalCertificate P D
  complete : GloballyCompleteCertificate P D certificate

@[simp] theorem CompletenessGlobalPackage.certificate_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (h : GloballyCompleteCertificate P D C) :
    (CompletenessGlobalPackage.mk C h).certificate = C := rfl

@[simp] theorem CompletenessGlobalPackage.complete_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (h : GloballyCompleteCertificate P D C) :
    (CompletenessGlobalPackage.mk C h).complete = h := rfl

def completeCertificateRecords
    (P : Params) (D : ClosureData P)
    (X : CompletenessGlobalPackage P D) : RecordFamily P D :=
  certificateRecords X.certificate

@[simp] theorem completeCertificateRecords_def
    (P : Params) (D : ClosureData P)
    (X : CompletenessGlobalPackage P D) :
    completeCertificateRecords P D X = certificateRecords X.certificate := rfl

theorem completePackage_mem
    (P : Params) (D : ClosureData P)
    (X : CompletenessGlobalPackage P D) :
    ∀ r : RecordData P D,
      r ∈ completeCertificateRecords P D X →
        LocallyCompleteRecord r := by
  intro r hr
  rw [completeCertificateRecords_def] at hr
  exact globallyCompleteCertificate_mem P D X.certificate X.complete r hr

theorem completePackage_sound
    (P : Params) (D : ClosureData P)
    (X : CompletenessGlobalPackage P D) :
    GloballySoundCertificate P D X.certificate := by
  exact globallyComplete_implies_globallySoundCertificate
    P D X.certificate X.complete

theorem globallyCompleteFamily_exhaustive
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    GloballyCompleteRecordFamily P D R ∨
      ¬ GloballyCompleteRecordFamily P D R := by
  exact Classical.em _

theorem globallyCompleteCertificate_exhaustive
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballyCompleteCertificate P D C ∨
      ¬ GloballyCompleteCertificate P D C := by
  exact Classical.em _

end Certificate
end CaseC
end Lehmer