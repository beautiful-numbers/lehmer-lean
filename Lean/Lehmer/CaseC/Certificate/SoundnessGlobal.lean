-- FILE: Lean/Lehmer/CaseC/Certificate/SoundnessGlobal.lean
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
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def GloballySoundRecordFamily (R : RecordFamily) : Prop :=
  ∀ r : RecordData, r ∈ R → LocallySoundRecord r

@[simp] theorem GloballySoundRecordFamily_def (R : RecordFamily) :
    GloballySoundRecordFamily R = (∀ r : RecordData, r ∈ R → LocallySoundRecord r) := rfl

def GloballySoundCertificate (C : GlobalCertificate) : Prop :=
  GloballySoundRecordFamily (certificateRecords C)

@[simp] theorem GloballySoundCertificate_def (C : GlobalCertificate) :
    GloballySoundCertificate C = GloballySoundRecordFamily (certificateRecords C) := rfl

theorem globallySoundFamily_nil :
    GloballySoundRecordFamily [] := by
  intro r hr
  simp at hr

theorem globallySoundFamily_cons (r : RecordData) (rs : RecordFamily) :
    GloballySoundRecordFamily (r :: rs) ↔
      LocallySoundRecord r ∧ GloballySoundRecordFamily rs := by
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

theorem globallySoundCertificate_iff_family (C : GlobalCertificate) :
    GloballySoundCertificate C ↔ GloballySoundRecordFamily (certificateRecords C) := by
  rfl

theorem globallySoundCertificate_nil :
    GloballySoundCertificate (GlobalCertificate.mk []) := by
  exact globallySoundFamily_nil

theorem globallySoundCertificate_cons (r : RecordData) (rs : RecordFamily) :
    GloballySoundCertificate (GlobalCertificate.mk (r :: rs)) ↔
      LocallySoundRecord r ∧ GloballySoundCertificate (GlobalCertificate.mk rs) := by
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

theorem globallySoundFamily_mem (R : RecordFamily) :
    GloballySoundRecordFamily R → ∀ r, r ∈ R → LocallySoundRecord r := by
  intro h r hr
  exact h r hr

theorem globallySoundCertificate_mem (C : GlobalCertificate) :
    GloballySoundCertificate C → ∀ r, certificateHasRecord C r → LocallySoundRecord r := by
  intro hC r hr
  exact hC r hr

theorem globallySoundFamily_of_pointwise (R : RecordFamily) :
    (∀ r, r ∈ R → LocallySoundRecord r) → GloballySoundRecordFamily R := by
  intro h
  exact h

theorem globallySoundCertificate_of_pointwise (C : GlobalCertificate) :
    (∀ r, certificateHasRecord C r → LocallySoundRecord r) → GloballySoundCertificate C := by
  intro h r hr
  exact h r hr

theorem globallySoundFamily_tail (r : RecordData) (rs : RecordFamily) :
    GloballySoundRecordFamily (r :: rs) → GloballySoundRecordFamily rs := by
  intro h
  exact (globallySoundFamily_cons r rs).mp h |>.2

theorem globallySoundFamily_head (r : RecordData) (rs : RecordFamily) :
    GloballySoundRecordFamily (r :: rs) → LocallySoundRecord r := by
  intro h
  exact (globallySoundFamily_cons r rs).mp h |>.1

theorem globallySoundCertificate_head (r : RecordData) (rs : RecordFamily) :
    GloballySoundCertificate (GlobalCertificate.mk (r :: rs)) → LocallySoundRecord r := by
  intro h
  exact (globallySoundCertificate_cons r rs).mp h |>.1

theorem globallySoundCertificate_tail (r : RecordData) (rs : RecordFamily) :
    GloballySoundCertificate (GlobalCertificate.mk (r :: rs)) →
      GloballySoundCertificate (GlobalCertificate.mk rs) := by
  intro h
  exact (globallySoundCertificate_cons r rs).mp h |>.2

structure SoundnessGlobalPackage where
  certificate : GlobalCertificate
  sound : GloballySoundCertificate certificate

@[simp] theorem SoundnessGlobalPackage.certificate_mk
    (C : GlobalCertificate) (h : GloballySoundCertificate C) :
    (SoundnessGlobalPackage.mk C h).certificate = C := rfl

@[simp] theorem SoundnessGlobalPackage.sound_mk
    (C : GlobalCertificate) (h : GloballySoundCertificate C) :
    (SoundnessGlobalPackage.mk C h).sound = h := rfl

def soundCertificateRecords (X : SoundnessGlobalPackage) : RecordFamily :=
  certificateRecords X.certificate

@[simp] theorem soundCertificateRecords_def (X : SoundnessGlobalPackage) :
    soundCertificateRecords X = certificateRecords X.certificate := rfl

theorem soundPackage_mem (X : SoundnessGlobalPackage) :
    ∀ r, r ∈ soundCertificateRecords X → LocallySoundRecord r := by
  intro r hr
  rw [soundCertificateRecords_def] at hr
  exact globallySoundCertificate_mem X.certificate X.sound r hr

theorem globallySoundFamily_exhaustive (R : RecordFamily) :
    GloballySoundRecordFamily R ∨ ¬ GloballySoundRecordFamily R := by
  exact Classical.em _

theorem globallySoundCertificate_exhaustive (C : GlobalCertificate) :
    GloballySoundCertificate C ∨ ¬ GloballySoundCertificate C := by
  exact Classical.em _

theorem globallySoundFamily_cons_intro (r : RecordData) (rs : RecordFamily) :
    LocallySoundRecord r →
    GloballySoundRecordFamily rs →
    GloballySoundRecordFamily (r :: rs) := by
  intro hr hrs
  exact (globallySoundFamily_cons r rs).mpr ⟨hr, hrs⟩

theorem globallySoundCertificate_cons_intro (r : RecordData) (rs : RecordFamily) :
    LocallySoundRecord r →
    GloballySoundCertificate (GlobalCertificate.mk rs) →
    GloballySoundCertificate (GlobalCertificate.mk (r :: rs)) := by
  intro hr h
  exact (globallySoundCertificate_cons r rs).mpr ⟨hr, h⟩

theorem globallySoundCertificate_hasRecord_head (r : RecordData) (rs : RecordFamily) :
    GloballySoundCertificate (GlobalCertificate.mk (r :: rs)) →
    LocallySoundRecord r := by
  intro h
  exact globallySoundCertificate_mem (GlobalCertificate.mk (r :: rs)) h r
    (by simp [certificateRecords])

theorem globallySoundCertificate_hasRecord_tail (r s : RecordData) (rs : RecordFamily) :
    GloballySoundCertificate (GlobalCertificate.mk (r :: rs)) →
    s ∈ rs →
    LocallySoundRecord s := by
  intro h hs
  exact globallySoundCertificate_mem (GlobalCertificate.mk (r :: rs)) h s
    (by simp [certificateRecords, hs])

end Certificate
end CaseC
end Lehmer