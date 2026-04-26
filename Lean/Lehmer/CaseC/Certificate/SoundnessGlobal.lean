-- FILE: Lean/Lehmer/CaseC/Certificate/SoundnessGlobal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.SoundnessLocal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def GloballySoundRecordFamily
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) : Prop :=
  ∀ r : RecordData P D, r ∈ R → LocallySoundRecord r

@[simp] theorem GloballySoundRecordFamily_def
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    GloballySoundRecordFamily P D R =
      (∀ r : RecordData P D, r ∈ R → LocallySoundRecord r) := rfl

def GloballySoundCertificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) : Prop :=
  GloballySoundRecordFamily P D (certificateRecords C)

@[simp] theorem GloballySoundCertificate_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballySoundCertificate P D C =
      GloballySoundRecordFamily P D (certificateRecords C) := rfl

theorem globallySoundFamily_nil
    (P : Params) (D : ClosureData P) :
    GloballySoundRecordFamily P D [] := by
  intro r hr
  simp at hr

theorem globallySoundFamily_cons
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    GloballySoundRecordFamily P D (r :: rs) ↔
      LocallySoundRecord r ∧ GloballySoundRecordFamily P D rs := by
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

theorem globallySoundCertificate_iff_family
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballySoundCertificate P D C ↔
      GloballySoundRecordFamily P D (certificateRecords C) := by
  rfl

theorem globallySoundFamily_mem
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    GloballySoundRecordFamily P D R →
      ∀ r : RecordData P D, r ∈ R → LocallySoundRecord r := by
  intro h r hr
  exact h r hr

theorem globallySoundCertificate_mem
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballySoundCertificate P D C →
      ∀ r : RecordData P D,
        certificateHasRecord C r → LocallySoundRecord r := by
  intro hC r hr
  exact hC r hr

theorem globallySoundFamily_of_pointwise
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    (∀ r : RecordData P D, r ∈ R → LocallySoundRecord r) →
      GloballySoundRecordFamily P D R := by
  intro h
  exact h

theorem globallySoundCertificate_of_pointwise
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    (∀ r : RecordData P D,
      certificateHasRecord C r → LocallySoundRecord r) →
      GloballySoundCertificate P D C := by
  intro h r hr
  exact h r hr

theorem globallySoundFamily_tail
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    GloballySoundRecordFamily P D (r :: rs) →
      GloballySoundRecordFamily P D rs := by
  intro h
  exact (globallySoundFamily_cons P D r rs).mp h |>.2

theorem globallySoundFamily_head
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    GloballySoundRecordFamily P D (r :: rs) →
      LocallySoundRecord r := by
  intro h
  exact (globallySoundFamily_cons P D r rs).mp h |>.1

theorem globallySoundFamily_cons_intro
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (rs : RecordFamily P D) :
    LocallySoundRecord r →
    GloballySoundRecordFamily P D rs →
    GloballySoundRecordFamily P D (r :: rs) := by
  intro hr hrs
  exact (globallySoundFamily_cons P D r rs).mpr ⟨hr, hrs⟩

structure SoundnessGlobalPackage
    (P : Params) (D : ClosureData P) where
  certificate : GlobalCertificate P D
  sound : GloballySoundCertificate P D certificate

@[simp] theorem SoundnessGlobalPackage.certificate_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (h : GloballySoundCertificate P D C) :
    (SoundnessGlobalPackage.mk C h).certificate = C := rfl

@[simp] theorem SoundnessGlobalPackage.sound_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (h : GloballySoundCertificate P D C) :
    (SoundnessGlobalPackage.mk C h).sound = h := rfl

def soundCertificateRecords
    (P : Params) (D : ClosureData P)
    (X : SoundnessGlobalPackage P D) : RecordFamily P D :=
  certificateRecords X.certificate

@[simp] theorem soundCertificateRecords_def
    (P : Params) (D : ClosureData P)
    (X : SoundnessGlobalPackage P D) :
    soundCertificateRecords P D X = certificateRecords X.certificate := rfl

theorem soundPackage_mem
    (P : Params) (D : ClosureData P)
    (X : SoundnessGlobalPackage P D) :
    ∀ r : RecordData P D,
      r ∈ soundCertificateRecords P D X → LocallySoundRecord r := by
  intro r hr
  rw [soundCertificateRecords_def] at hr
  exact globallySoundCertificate_mem P D X.certificate X.sound r hr

theorem globallySoundFamily_exhaustive
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) :
    GloballySoundRecordFamily P D R ∨
      ¬ GloballySoundRecordFamily P D R := by
  exact Classical.em _

theorem globallySoundCertificate_exhaustive
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballySoundCertificate P D C ∨
      ¬ GloballySoundCertificate P D C := by
  exact Classical.em _

theorem globallySoundCertificate_hasRecord
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hC : GloballySoundCertificate P D C)
    (r : RecordData P D)
    (hr : certificateHasRecord C r) :
    LocallySoundRecord r := by
  exact globallySoundCertificate_mem P D C hC r hr

end Certificate
end CaseC
end Lehmer