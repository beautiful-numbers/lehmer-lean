-- FILE: Lean/Lehmer/CaseC/Certificate/Coverage.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Priority : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def RecordCoversSupport (r : RecordData) (S : Support) : Prop :=
  S ∈ recordCylinder r

@[simp] theorem RecordCoversSupport_def (r : RecordData) (S : Support) :
    RecordCoversSupport r S = (S ∈ recordCylinder r) := rfl

theorem record_covers_iff_mem_cylinder (r : RecordData) (S : Support) :
    RecordCoversSupport r S ↔ S ∈ recordCylinder r := Iff.rfl

theorem recordCoversSupport_iff_prefix (r : RecordData) (S : Support) :
    RecordCoversSupport r S ↔ IsPrefixOf (recordPrefix r) S := by
  rfl

def RecordCoversState (P : Params) (r : RecordData) (U : State P) : Prop :=
  RecordCoversSupport r U.support

@[simp] theorem RecordCoversState_def (P : Params) (r : RecordData) (U : State P) :
    RecordCoversState P r U = RecordCoversSupport r U.support := rfl

theorem recordCoversState_iff_support (P : Params) (r : RecordData) (U : State P) :
    RecordCoversState P r U ↔ RecordCoversSupport r U.support := Iff.rfl

def RecordChildrenCoverSupport (r : RecordData) (S : Support) : Prop :=
  ∃ p ∈ recordChildren r, S ∈ Cylinder p

@[simp] theorem RecordChildrenCoverSupport_def (r : RecordData) (S : Support) :
    RecordChildrenCoverSupport r S = (∃ p ∈ recordChildren r, S ∈ Cylinder p) := rfl

def RecordChildrenCoverState (P : Params) (r : RecordData) (U : State P) : Prop :=
  RecordChildrenCoverSupport r U.support

@[simp] theorem RecordChildrenCoverState_def (P : Params) (r : RecordData) (U : State P) :
    RecordChildrenCoverState P r U = RecordChildrenCoverSupport r U.support := rfl

def CertificateCoversSupport (C : GlobalCertificate) (S : Support) : Prop :=
  ∃ r, certificateHasRecord C r ∧ RecordCoversSupport r S

@[simp] theorem CertificateCoversSupport_def (C : GlobalCertificate) (S : Support) :
    CertificateCoversSupport C S = (∃ r, certificateHasRecord C r ∧ RecordCoversSupport r S) := rfl

def CertificateCoversState (P : Params) (C : GlobalCertificate) (U : State P) : Prop :=
  CertificateCoversSupport C U.support

@[simp] theorem CertificateCoversState_def (P : Params) (C : GlobalCertificate) (U : State P) :
    CertificateCoversState P C U = CertificateCoversSupport C U.support := rfl

theorem certificateCoversState_iff_support (P : Params) (C : GlobalCertificate) (U : State P) :
    CertificateCoversState P C U ↔ CertificateCoversSupport C U.support := Iff.rfl

def FamilyCoversSupport (R : RecordFamily) (S : Support) : Prop :=
  ∃ r, r ∈ R ∧ RecordCoversSupport r S

@[simp] theorem FamilyCoversSupport_def (R : RecordFamily) (S : Support) :
    FamilyCoversSupport R S = (∃ r, r ∈ R ∧ RecordCoversSupport r S) := rfl

theorem certificateCoversSupport_iff_family (C : GlobalCertificate) (S : Support) :
    CertificateCoversSupport C S ↔ FamilyCoversSupport (certificateRecords C) S := by
  constructor
  · intro h
    rcases h with ⟨r, hrC, hrS⟩
    exact ⟨r, hrC, hrS⟩
  · intro h
    rcases h with ⟨r, hrC, hrS⟩
    exact ⟨r, hrC, hrS⟩

@[simp] theorem FamilyCoversSupport_nil (S : Support) :
    ¬ FamilyCoversSupport [] S := by
  intro h
  rcases h with ⟨r, hr, _⟩
  simp at hr

theorem FamilyCoversSupport_cons (r : RecordData) (rs : RecordFamily) (S : Support) :
    FamilyCoversSupport (r :: rs) S ↔
      RecordCoversSupport r S ∨ FamilyCoversSupport rs S := by
  constructor
  · intro h
    rcases h with ⟨r', hr', hcov⟩
    simp at hr'
    rcases hr' with rfl | hrs
    · exact Or.inl hcov
    · exact Or.inr ⟨r', hrs, hcov⟩
  · intro h
    rcases h with h | h
    · exact ⟨r, by simp, h⟩
    · rcases h with ⟨r', hr', hcov⟩
      exact ⟨r', by simp [hr'], hcov⟩

@[simp] theorem CertificateCoversSupport_empty (S : Support) :
    ¬ CertificateCoversSupport (GlobalCertificate.mk []) S := by
  intro h
  rcases h with ⟨r, hr, _⟩
  simp [certificateHasRecord, certificateRecords] at hr

theorem CertificateCoversSupport_cons (r : RecordData) (rs : RecordFamily) (S : Support) :
    CertificateCoversSupport (GlobalCertificate.mk (r :: rs)) S ↔
      RecordCoversSupport r S ∨ CertificateCoversSupport (GlobalCertificate.mk rs) S := by
  constructor
  · intro h
    rcases h with ⟨r', hr', hcov⟩
    simp [certificateHasRecord, certificateRecords] at hr'
    rcases hr' with rfl | hrs
    · exact Or.inl hcov
    · exact Or.inr ⟨r', hrs, hcov⟩
  · intro h
    rcases h with h | h
    · exact ⟨r, by simp [certificateHasRecord, certificateRecords], h⟩
    · rcases h with ⟨r', hr', hcov⟩
      have hrs : r' ∈ rs := by
        simpa [certificateHasRecord, certificateRecords] using hr'
      exact ⟨r', by simp [certificateHasRecord, certificateRecords, hrs], hcov⟩

theorem CertificateCoversSupport_of_hasRecord (C : GlobalCertificate) (r : RecordData) (S : Support) :
    certificateHasRecord C r → RecordCoversSupport r S → CertificateCoversSupport C S := by
  intro hr hcov
  exact ⟨r, hr, hcov⟩

theorem CertificateCoversState_of_hasRecord (P : Params) (C : GlobalCertificate)
    (r : RecordData) (U : State P) :
    certificateHasRecord C r → RecordCoversState P r U → CertificateCoversState P C U := by
  intro hr hcov
  exact ⟨r, hr, hcov⟩

theorem certificateHasRecord_cons_head (r : RecordData) (rs : RecordFamily) :
    certificateHasRecord (GlobalCertificate.mk (r :: rs)) r := by
  simp [certificateHasRecord, certificateRecords]

theorem certificateHasRecord_cons_tail (r s : RecordData) (rs : RecordFamily) :
    certificateHasRecord (GlobalCertificate.mk rs) s →
    certificateHasRecord (GlobalCertificate.mk (r :: rs)) s := by
  intro hs
  have hs' : s ∈ rs := by
    simpa [certificateHasRecord, certificateRecords] using hs
  simp [certificateHasRecord, certificateRecords, hs']

theorem RecordCoversState_mk (P : Params) (r : RecordData) (S : Support) :
    RecordCoversState P r (State.mk S) ↔ RecordCoversSupport r S := Iff.rfl

theorem CertificateCoversState_mk (P : Params) (C : GlobalCertificate) (S : Support) :
    CertificateCoversState P C (State.mk S) ↔ CertificateCoversSupport C S := Iff.rfl

theorem RecordChildrenCoverState_mk (P : Params) (r : RecordData) (S : Support) :
    RecordChildrenCoverState P r (State.mk S) ↔ RecordChildrenCoverSupport r S := Iff.rfl

end Certificate
end CaseC
end Lehmer