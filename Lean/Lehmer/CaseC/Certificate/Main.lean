-- FILE: Lean/Lehmer/CaseC/Certificate/Main.lean
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
- Lehmer.CaseC.Certificate.CompletenessGlobal : def thm
- Lehmer.CaseC.Certificate.CheckerLocal : def thm
- Lehmer.CaseC.Certificate.CheckerGlobal : def thm
- Lehmer.CaseC.Certificate.VerifiedRecordSoundness : def thm
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
import Lehmer.CaseC.Certificate.CompletenessGlobal
import Lehmer.CaseC.Certificate.CheckerLocal
import Lehmer.CaseC.Certificate.CheckerGlobal
import Lehmer.CaseC.Certificate.VerifiedRecordSoundness

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic
open Lehmer.Pipeline

def CertificateMainChecked
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) : Type :=
  VerifiedCertificateRecords P D C

@[simp] theorem CertificateMainChecked_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    CertificateMainChecked P D C =
      VerifiedCertificateRecords P D C := rfl

structure CertificateMainPackage
    (P : Params) (D : ClosureData P) where
  certificate : GlobalCertificate P D
  verifiedRecords : VerifiedCertificateRecords P D certificate

@[simp] theorem CertificateMainPackage.certificate_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C) :
    (CertificateMainPackage.mk C hV).certificate = C := rfl

@[simp] theorem CertificateMainPackage.verifiedRecords_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C) :
    (CertificateMainPackage.mk C hV).verifiedRecords = hV := rfl

def mkCertificateMainPackage
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C) :
    CertificateMainPackage P D :=
  { certificate := C
    verifiedRecords := hV }

@[simp] theorem mkCertificateMainPackage_certificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C) :
    (mkCertificateMainPackage P D C hV).certificate = C := rfl

@[simp] theorem mkCertificateMainPackage_verifiedRecords
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C) :
    (mkCertificateMainPackage P D C hV).verifiedRecords = hV := rfl

def CertificateMainPackage.records
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D) : RecordFamily P D :=
  certificateRecords X.certificate

@[simp] theorem CertificateMainPackage.records_def
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D) :
    X.records P D = certificateRecords X.certificate := rfl

def CertificateMainPackage.head?
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D) : Option (RecordData P D) :=
  X.certificate.records.head?

@[simp] theorem CertificateMainPackage.head?_nil
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (h : C.records = []) :
    (CertificateMainPackage.mk C hV).head? P D = none := by
  simp [CertificateMainPackage.head?, h]

@[simp] theorem CertificateMainPackage.head?_cons
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (r : RecordData P D)
    (rs : RecordFamily P D)
    (h : C.records = r :: rs) :
    (CertificateMainPackage.mk C hV).head? P D = some r := by
  simp [CertificateMainPackage.head?, h]

theorem CertificateMainPackage.head?_eq_none_of_records_eq_nil
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (h : X.certificate.records = []) :
    X.head? P D = none := by
  simp [CertificateMainPackage.head?, h]

theorem CertificateMainPackage.head?_eq_some_of_records_eq_cons
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (r : RecordData P D)
    (rs : RecordFamily P D)
    (h : X.certificate.records = r :: rs) :
    X.head? P D = some r := by
  simp [CertificateMainPackage.head?, h]

def CertificateMainPackage.checked
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D) :
    CertificateMainChecked P D X.certificate :=
  X.verifiedRecords

def CertificateMainPackage.verified
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D) :
    VerifiedCertificateRecords P D X.certificate :=
  X.verifiedRecords

def CertificateMainPackage.mem_verified
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D) :
    ∀ r : RecordData P D,
      certificateHasRecord X.certificate r →
        VerifiedRecordCertificate P D r :=
  fun r hr => X.verifiedRecords r hr

theorem CertificateMainPackage.covers_admissible_support
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    GlobalCertificateCoversSupport P D X.certificate S := by
  exact globalCertificate_covers_admissible_support
    P D X.certificate S hAdm

theorem CertificateMainPackage.covers_admissible_state
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    GlobalCertificateCoversState P D X.certificate U := by
  exact globalCertificate_covers_admissible_state
    P D X.certificate U hAdm

theorem CertificateMainPackage.excludes_covered_support
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (Γ : VerifiedRecordSoundnessContext P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCover : GlobalCertificateCoversSupport P D X.certificate S) :
    False := by
  exact verifiedCertificateRecords_excludes_covered_support
    P D Γ X.certificate X.verifiedRecords S hAdm hCover

theorem CertificateMainPackage.excludes_covered_state
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (Γ : VerifiedRecordSoundnessContext P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support)
    (hCover : GlobalCertificateCoversState P D X.certificate U) :
    False := by
  exact verifiedCertificateRecords_excludes_covered_state
    P D Γ X.certificate X.verifiedRecords U hAdm hCover

theorem CertificateMainPackage.excludes_covered_candidate
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (Γ : VerifiedRecordSoundnessContext P D)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n)
    (hAdm : CaseCAdmissibleSupport P D (candidateSupport n))
    (hCover :
      CandidateCoveredByCertificate P D X.certificate n) :
    False := by
  exact verifiedCertificateRecords_excludes_covered_candidate
    P D Γ X.certificate X.verifiedRecords hL hC hAdm hCover

theorem CertificateMainPackage.excludes_admissible_support
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (Γ : VerifiedRecordSoundnessContext P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    False := by
  exact verifiedCertificateRecords_excludes_admissible_support
    P D Γ X.certificate X.verifiedRecords S hAdm

theorem CertificateMainPackage.excludes_admissible_state
    (P : Params) (D : ClosureData P)
    (X : CertificateMainPackage P D)
    (Γ : VerifiedRecordSoundnessContext P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    False := by
  exact verifiedCertificateRecords_excludes_admissible_state
    P D Γ X.certificate X.verifiedRecords U hAdm

end Certificate
end CaseC
end Lehmer