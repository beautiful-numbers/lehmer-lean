-- FILE: Lean/Lehmer/CaseC/Certificate/CheckerGlobal.lean

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
- Lehmer.CaseC.Certificate.CheckerLocal : def thm
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
import Lehmer.CaseC.Certificate.CheckerLocal
import Lehmer.CaseC.Certificate.VerifiedRecordSoundness

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def GlobalLocalCheck
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) : Prop :=
  ∀ r : RecordData P D,
    certificateHasRecord C r →
      CheckerLocalPackage P D r

@[simp] theorem GlobalLocalCheck_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GlobalLocalCheck P D C =
      (∀ r : RecordData P D,
        certificateHasRecord C r →
          CheckerLocalPackage P D r) := rfl

def GloballyCheckedCertificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) : Prop :=
  GlobalLocalCheck P D C

@[simp] theorem GloballyCheckedCertificate_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) :
    GloballyCheckedCertificate P D C =
      GlobalLocalCheck P D C := rfl

structure CheckerGlobalPackage
    (P : Params) (D : ClosureData P) where
  certificate : GlobalCertificate P D
  localChecks : GlobalLocalCheck P D certificate

@[simp] theorem CheckerGlobalPackage.certificate_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C) :
    (CheckerGlobalPackage.mk C hL).certificate = C := rfl

@[simp] theorem CheckerGlobalPackage.localChecks_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C) :
    (CheckerGlobalPackage.mk C hL).localChecks = hL := rfl

def mkCheckerGlobalPackage
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C) :
    CheckerGlobalPackage P D :=
  { certificate := C
    localChecks := hL }

@[simp] theorem mkCheckerGlobalPackage_certificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C) :
    (mkCheckerGlobalPackage P D C hL).certificate = C := rfl

@[simp] theorem mkCheckerGlobalPackage_localChecks
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C) :
    (mkCheckerGlobalPackage P D C hL).localChecks = hL := rfl

theorem CheckerGlobalPackage.localPackage
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    CheckerLocalPackage P D r := by
  exact X.localChecks r hr

theorem CheckerGlobalPackage.local_checked
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    LocallyCheckedRecord r := by
  exact (CheckerGlobalPackage.localPackage P D X r hr).checked

theorem CheckerGlobalPackage.local_sound
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    LocallySoundRecord r := by
  exact locallyCheckedRecord_sound r
    (CheckerGlobalPackage.local_checked P D X r hr)

theorem CheckerGlobalPackage.local_complete
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    LocallyCompleteRecord r := by
  exact locallyCheckedRecord_complete r
    (CheckerGlobalPackage.local_checked P D X r hr)

theorem CheckerGlobalPackage.local_routing_cases
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    IsEmptinessRecord r ∨
      IsExclusionRecord r ∨
      IsFiniteReductionRecord r := by
  exact CheckerLocalPackage.routing_cases P D
    (CheckerGlobalPackage.localPackage P D X r hr)

theorem CheckerGlobalPackage.record_closes_or_routes_support
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S)
    (hCandClosed :
      ∀ d : ExclusionData P D r.pref,
        d.kind = ExclusionKind.candNFailure →
          CandNEmpty P D S →
          False)
    (hNonInt :
      ∀ d : ExclusionData P D r.pref,
        d.kind = ExclusionKind.nonIntegrality →
          supportNonIntegral S →
          False)
    (hChildClosed :
      ∀ child : Prefix,
        PrefixCoversSupport child S →
          False) :
    False := by
  exact CheckerLocalPackage.closes_or_routes_support P D
    (CheckerGlobalPackage.localPackage P D X r hr)
    S hAdm hCov hCandClosed hNonInt hChildClosed

def CheckerGlobalPackage.local_verified
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    VerifiedRecordCertificate P D r :=
  VerifiedRecordCertificate.mk
    (CheckerGlobalPackage.localPackage P D X r hr)

def CheckerGlobalPackage.verifiedRecords
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D) :
    VerifiedCertificateRecords P D X.certificate :=
  fun r hr =>
    CheckerGlobalPackage.local_verified P D X r hr

@[simp] theorem CheckerGlobalPackage.verifiedRecords_apply
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    CheckerGlobalPackage.verifiedRecords P D X r hr =
      CheckerGlobalPackage.local_verified P D X r hr := rfl

def verifiedCertificateRecords_of_globalLocalCheck
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C) :
    VerifiedCertificateRecords P D C :=
  fun r hr =>
    VerifiedRecordCertificate.mk (hL r hr)

@[simp] theorem verifiedCertificateRecords_of_globalLocalCheck_apply
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C)
    (r : RecordData P D)
    (hr : certificateHasRecord C r) :
    verifiedCertificateRecords_of_globalLocalCheck P D C hL r hr =
      VerifiedRecordCertificate.mk (hL r hr) := rfl

def globallyCheckedCertificate_verifiedRecords
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hG : GloballyCheckedCertificate P D C) :
    VerifiedCertificateRecords P D C :=
  verifiedCertificateRecords_of_globalLocalCheck P D C hG

theorem CheckerGlobalPackage.checked
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D) :
    GloballyCheckedCertificate P D X.certificate := by
  exact X.localChecks

def CheckerGlobalPackage.to_verifiedRecords
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D) :
    VerifiedCertificateRecords P D X.certificate :=
  CheckerGlobalPackage.verifiedRecords P D X

def checkerGlobalPackage_verifiedRecords
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D) :
    VerifiedCertificateRecords P D X.certificate :=
  CheckerGlobalPackage.to_verifiedRecords P D X

def checkerGlobalPackage_mem_verified
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    VerifiedRecordCertificate P D r :=
  CheckerGlobalPackage.local_verified P D X r hr

theorem checkerGlobalPackage_mem_checked
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    LocallyCheckedRecord r := by
  exact CheckerGlobalPackage.local_checked P D X r hr

theorem checkerGlobalPackage_mem_sound
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    LocallySoundRecord r := by
  exact CheckerGlobalPackage.local_sound P D X r hr

theorem checkerGlobalPackage_mem_complete
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (hr : certificateHasRecord X.certificate r) :
    LocallyCompleteRecord r := by
  exact CheckerGlobalPackage.local_complete P D X r hr

def checkedCertificateRecords
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D) : RecordFamily P D :=
  certificateRecords X.certificate

@[simp] theorem checkedCertificateRecords_def
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D) :
    checkedCertificateRecords P D X =
      certificateRecords X.certificate := rfl

def checkedCertificateHead?
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D) : Option (RecordData P D) :=
  match X.certificate.records with
  | [] => none
  | r :: _ => some r

@[simp] theorem checkedCertificateHead?_eq_none_of_records_eq_nil
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (h : X.certificate.records = []) :
    checkedCertificateHead? P D X = none := by
  simp [checkedCertificateHead?, h]

@[simp] theorem checkedCertificateHead?_eq_some_of_records_eq_cons
    (P : Params) (D : ClosureData P)
    (X : CheckerGlobalPackage P D)
    (r : RecordData P D)
    (rs : RecordFamily P D)
    (h : X.certificate.records = r :: rs) :
    checkedCertificateHead? P D X = some r := by
  simp [checkedCertificateHead?, h]

@[simp] theorem checkedCertificateHead?_nil
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C)
    (h : C.records = []) :
    checkedCertificateHead? P D
      (mkCheckerGlobalPackage P D C hL) = none := by
  simp [checkedCertificateHead?, mkCheckerGlobalPackage, h]

@[simp] theorem checkedCertificateHead?_cons
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (hL : GlobalLocalCheck P D C)
    (r : RecordData P D)
    (rs : RecordFamily P D)
    (h : C.records = r :: rs) :
    checkedCertificateHead? P D
      (mkCheckerGlobalPackage P D C hL) = some r := by
  simp [checkedCertificateHead?, mkCheckerGlobalPackage, h]

end Certificate
end CaseC
end Lehmer