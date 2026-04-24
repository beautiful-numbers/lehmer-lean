-- FILE: Lean/Lehmer/CaseC/Main.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.CaseC.GapClosure.KmaxGap : def thm
- Lehmer.CaseC.GapClosure.GapToClosure : def thm
- Lehmer.CaseC.StateMachine.ResidualClosure : def thm
- Lehmer.CaseC.Certificate.Main : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.KmaxGap
import Lehmer.CaseC.GapClosure.GapToClosure
import Lehmer.CaseC.StateMachine.ResidualClosure
import Lehmer.CaseC.Certificate.Main
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC

open Lehmer.Basic
open Lehmer.Pipeline

def CaseCImpossible : Prop :=
  ∀ n : ℕ, LehmerComposite n → InCaseC n → False

@[simp] theorem CaseCImpossible_def :
    CaseCImpossible =
      (∀ n : ℕ, LehmerComposite n → InCaseC n → False) := rfl

structure CaseCMainPackage (P : Params) (D : ClosureData P) where
  nonIntegrality : GapClosure.NonIntegralityFamilyPackage P D
  kmaxGap : GapClosure.KmaxGapPackage P D
  gap : GapClosure.GapClosurePackage P D
  residual : StateMachine.ResidualClosurePackage P D
  certificate : Certificate.CertificateMainPackage
  impossible : CaseCImpossible

@[simp] theorem CaseCMainPackage.nonIntegrality_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (CaseCMainPackage.mk NI KG G R C hI).nonIntegrality = NI := rfl

@[simp] theorem CaseCMainPackage.kmaxGap_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (CaseCMainPackage.mk NI KG G R C hI).kmaxGap = KG := rfl

@[simp] theorem CaseCMainPackage.gap_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (CaseCMainPackage.mk NI KG G R C hI).gap = G := rfl

@[simp] theorem CaseCMainPackage.residual_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (CaseCMainPackage.mk NI KG G R C hI).residual = R := rfl

@[simp] theorem CaseCMainPackage.certificate_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (CaseCMainPackage.mk NI KG G R C hI).certificate = C := rfl

@[simp] theorem CaseCMainPackage.impossible_mk
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (CaseCMainPackage.mk NI KG G R C hI).impossible = hI := rfl

def CaseCMainReady (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : Prop :=
  Certificate.CertificateMainChecked X.certificate.certificate

@[simp] theorem CaseCMainReady_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCMainReady P D X =
      Certificate.CertificateMainChecked X.certificate.certificate := rfl

theorem caseCMainReady (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    CaseCMainReady P D X := by
  exact X.certificate.checked

def caseCMainGapFamily (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : GapClosure.SupportProfileFamily :=
  GapClosure.kmaxGapFamily P D X.kmaxGap

@[simp] theorem caseCMainGapFamily_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainGapFamily P D X = GapClosure.kmaxGapFamily P D X.kmaxGap := rfl

def caseCMainGapValue (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : ℕ :=
  GapClosure.kmaxGapValue P D X.kmaxGap

@[simp] theorem caseCMainGapValue_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainGapValue P D X = GapClosure.kmaxGapValue P D X.kmaxGap := rfl

def caseCMainKmaxValue (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : ℕ :=
  GapClosure.kmaxGapKmaxValue P D X.kmaxGap

@[simp] theorem caseCMainKmaxValue_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainKmaxValue P D X = GapClosure.kmaxGapKmaxValue P D X.kmaxGap := rfl

def caseCMainClosureCapValue (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : ℕ :=
  GapClosure.kmaxGapClosureCapValue P D X.kmaxGap

@[simp] theorem caseCMainClosureCapValue_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainClosureCapValue P D X =
      GapClosure.kmaxGapClosureCapValue P D X.kmaxGap := rfl

theorem caseCMainGapValue_pos (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    0 < caseCMainGapValue P D X := by
  exact GapClosure.kmaxGapValue_pos P D X.kmaxGap

theorem caseCMainKmaxValue_pos (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    0 < caseCMainKmaxValue P D X := by
  exact GapClosure.kmaxGapKmaxValue_pos P D X.kmaxGap

theorem caseCMainClosureCapValue_pos (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    0 < caseCMainClosureCapValue P D X := by
  exact GapClosure.kmaxGapClosureCapValue_pos P D X.kmaxGap

theorem caseCMainGapFamily_mem_hasWitness (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ R, R ∈ caseCMainGapFamily P D X →
      GapClosure.hasNonIntegralityWitness P D R := by
  intro R hR
  exact GapClosure.kmaxGapFamily_mem_hasWitness P D X.kmaxGap R hR

theorem caseCMainGapFamily_mem_rigid (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ R, R ∈ caseCMainGapFamily P D X →
      GapClosure.RigidProfile P D R := by
  intro R hR
  exact GapClosure.kmaxGapFamily_mem_rigid P D X.kmaxGap R hR

theorem caseCMainResidualClosed (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    StateMachine.ResidualClosed P D X.residual.state := by
  exact X.residual.closed

def caseCMainCertificate (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : Certificate.GlobalCertificate :=
  X.certificate.certificate

@[simp] theorem caseCMainCertificate_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainCertificate P D X = X.certificate.certificate := rfl

theorem caseCMainCertificate_checked (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    Certificate.CertificateMainChecked (caseCMainCertificate P D X) := by
  simpa [caseCMainCertificate] using X.certificate.checked

theorem caseCMainCertificate_sound (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    Certificate.GloballySoundCertificate (caseCMainCertificate P D X) := by
  simpa [caseCMainCertificate] using X.certificate.sound

theorem caseCMainCertificate_complete (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    Certificate.GloballyCompleteCertificate (caseCMainCertificate P D X) := by
  simpa [caseCMainCertificate] using X.certificate.complete

theorem caseCMainCertificate_coverageReady (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    Certificate.CoverageReadyCertificate (caseCMainCertificate P D X) := by
  simpa [caseCMainCertificate] using X.certificate.coverageReady

theorem caseCMainCertificate_mem_sound (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ r, Certificate.certificateHasRecord (caseCMainCertificate P D X) r →
      Certificate.LocallySoundRecord r := by
  intro r hr
  simpa [caseCMainCertificate] using X.certificate.mem_sound r hr

theorem caseCMainCertificate_mem_complete (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ r, Certificate.certificateHasRecord (caseCMainCertificate P D X) r →
      Certificate.LocallyCompleteRecord r := by
  intro r hr
  simpa [caseCMainCertificate] using X.certificate.mem_complete r hr

theorem caseCMainCertificate_mem_checked (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    ∀ r, Certificate.certificateHasRecord (caseCMainCertificate P D X) r →
      Certificate.LocallyCheckedRecord r := by
  intro r hr
  simpa [caseCMainCertificate] using X.certificate.mem_checked r hr

def caseCMainCertificateHead? (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) : Option Certificate.RecordData :=
  X.certificate.head?

@[simp] theorem caseCMainCertificateHead?_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    caseCMainCertificateHead? P D X = X.certificate.head? := rfl

def caseCMainImpossibleAt (P : Params) (D : ClosureData P)
    (_ : CaseCMainPackage P D) (n : ℕ) : Prop :=
  LehmerComposite n → InCaseC n → False

@[simp] theorem caseCMainImpossibleAt_def (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) (n : ℕ) :
    caseCMainImpossibleAt P D X n =
      (LehmerComposite n → InCaseC n → False) := rfl

theorem CaseCMainPackage.impossible_pointwise
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) (hC : InCaseC n) :
    False := by
  exact X.impossible n hL hC

theorem CaseCMainPackage.not_inCaseC_of_LehmerComposite
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  intro hC
  exact CaseCMainPackage.impossible_pointwise P D X hL hC

def mkCaseCMainPackage (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    CaseCMainPackage P D :=
  CaseCMainPackage.mk NI KG G R C hI

@[simp] theorem mkCaseCMainPackage_nonIntegrality
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (mkCaseCMainPackage P D NI KG G R C hI).nonIntegrality = NI := rfl

@[simp] theorem mkCaseCMainPackage_kmaxGap
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (mkCaseCMainPackage P D NI KG G R C hI).kmaxGap = KG := rfl

@[simp] theorem mkCaseCMainPackage_gap
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (mkCaseCMainPackage P D NI KG G R C hI).gap = G := rfl

@[simp] theorem mkCaseCMainPackage_residual
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (mkCaseCMainPackage P D NI KG G R C hI).residual = R := rfl

@[simp] theorem mkCaseCMainPackage_certificate
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (mkCaseCMainPackage P D NI KG G R C hI).certificate = C := rfl

@[simp] theorem mkCaseCMainPackage_impossible
    (P : Params) (D : ClosureData P)
    (NI : GapClosure.NonIntegralityFamilyPackage P D)
    (KG : GapClosure.KmaxGapPackage P D)
    (G : GapClosure.GapClosurePackage P D)
    (R : StateMachine.ResidualClosurePackage P D)
    (C : Certificate.CertificateMainPackage)
    (hI : CaseCImpossible) :
    (mkCaseCMainPackage P D NI KG G R C hI).impossible = hI := rfl

theorem caseC_impossible_from_package
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) (hC : InCaseC n) :
    False := by
  exact CaseCMainPackage.impossible_pointwise P D X hL hC

theorem not_inCaseC_of_LehmerComposite_from_package
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  exact CaseCMainPackage.not_inCaseC_of_LehmerComposite P D X hL

theorem caseC_impossible
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) (hC : InCaseC n) :
    False := by
  exact caseC_impossible_from_package P D X hL hC

theorem not_inCaseC_of_LehmerComposite
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  exact not_inCaseC_of_LehmerComposite_from_package P D X hL

end CaseC
end Lehmer