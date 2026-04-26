-- FILE: Lean/Lehmer/Audit/CaseC/Exhaustivity.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.CaseC.Spec : def
- Lehmer.Audit.CaseC.Params : def thm
- Lehmer.Audit.CaseC.ClosureData : def thm
- Lehmer.Audit.CaseC.NonIntegrality : def thm
- Lehmer.Audit.CaseC.KmaxGap : def thm
- Lehmer.Audit.CaseC.GapClosure : def thm
- Lehmer.Audit.CaseC.ResidualClosure : def thm
- Lehmer.Audit.CaseC.Certificate : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit
import Lehmer.CaseC.Spec
import Lehmer.Audit.CaseC.Params
import Lehmer.Audit.CaseC.ClosureData
import Lehmer.Audit.CaseC.NonIntegrality
import Lehmer.Audit.CaseC.KmaxGap
import Lehmer.Audit.CaseC.GapClosure
import Lehmer.Audit.CaseC.ResidualClosure
import Lehmer.Audit.CaseC.Certificate

namespace Lehmer
namespace Audit
namespace CaseC

def CaseCAuditCandidate (n : ℕ) : Prop :=
  Lehmer.Basic.LehmerComposite n

@[simp] theorem CaseCAuditCandidate_def (n : ℕ) :
    CaseCAuditCandidate n = Lehmer.Basic.LehmerComposite n := rfl

def CaseCAuditClass (n : ℕ) : Prop :=
  Lehmer.Pipeline.InCaseC n

@[simp] theorem CaseCAuditClass_def (n : ℕ) :
    CaseCAuditClass n = Lehmer.Pipeline.InCaseC n := rfl

def CaseCGapClosureAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty
    (Lehmer.CaseC.GapClosure.GapToClosurePackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

theorem caseCGapClosureAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCGapClosureAuditAvailable hC := by
  exact ⟨auditCaseCGapToClosureOf hC⟩

structure CaseCExhaustivityData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  paramsData : Lehmer.Audit.CaseC.AuditCaseCParamsData n
  closureData : Lehmer.Audit.CaseC.AuditCaseCClosureData n
  nonIntegralityAvailable :
    Lehmer.Audit.CaseC.CaseCNonIntegralityAuditAvailable inCaseC
  kmaxGapAvailable :
    Lehmer.Audit.CaseC.CaseCKmaxGapAuditAvailable inCaseC
  gapClosureAvailable :
    Lehmer.Audit.CaseC.CaseCGapClosureAuditAvailable inCaseC
  residualAvailable :
    Lehmer.Audit.CaseC.CaseCResidualAuditAvailable inCaseC
  certificateAvailable :
    Lehmer.Audit.CaseC.CaseCCertificateAuditAvailable inCaseC
  level_eq_pivot :
    closureData.level = Lehmer.Pipeline.pivotOf n
  width_eq_pivot :
    closureData.width = Lehmer.Pipeline.pivotOf n
  cap_eq_pivot :
    closureData.cap = Lehmer.Pipeline.pivotOf n
  omegaBound_eq_pivot :
    closureData.omegaBound = Lehmer.Pipeline.pivotOf n

def caseCExhaustivityDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCExhaustivityData n :=
  {
    inCaseC := hC
    paramsData := auditCaseCParamsDataOf hC
    closureData := auditCaseCClosureDataDataOf hC
    nonIntegralityAvailable := caseCNonIntegralityAuditAvailable hC
    kmaxGapAvailable := caseCKmaxGapAuditAvailable hC
    gapClosureAvailable := caseCGapClosureAuditAvailable hC
    residualAvailable := caseCResidualAuditAvailable hC
    certificateAvailable := caseCCertificateAuditAvailable hC
    level_eq_pivot := by rfl
    width_eq_pivot := by rfl
    cap_eq_pivot := by rfl
    omegaBound_eq_pivot := by rfl
  }

@[simp] theorem caseCExhaustivityDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).inCaseC = hC := rfl

@[simp] theorem caseCExhaustivityDataOf_paramsData
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).paramsData = auditCaseCParamsDataOf hC := rfl

@[simp] theorem caseCExhaustivityDataOf_closureData
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).closureData = auditCaseCClosureDataDataOf hC := rfl

@[simp] theorem caseCExhaustivityDataOf_nonIntegralityAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).nonIntegralityAvailable =
      caseCNonIntegralityAuditAvailable hC := rfl

@[simp] theorem caseCExhaustivityDataOf_kmaxGapAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).kmaxGapAvailable =
      caseCKmaxGapAuditAvailable hC := rfl

@[simp] theorem caseCExhaustivityDataOf_gapClosureAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).gapClosureAvailable =
      caseCGapClosureAuditAvailable hC := rfl

@[simp] theorem caseCExhaustivityDataOf_residualAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).residualAvailable =
      caseCResidualAuditAvailable hC := rfl

@[simp] theorem caseCExhaustivityDataOf_certificateAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCExhaustivityDataOf hC).certificateAvailable =
      caseCCertificateAuditAvailable hC := rfl

def CaseCStructuralExhaustivity : Prop :=
  ∀ n : ℕ,
    Lehmer.Pipeline.InCaseC n →
      ∃ X : CaseCExhaustivityData n, True

@[simp] theorem CaseCStructuralExhaustivity_def :
    CaseCStructuralExhaustivity =
      (∀ n : ℕ,
        Lehmer.Pipeline.InCaseC n →
          ∃ X : CaseCExhaustivityData n, True) := rfl

theorem caseC_structural_exhaustivity :
    CaseCStructuralExhaustivity := by
  intro n hC
  exact ⟨caseCExhaustivityDataOf hC, trivial⟩

def CaseCAuditStructuralExhaustivity : Prop :=
  ∀ n : ℕ,
    CaseCAuditCandidate n →
    CaseCAuditClass n →
      ∃ X : CaseCExhaustivityData n, True

@[simp] theorem CaseCAuditStructuralExhaustivity_def :
    CaseCAuditStructuralExhaustivity =
      (∀ n : ℕ,
        CaseCAuditCandidate n →
        CaseCAuditClass n →
          ∃ X : CaseCExhaustivityData n, True) := rfl

theorem caseC_audit_structural_exhaustivity :
    CaseCAuditStructuralExhaustivity := by
  intro n _hCand hC
  exact ⟨caseCExhaustivityDataOf hC, trivial⟩

theorem exists_caseCExhaustivityData_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ X : CaseCExhaustivityData n, True := by
  exact ⟨caseCExhaustivityDataOf hC, trivial⟩

theorem exists_caseCExhaustivityData_of_auditClass
    {n : ℕ} (hC : CaseCAuditClass n) :
    ∃ X : CaseCExhaustivityData n, True := by
  exact exists_caseCExhaustivityData_of_inCaseC hC

theorem CaseCExhaustivityData.nonIntegrality_available
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Audit.CaseC.CaseCNonIntegralityAuditAvailable X.inCaseC := by
  exact X.nonIntegralityAvailable

theorem CaseCExhaustivityData.kmaxGap_available
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Audit.CaseC.CaseCKmaxGapAuditAvailable X.inCaseC := by
  exact X.kmaxGapAvailable

theorem CaseCExhaustivityData.gapClosure_available
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Audit.CaseC.CaseCGapClosureAuditAvailable X.inCaseC := by
  exact X.gapClosureAvailable

theorem CaseCExhaustivityData.residual_available
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Audit.CaseC.CaseCResidualAuditAvailable X.inCaseC := by
  exact X.residualAvailable

theorem CaseCExhaustivityData.certificate_available
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Audit.CaseC.CaseCCertificateAuditAvailable X.inCaseC := by
  exact X.certificateAvailable

theorem CaseCExhaustivityData.level_eq_pivot'
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.level = Lehmer.Pipeline.pivotOf n := by
  exact X.level_eq_pivot

theorem CaseCExhaustivityData.width_eq_pivot'
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.width = Lehmer.Pipeline.pivotOf n := by
  exact X.width_eq_pivot

theorem CaseCExhaustivityData.cap_eq_pivot'
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.cap = Lehmer.Pipeline.pivotOf n := by
  exact X.cap_eq_pivot

theorem CaseCExhaustivityData.omegaBound_eq_pivot'
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.omegaBound = Lehmer.Pipeline.pivotOf n := by
  exact X.omegaBound_eq_pivot

theorem CaseCExhaustivityData.level_ge_YA
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Pipeline.YA ≤ X.closureData.level := by
  rw [X.level_eq_pivot]
  exact X.inCaseC.1

theorem CaseCExhaustivityData.width_ge_YA
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Pipeline.YA ≤ X.closureData.width := by
  rw [X.width_eq_pivot]
  exact X.inCaseC.1

theorem CaseCExhaustivityData.cap_ge_YA
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Pipeline.YA ≤ X.closureData.cap := by
  rw [X.cap_eq_pivot]
  exact X.inCaseC.1

theorem CaseCExhaustivityData.omegaBound_ge_YA
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Pipeline.YA ≤ X.closureData.omegaBound := by
  rw [X.omegaBound_eq_pivot]
  exact X.inCaseC.1

theorem CaseCExhaustivityData.level_lt_YC
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.level < Lehmer.Pipeline.YC := by
  rw [X.level_eq_pivot]
  exact X.inCaseC.2

theorem CaseCExhaustivityData.width_lt_YC
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.width < Lehmer.Pipeline.YC := by
  rw [X.width_eq_pivot]
  exact X.inCaseC.2

theorem CaseCExhaustivityData.cap_lt_YC
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.cap < Lehmer.Pipeline.YC := by
  rw [X.cap_eq_pivot]
  exact X.inCaseC.2

theorem CaseCExhaustivityData.omegaBound_lt_YC
    {n : ℕ} (X : CaseCExhaustivityData n) :
    X.closureData.omegaBound < Lehmer.Pipeline.YC := by
  rw [X.omegaBound_eq_pivot]
  exact X.inCaseC.2

theorem caseCExhaustivityData_sound
    {n : ℕ} (X : CaseCExhaustivityData n) :
    Lehmer.Pipeline.InCaseC n := by
  exact X.inCaseC

theorem caseCExhaustivityData_reconstructs
    {n : ℕ} (X : CaseCExhaustivityData n) :
    CaseCAuditClass n := by
  exact X.inCaseC

structure AuditCaseCClosureInput (n : ℕ) where
  candidate : Lehmer.Basic.LehmerComposite n
  inCaseC : Lehmer.Pipeline.InCaseC n
  paramsData : Lehmer.Audit.CaseC.AuditCaseCParamsData n
  closureData : Lehmer.Audit.CaseC.AuditCaseCClosureData n
  nonIntegrality :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (auditCaseCParamsOf inCaseC)
      (auditCaseCClosureDataOf inCaseC)
  kmaxGap :
    Lehmer.CaseC.GapClosure.KmaxGapPackage
      (auditCaseCParamsOf inCaseC)
      (auditCaseCClosureDataOf inCaseC)
  gapToClosure :
    Lehmer.CaseC.GapClosure.GapToClosurePackage
      (auditCaseCParamsOf inCaseC)
      (auditCaseCClosureDataOf inCaseC)
  residual :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (auditCaseCParamsOf inCaseC)
      (auditCaseCClosureDataOf inCaseC)
  certificate :
    Lehmer.CaseC.Certificate.CertificateMainPackage
  level_eq_pivot :
    closureData.level = Lehmer.Pipeline.pivotOf n
  width_eq_pivot :
    closureData.width = Lehmer.Pipeline.pivotOf n
  cap_eq_pivot :
    closureData.cap = Lehmer.Pipeline.pivotOf n
  omegaBound_eq_pivot :
    closureData.omegaBound = Lehmer.Pipeline.pivotOf n

def auditCaseCClosureInputOf
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCClosureInput n :=
  {
    candidate := hCand
    inCaseC := hC
    paramsData := auditCaseCParamsDataOf hC
    closureData := auditCaseCClosureDataDataOf hC
    nonIntegrality := auditCaseCNonIntegralityOf hC
    kmaxGap := auditCaseCKmaxGapOf hC
    gapToClosure := auditCaseCGapToClosureOf hC
    residual := auditCaseCResidualClosureOfInCaseC hC
    certificate := auditCaseCCertificateMainPackageOf hC
    level_eq_pivot := by rfl
    width_eq_pivot := by rfl
    cap_eq_pivot := by rfl
    omegaBound_eq_pivot := by rfl
  }

@[simp] theorem auditCaseCClosureInputOf_candidate
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).candidate = hCand := rfl

@[simp] theorem auditCaseCClosureInputOf_inCaseC
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCClosureInputOf_paramsData
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).paramsData =
      auditCaseCParamsDataOf hC := rfl

@[simp] theorem auditCaseCClosureInputOf_closureData
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).closureData =
      auditCaseCClosureDataDataOf hC := rfl

@[simp] theorem auditCaseCClosureInputOf_nonIntegrality
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).nonIntegrality =
      auditCaseCNonIntegralityOf hC := rfl

@[simp] theorem auditCaseCClosureInputOf_kmaxGap
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).kmaxGap =
      auditCaseCKmaxGapOf hC := rfl

@[simp] theorem auditCaseCClosureInputOf_gapToClosure
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).gapToClosure =
      auditCaseCGapToClosureOf hC := rfl

@[simp] theorem auditCaseCClosureInputOf_residual
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).residual =
      auditCaseCResidualClosureOfInCaseC hC := rfl

@[simp] theorem auditCaseCClosureInputOf_certificate
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).certificate =
      auditCaseCCertificateMainPackageOf hC := rfl

theorem AuditCaseCClosureInput.in_caseC
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.Pipeline.InCaseC n := by
  exact I.inCaseC

theorem AuditCaseCClosureInput.is_candidate
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.Basic.LehmerComposite n := by
  exact I.candidate

theorem AuditCaseCClosureInput.residual_closed
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.residual.state := by
  exact I.residual.closed

theorem AuditCaseCClosureInput.certificate_checked
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      I.certificate.certificate := by
  exact I.certificate.checked

theorem AuditCaseCClosureInput.certificate_sound
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      I.certificate.certificate := by
  exact I.certificate.sound

theorem AuditCaseCClosureInput.certificate_complete
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      I.certificate.certificate := by
  exact I.certificate.complete

theorem AuditCaseCClosureInput.level_eq_pivot'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.level = Lehmer.Pipeline.pivotOf n := by
  exact I.level_eq_pivot

theorem AuditCaseCClosureInput.width_eq_pivot'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.width = Lehmer.Pipeline.pivotOf n := by
  exact I.width_eq_pivot

theorem AuditCaseCClosureInput.cap_eq_pivot'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.cap = Lehmer.Pipeline.pivotOf n := by
  exact I.cap_eq_pivot

theorem AuditCaseCClosureInput.omegaBound_eq_pivot'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.omegaBound = Lehmer.Pipeline.pivotOf n := by
  exact I.omegaBound_eq_pivot

def CaseCClosureInputExhaustivity : Prop :=
  ∀ n : ℕ,
    CaseCAuditCandidate n →
    CaseCAuditClass n →
      ∃ I : AuditCaseCClosureInput n, True

@[simp] theorem CaseCClosureInputExhaustivity_def :
    CaseCClosureInputExhaustivity =
      (∀ n : ℕ,
        CaseCAuditCandidate n →
        CaseCAuditClass n →
          ∃ I : AuditCaseCClosureInput n, True) := rfl

theorem caseC_closure_input_exhaustivity :
    CaseCClosureInputExhaustivity := by
  intro n hCand hC
  exact ⟨auditCaseCClosureInputOf hCand hC, trivial⟩

theorem exists_auditCaseCClosureInput
    {n : ℕ}
    (hCand : CaseCAuditCandidate n)
    (hC : CaseCAuditClass n) :
    ∃ I : AuditCaseCClosureInput n, True := by
  exact ⟨auditCaseCClosureInputOf hCand hC, trivial⟩

end CaseC
end Audit
end Lehmer