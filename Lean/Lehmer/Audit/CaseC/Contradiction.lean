-- FILE: Lean/Lehmer/Audit/CaseC/Contradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.CaseC.Spec : def
- Lehmer.Audit.CaseC.Exhaustivity : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit
import Lehmer.CaseC.Spec
import Lehmer.Audit.CaseC.Exhaustivity
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.KmaxGap
import Lehmer.CaseC.GapClosure.GapToClosure
import Lehmer.CaseC.StateMachine.ResidualClosure
import Lehmer.CaseC.Certificate.Main

namespace Lehmer
namespace Audit
namespace CaseC

structure AuditCaseCTerminalInput (n : ℕ) where
  closureInput : AuditCaseCClosureInput n

def auditCaseCTerminalInputOf
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    AuditCaseCTerminalInput n :=
  { closureInput := I }

@[simp] theorem auditCaseCTerminalInputOf_closureInput
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalInputOf I).closureInput = I := rfl

@[simp] theorem auditCaseCTerminalInputOf_candidate
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalInputOf I).closureInput.candidate = I.candidate := rfl

@[simp] theorem auditCaseCTerminalInputOf_inCaseC
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalInputOf I).closureInput.inCaseC = I.inCaseC := rfl

theorem AuditCaseCTerminalInput.candidate
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.Basic.LehmerComposite n := by
  exact T.closureInput.candidate

theorem AuditCaseCTerminalInput.inCaseC
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.Pipeline.InCaseC n := by
  exact T.closureInput.inCaseC

def AuditCaseCTerminalInput.paramsData
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.Audit.CaseC.AuditCaseCParamsData n :=
  T.closureInput.paramsData

@[simp] theorem AuditCaseCTerminalInput.paramsData_def
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    T.paramsData = T.closureInput.paramsData := rfl

def AuditCaseCTerminalInput.closureData
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.Audit.CaseC.AuditCaseCClosureData n :=
  T.closureInput.closureData

@[simp] theorem AuditCaseCTerminalInput.closureData_def
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    T.closureData = T.closureInput.closureData := rfl

def AuditCaseCTerminalInput.nonIntegrality
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (auditCaseCParamsOf T.closureInput.inCaseC)
      (auditCaseCClosureDataOf T.closureInput.inCaseC) :=
  T.closureInput.nonIntegrality

@[simp] theorem AuditCaseCTerminalInput.nonIntegrality_def
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    T.nonIntegrality = T.closureInput.nonIntegrality := rfl

def AuditCaseCTerminalInput.kmaxGap
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.CaseC.GapClosure.KmaxGapPackage
      (auditCaseCParamsOf T.closureInput.inCaseC)
      (auditCaseCClosureDataOf T.closureInput.inCaseC) :=
  T.closureInput.kmaxGap

@[simp] theorem AuditCaseCTerminalInput.kmaxGap_def
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    T.kmaxGap = T.closureInput.kmaxGap := rfl

def AuditCaseCTerminalInput.gapToClosure
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.CaseC.GapClosure.GapToClosurePackage
      (auditCaseCParamsOf T.closureInput.inCaseC)
      (auditCaseCClosureDataOf T.closureInput.inCaseC) :=
  T.closureInput.gapToClosure

@[simp] theorem AuditCaseCTerminalInput.gapToClosure_def
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    T.gapToClosure = T.closureInput.gapToClosure := rfl

def AuditCaseCTerminalInput.residual
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (auditCaseCParamsOf T.closureInput.inCaseC)
      (auditCaseCClosureDataOf T.closureInput.inCaseC) :=
  T.closureInput.residual

@[simp] theorem AuditCaseCTerminalInput.residual_def
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    T.residual = T.closureInput.residual := rfl

def AuditCaseCTerminalInput.certificate
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    Lehmer.CaseC.Certificate.CertificateMainPackage :=
  T.closureInput.certificate

@[simp] theorem AuditCaseCTerminalInput.certificate_def
    {n : ℕ} (T : AuditCaseCTerminalInput n) :
    T.certificate = T.closureInput.certificate := rfl

theorem AuditCaseCClosureInput.candidate_is_LehmerComposite
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.Basic.LehmerComposite n := by
  exact I.candidate

theorem AuditCaseCClosureInput.in_caseC
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.Pipeline.InCaseC n := by
  exact I.inCaseC

theorem AuditCaseCClosureInput.pivot_ge_YA
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.Pipeline.YA ≤ Lehmer.Pipeline.pivotOf n := by
  exact I.inCaseC.1

theorem AuditCaseCClosureInput.pivot_lt_YC
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.Pipeline.pivotOf n < Lehmer.Pipeline.YC := by
  exact I.inCaseC.2

theorem AuditCaseCClosureInput.level_eq_pivot_core
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.level = Lehmer.Pipeline.pivotOf n := by
  exact I.level_eq_pivot

theorem AuditCaseCClosureInput.width_eq_pivot_core
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.width = Lehmer.Pipeline.pivotOf n := by
  exact I.width_eq_pivot

theorem AuditCaseCClosureInput.cap_eq_pivot_core
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.cap = Lehmer.Pipeline.pivotOf n := by
  exact I.cap_eq_pivot

theorem AuditCaseCClosureInput.omegaBound_eq_pivot_core
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.closureData.omegaBound = Lehmer.Pipeline.pivotOf n := by
  exact I.omegaBound_eq_pivot

theorem AuditCaseCClosureInput.kmaxGap_gap_pos
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    0 < Lehmer.CaseC.GapClosure.kmaxGapValue
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGapValue_pos
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.kmaxGap

theorem AuditCaseCClosureInput.kmaxGap_kmax_pos
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    0 < Lehmer.CaseC.GapClosure.kmaxGapKmaxValue
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGapKmaxValue_pos
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.kmaxGap

theorem AuditCaseCClosureInput.kmaxGap_closureCap_pos
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    0 < Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue_pos
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.kmaxGap

theorem AuditCaseCClosureInput.kmaxGap_family_mem_hasWitness
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    ∀ R,
      R ∈ Lehmer.CaseC.GapClosure.kmaxGapFamily
        (auditCaseCParamsOf I.inCaseC)
        (auditCaseCClosureDataOf I.inCaseC)
        I.kmaxGap →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness
        (auditCaseCParamsOf I.inCaseC)
        (auditCaseCClosureDataOf I.inCaseC)
        R := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_hasWitness
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.kmaxGap R hR

theorem AuditCaseCClosureInput.kmaxGap_family_mem_rigid
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    ∀ R,
      R ∈ Lehmer.CaseC.GapClosure.kmaxGapFamily
        (auditCaseCParamsOf I.inCaseC)
        (auditCaseCClosureDataOf I.inCaseC)
        I.kmaxGap →
      Lehmer.CaseC.GapClosure.RigidProfile
        (auditCaseCParamsOf I.inCaseC)
        (auditCaseCClosureDataOf I.inCaseC)
        R := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_rigid
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.kmaxGap R hR

@[simp] theorem auditCaseCClosureInputOf_gapToClosure_kmaxGap
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).gapToClosure.kmaxGap =
      auditCaseCKmaxGapOf hC := rfl

@[simp] theorem auditCaseCClosureInputOf_gapToClosure_gap
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureInputOf hCand hC).gapToClosure.gap =
      auditCaseCGapClosureOf hC := rfl

theorem AuditCaseCClosureInput.gapToClosure_gap_bootstrap_holds
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.GapClosure.BootstrapCondition
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.gapToClosure.gap.data.data.data := by
  exact Lehmer.CaseC.GapClosure.GapClosurePackage.bootstrap_holds
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.gapToClosure.gap

theorem AuditCaseCClosureInput.gapToClosure_omegahat_below_width
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.GapClosure.OmegahatBelowWidth
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.gapToClosure.gap.data.data.data.omegaHat := by
  exact Lehmer.CaseC.GapClosure.GapClosurePackage.omegahat_below_width
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.gapToClosure.gap

theorem AuditCaseCClosureInput.residual_closed'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.residual.state := by
  exact I.residual.closed

def AuditCaseCClosureInput.residualRouting
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC) :=
  Lehmer.CaseC.StateMachine.residualClosureRoutingOfState
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.residual.state

@[simp] theorem AuditCaseCClosureInput.residualRouting_state
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.state
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.residualRouting =
        I.residual.state := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_state
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.residual.state

@[simp] theorem AuditCaseCClosureInput.residualRouting_family
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.residualRouting =
        Lehmer.CaseC.StateMachine.residualFamily
          (auditCaseCParamsOf I.inCaseC)
          (auditCaseCClosureDataOf I.inCaseC)
          I.residual.state := by
  exact Lehmer.CaseC.StateMachine.residualClosureRoutingOfState_family
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.residual.state

def AuditCaseCClosureInput.residualFamily
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.ResidualFamily :=
  Lehmer.CaseC.StateMachine.residualFamily
    (auditCaseCParamsOf I.inCaseC)
    (auditCaseCClosureDataOf I.inCaseC)
    I.residual.state

@[simp] theorem AuditCaseCClosureInput.residualFamily_def
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    I.residualFamily =
      Lehmer.CaseC.StateMachine.residualFamily
        (auditCaseCParamsOf I.inCaseC)
        (auditCaseCClosureDataOf I.inCaseC)
        I.residual.state := rfl

theorem AuditCaseCClosureInput.residualFamily_eq_routingFamily
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.StateMachine.ResidualClosureRouting.family
      (auditCaseCParamsOf I.inCaseC)
      (auditCaseCClosureDataOf I.inCaseC)
      I.residualRouting =
        I.residualFamily := by
  rw [AuditCaseCClosureInput.residualRouting_family]
  rfl

theorem AuditCaseCClosureInput.certificate_checked'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      I.certificate.certificate := by
  exact I.certificate.checked

theorem AuditCaseCClosureInput.certificate_sound'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      I.certificate.certificate := by
  exact I.certificate.sound

theorem AuditCaseCClosureInput.certificate_complete'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      I.certificate.certificate := by
  exact I.certificate.complete

theorem AuditCaseCClosureInput.certificate_coverageReady'
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      I.certificate.certificate := by
  exact I.certificate.coverageReady

structure AuditCaseCTerminalCertificate (n : ℕ) where
  input : AuditCaseCClosureInput n
  candidate : Lehmer.Basic.LehmerComposite n
  inCaseC : Lehmer.Pipeline.InCaseC n
  residualClosed :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf input.inCaseC)
      (auditCaseCClosureDataOf input.inCaseC)
      input.residual.state
  certificateChecked :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      input.certificate.certificate
  certificateSound :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      input.certificate.certificate
  certificateComplete :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      input.certificate.certificate
  certificateCoverageReady :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      input.certificate.certificate

def auditCaseCTerminalCertificateOf
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    AuditCaseCTerminalCertificate n :=
  {
    input := I
    candidate := I.candidate
    inCaseC := I.inCaseC
    residualClosed := I.residual.closed
    certificateChecked := I.certificate.checked
    certificateSound := I.certificate.sound
    certificateComplete := I.certificate.complete
    certificateCoverageReady := I.certificate.coverageReady
  }

@[simp] theorem auditCaseCTerminalCertificateOf_input
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalCertificateOf I).input = I := rfl

@[simp] theorem auditCaseCTerminalCertificateOf_candidate
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalCertificateOf I).candidate = I.candidate := rfl

@[simp] theorem auditCaseCTerminalCertificateOf_inCaseC
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalCertificateOf I).inCaseC = I.inCaseC := rfl

theorem AuditCaseCTerminalCertificate.residual_closed
    {n : ℕ} (T : AuditCaseCTerminalCertificate n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf T.input.inCaseC)
      (auditCaseCClosureDataOf T.input.inCaseC)
      T.input.residual.state := by
  exact T.residualClosed

theorem AuditCaseCTerminalCertificate.certificate_checked
    {n : ℕ} (T : AuditCaseCTerminalCertificate n) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      T.input.certificate.certificate := by
  exact T.certificateChecked

theorem AuditCaseCTerminalCertificate.certificate_sound
    {n : ℕ} (T : AuditCaseCTerminalCertificate n) :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      T.input.certificate.certificate := by
  exact T.certificateSound

theorem AuditCaseCTerminalCertificate.certificate_complete
    {n : ℕ} (T : AuditCaseCTerminalCertificate n) :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      T.input.certificate.certificate := by
  exact T.certificateComplete

theorem AuditCaseCTerminalCertificate.certificate_coverageReady
    {n : ℕ} (T : AuditCaseCTerminalCertificate n) :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      T.input.certificate.certificate := by
  exact T.certificateCoverageReady

structure AuditCaseCTerminalClosure (n : ℕ) where
  input : AuditCaseCClosureInput n
  terminalCertificate : AuditCaseCTerminalCertificate n
  gapBootstrap :
    Lehmer.CaseC.GapClosure.BootstrapCondition
      (auditCaseCParamsOf input.inCaseC)
      (auditCaseCClosureDataOf input.inCaseC)
      input.gapToClosure.gap.data.data.data
  gapOmega :
    Lehmer.CaseC.GapClosure.OmegahatBelowWidth
      (auditCaseCParamsOf input.inCaseC)
      (auditCaseCClosureDataOf input.inCaseC)
      input.gapToClosure.gap.data.data.data.omegaHat
  residualClosed :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf input.inCaseC)
      (auditCaseCClosureDataOf input.inCaseC)
      input.residual.state
  certificateReady :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      input.certificate.certificate

def auditCaseCTerminalClosureOf
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    AuditCaseCTerminalClosure n :=
  {
    input := I
    terminalCertificate := auditCaseCTerminalCertificateOf I
    gapBootstrap := I.gapToClosure_gap_bootstrap_holds
    gapOmega := I.gapToClosure_omegahat_below_width
    residualClosed := I.residual.closed
    certificateReady := I.certificate.coverageReady
  }

@[simp] theorem auditCaseCTerminalClosureOf_input
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalClosureOf I).input = I := rfl

@[simp] theorem auditCaseCTerminalClosureOf_terminalCertificate
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    (auditCaseCTerminalClosureOf I).terminalCertificate =
      auditCaseCTerminalCertificateOf I := rfl

theorem AuditCaseCTerminalClosure.candidate
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.Basic.LehmerComposite n := by
  exact T.input.candidate

theorem AuditCaseCTerminalClosure.inCaseC
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.Pipeline.InCaseC n := by
  exact T.input.inCaseC

theorem AuditCaseCTerminalClosure.level_eq_pivot
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    T.input.closureData.level = Lehmer.Pipeline.pivotOf n := by
  exact T.input.level_eq_pivot

theorem AuditCaseCTerminalClosure.width_eq_pivot
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    T.input.closureData.width = Lehmer.Pipeline.pivotOf n := by
  exact T.input.width_eq_pivot

theorem AuditCaseCTerminalClosure.cap_eq_pivot
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    T.input.closureData.cap = Lehmer.Pipeline.pivotOf n := by
  exact T.input.cap_eq_pivot

theorem AuditCaseCTerminalClosure.omegaBound_eq_pivot
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    T.input.closureData.omegaBound = Lehmer.Pipeline.pivotOf n := by
  exact T.input.omegaBound_eq_pivot

theorem AuditCaseCTerminalClosure.pivot_ge_YA
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.Pipeline.YA ≤ Lehmer.Pipeline.pivotOf n := by
  exact T.input.inCaseC.1

theorem AuditCaseCTerminalClosure.pivot_lt_YC
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.Pipeline.pivotOf n < Lehmer.Pipeline.YC := by
  exact T.input.inCaseC.2

theorem AuditCaseCTerminalClosure.gap_bootstrap
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.CaseC.GapClosure.BootstrapCondition
      (auditCaseCParamsOf T.input.inCaseC)
      (auditCaseCClosureDataOf T.input.inCaseC)
      T.input.gapToClosure.gap.data.data.data := by
  exact T.gapBootstrap

theorem AuditCaseCTerminalClosure.gap_omega
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.CaseC.GapClosure.OmegahatBelowWidth
      (auditCaseCParamsOf T.input.inCaseC)
      (auditCaseCClosureDataOf T.input.inCaseC)
      T.input.gapToClosure.gap.data.data.data.omegaHat := by
  exact T.gapOmega

theorem AuditCaseCTerminalClosure.residual_closed
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf T.input.inCaseC)
      (auditCaseCClosureDataOf T.input.inCaseC)
      T.input.residual.state := by
  exact T.residualClosed

theorem AuditCaseCTerminalClosure.certificate_ready
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      T.input.certificate.certificate := by
  exact T.certificateReady

structure AuditCaseCTerminalObstruction (n : ℕ) where
  terminal : AuditCaseCTerminalClosure n
  candidate : Lehmer.Basic.LehmerComposite n
  inCaseC : Lehmer.Pipeline.InCaseC n
  gapBootstrap :
    Lehmer.CaseC.GapClosure.BootstrapCondition
      (auditCaseCParamsOf terminal.input.inCaseC)
      (auditCaseCClosureDataOf terminal.input.inCaseC)
      terminal.input.gapToClosure.gap.data.data.data
  gapOmega :
    Lehmer.CaseC.GapClosure.OmegahatBelowWidth
      (auditCaseCParamsOf terminal.input.inCaseC)
      (auditCaseCClosureDataOf terminal.input.inCaseC)
      terminal.input.gapToClosure.gap.data.data.data.omegaHat
  residualClosed :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf terminal.input.inCaseC)
      (auditCaseCClosureDataOf terminal.input.inCaseC)
      terminal.input.residual.state
  certificateChecked :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      terminal.input.certificate.certificate
  certificateSound :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      terminal.input.certificate.certificate
  certificateComplete :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      terminal.input.certificate.certificate
  certificateReady :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      terminal.input.certificate.certificate

def auditCaseCTerminalObstructionOf
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    AuditCaseCTerminalObstruction n :=
  {
    terminal := T
    candidate := T.input.candidate
    inCaseC := T.input.inCaseC
    gapBootstrap := T.gapBootstrap
    gapOmega := T.gapOmega
    residualClosed := T.residualClosed
    certificateChecked := T.input.certificate.checked
    certificateSound := T.input.certificate.sound
    certificateComplete := T.input.certificate.complete
    certificateReady := T.certificateReady
  }

@[simp] theorem auditCaseCTerminalObstructionOf_terminal
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    (auditCaseCTerminalObstructionOf T).terminal = T := rfl

@[simp] theorem auditCaseCTerminalObstructionOf_candidate
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    (auditCaseCTerminalObstructionOf T).candidate = T.input.candidate := rfl

@[simp] theorem auditCaseCTerminalObstructionOf_inCaseC
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    (auditCaseCTerminalObstructionOf T).inCaseC = T.input.inCaseC := rfl

theorem AuditCaseCTerminalObstruction.gap_bootstrap
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.CaseC.GapClosure.BootstrapCondition
      (auditCaseCParamsOf O.terminal.input.inCaseC)
      (auditCaseCClosureDataOf O.terminal.input.inCaseC)
      O.terminal.input.gapToClosure.gap.data.data.data := by
  exact O.gapBootstrap

theorem AuditCaseCTerminalObstruction.gap_omega
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.CaseC.GapClosure.OmegahatBelowWidth
      (auditCaseCParamsOf O.terminal.input.inCaseC)
      (auditCaseCClosureDataOf O.terminal.input.inCaseC)
      O.terminal.input.gapToClosure.gap.data.data.data.omegaHat := by
  exact O.gapOmega

theorem AuditCaseCTerminalObstruction.residual_closed
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (auditCaseCParamsOf O.terminal.input.inCaseC)
      (auditCaseCClosureDataOf O.terminal.input.inCaseC)
      O.terminal.input.residual.state := by
  exact O.residualClosed

theorem AuditCaseCTerminalObstruction.certificate_checked
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.CaseC.Certificate.CertificateMainChecked
      O.terminal.input.certificate.certificate := by
  exact O.certificateChecked

theorem AuditCaseCTerminalObstruction.certificate_sound
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.CaseC.Certificate.GloballySoundCertificate
      O.terminal.input.certificate.certificate := by
  exact O.certificateSound

theorem AuditCaseCTerminalObstruction.certificate_complete
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.CaseC.Certificate.GloballyCompleteCertificate
      O.terminal.input.certificate.certificate := by
  exact O.certificateComplete

theorem AuditCaseCTerminalObstruction.certificate_ready
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.CaseC.Certificate.CoverageReadyCertificate
      O.terminal.input.certificate.certificate := by
  exact O.certificateReady

theorem AuditCaseCTerminalObstruction.level_eq_pivot
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    O.terminal.input.closureData.level = Lehmer.Pipeline.pivotOf n := by
  exact O.terminal.input.level_eq_pivot

theorem AuditCaseCTerminalObstruction.width_eq_pivot
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    O.terminal.input.closureData.width = Lehmer.Pipeline.pivotOf n := by
  exact O.terminal.input.width_eq_pivot

theorem AuditCaseCTerminalObstruction.cap_eq_pivot
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    O.terminal.input.closureData.cap = Lehmer.Pipeline.pivotOf n := by
  exact O.terminal.input.cap_eq_pivot

theorem AuditCaseCTerminalObstruction.omegaBound_eq_pivot
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    O.terminal.input.closureData.omegaBound = Lehmer.Pipeline.pivotOf n := by
  exact O.terminal.input.omegaBound_eq_pivot

theorem AuditCaseCTerminalObstruction.pivot_ge_YA
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.Pipeline.YA ≤ Lehmer.Pipeline.pivotOf n := by
  exact O.inCaseC.1

theorem AuditCaseCTerminalObstruction.pivot_lt_YC
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    Lehmer.Pipeline.pivotOf n < Lehmer.Pipeline.YC := by
  exact O.inCaseC.2

theorem auditCaseC_terminal_contradiction
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    False := by
  have hCand : Lehmer.Basic.LehmerComposite n := O.candidate
  have hC : Lehmer.Pipeline.InCaseC n := O.inCaseC

  have hLevel :
      O.terminal.input.closureData.level = Lehmer.Pipeline.pivotOf n :=
    O.terminal.input.level_eq_pivot

  have hWidth :
      O.terminal.input.closureData.width = Lehmer.Pipeline.pivotOf n :=
    O.terminal.input.width_eq_pivot

  have hCap :
      O.terminal.input.closureData.cap = Lehmer.Pipeline.pivotOf n :=
    O.terminal.input.cap_eq_pivot

  have hOmega :
      O.terminal.input.closureData.omegaBound = Lehmer.Pipeline.pivotOf n :=
    O.terminal.input.omegaBound_eq_pivot

  have hGapBootstrap := O.gapBootstrap
  have hGapOmega := O.gapOmega
  have hResidualClosed := O.residualClosed
  have hCertificateChecked := O.certificateChecked
  have hCertificateSound := O.certificateSound
  have hCertificateComplete := O.certificateComplete
  have hCertificateReady := O.certificateReady

  -- Extract the coverage theorem from the certificate readiness
  -- The signature of CoverageReadyCertificate is exactly:
  -- ∀ (n : ℕ) (hL : LehmerComposite n) (hC : InCaseC n),
  --   (GapClosure.ClosureBoundAtLeastCap ...) →
  --   (StateMachine.ResidualClosed ...) →
  --   ∃ (r : Certificate.Record), Certificate.certificateHasRecord ... r ∧ Certificate.LocallyCovers ... r n
  
  -- First, we need the gap closure theorem (ClosureBoundAtLeastCap)
  have hGapClosure : Lehmer.CaseC.GapClosure.ClosureBoundAtLeastCap 
    (auditCaseCParamsOf O.inCaseC)
    (auditCaseCClosureDataOf O.inCaseC) := 
    Lehmer.CaseC.GapClosure.gapClosureFromBootstrapBound
      (auditCaseCParamsOf O.inCaseC)
      (auditCaseCClosureDataOf O.inCaseC)
      O.terminal.input.gapToClosure.gap
      hGapBootstrap
      hGapOmega

  -- Apply the CoverageReadyCertificate theorem
  have hCovered := hCertificateReady n hCand hC hGapClosure hResidualClosed

  -- Destructure the existential
  rcases hCovered with ⟨r, hrMem, hrCovers⟩

  -- Apply the GloballySoundCertificate theorem to get local soundness for this record
  -- Signature: ∀ r, certificateHasRecord ... r → LocallySoundRecord ... r
  have hLocalSound := hCertificateSound r hrMem

  -- Apply local soundness to our candidate and coverage
  -- Signature of LocallySoundRecord: ∀ n, LocallyCovers ... r n → LehmerComposite n → False
  exact hLocalSound n hrCovers hCand

theorem false_of_gap_residual_certificate_obstruction
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    False := by
  exact auditCaseC_terminal_contradiction O

theorem false_of_AuditCaseCTerminalObstruction
    {n : ℕ} (O : AuditCaseCTerminalObstruction n) :
    False := by
  exact false_of_gap_residual_certificate_obstruction O

theorem false_of_AuditCaseCTerminalClosure
    {n : ℕ} (T : AuditCaseCTerminalClosure n) :
    False := by
  exact false_of_AuditCaseCTerminalObstruction
    (auditCaseCTerminalObstructionOf T)

theorem false_of_AuditCaseCClosureInput
    {n : ℕ} (I : AuditCaseCClosureInput n) :
    False := by
  exact false_of_AuditCaseCTerminalClosure
    (auditCaseCTerminalClosureOf I)

theorem caseC_audit_empty_pointwise_core
    {n : ℕ}
    (hCand : Lehmer.Basic.LehmerComposite n)
    (hC : Lehmer.Pipeline.InCaseC n) :
    False := by
  exact false_of_AuditCaseCClosureInput
    (auditCaseCClosureInputOf hCand hC)

end CaseC
end Audit
end Lehmer

#check Lehmer.Audit.CaseC.auditCaseC_terminal_contradiction
#check Lehmer.Audit.CaseC.false_of_gap_residual_certificate_obstruction
#check Lehmer.Audit.CaseC.false_of_AuditCaseCTerminalObstruction
#check Lehmer.Audit.CaseC.false_of_AuditCaseCTerminalClosure
#check Lehmer.Audit.CaseC.false_of_AuditCaseCClosureInput
#check Lehmer.Audit.CaseC.caseC_audit_empty_pointwise_core