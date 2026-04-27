-- FILE: Lean/Lehmer/Audit/CaseCReconstruction.lean
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
- Lehmer.Audit.CaseC.Exhaustivity : def thm
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
import Lehmer.Audit.CaseC.Exhaustivity

namespace Lehmer
namespace CaseC

def caseCParamsOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.Params :=
  Lehmer.Audit.CaseC.auditCaseCParamsOf hC

@[simp] theorem caseCParamsOf_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCParamsOf hC = Lehmer.Audit.CaseC.auditCaseCParamsOf hC := rfl

def caseCClosureDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.ClosureData (caseCParamsOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCClosureDataOf hC

@[simp] theorem caseCClosureDataOf_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCClosureDataOf hC = Lehmer.Audit.CaseC.auditCaseCClosureDataOf hC := rfl

def caseCNonIntegralityOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCNonIntegralityOf hC

@[simp] theorem caseCNonIntegralityOf_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCNonIntegralityOf hC =
      Lehmer.Audit.CaseC.auditCaseCNonIntegralityOf hC := rfl

def caseCResidualStateOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualState
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCResidualStateOf hC

@[simp] theorem caseCResidualStateOf_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCResidualStateOf hC =
      Lehmer.Audit.CaseC.auditCaseCResidualStateOf hC := rfl

def caseCResidualClosureOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (caseCParamsOf hC)
      (caseCClosureDataOf hC) :=
  Lehmer.Audit.CaseC.auditCaseCResidualClosureOfInCaseC hC

@[simp] theorem caseCResidualClosureOf_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    caseCResidualClosureOf hC =
      Lehmer.Audit.CaseC.auditCaseCResidualClosureOfInCaseC hC := rfl

structure AuditCaseCReconstructionPieces (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  paramsData : Lehmer.Audit.CaseC.AuditCaseCParamsData n
  closureData : Lehmer.Audit.CaseC.AuditCaseCClosureData n
  nonIntegralityData : Lehmer.Audit.CaseC.AuditCaseCNonIntegralityData n
  exhaustivityData : Lehmer.Audit.CaseC.CaseCExhaustivityData n
  nonIntegrality :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (caseCParamsOf inCaseC)
      (caseCClosureDataOf inCaseC)
  residualState :
    Lehmer.CaseC.StateMachine.ResidualState
      (caseCParamsOf inCaseC)
      (caseCClosureDataOf inCaseC)
  residual :
    Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (caseCParamsOf inCaseC)
      (caseCClosureDataOf inCaseC)

@[simp] theorem AuditCaseCReconstructionPieces.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (Pdat : Lehmer.Audit.CaseC.AuditCaseCParamsData n)
    (Ddat : Lehmer.Audit.CaseC.AuditCaseCClosureData n)
    (NIData : Lehmer.Audit.CaseC.AuditCaseCNonIntegralityData n)
    (EData : Lehmer.Audit.CaseC.CaseCExhaustivityData n)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (caseCParamsOf hC) (caseCClosureDataOf hC))
    (U : Lehmer.CaseC.StateMachine.ResidualState
      (caseCParamsOf hC) (caseCClosureDataOf hC))
    (R : Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (caseCParamsOf hC) (caseCClosureDataOf hC)) :
    (AuditCaseCReconstructionPieces.mk
      hC Pdat Ddat NIData EData NI U R).inCaseC = hC := rfl

@[simp] theorem AuditCaseCReconstructionPieces.residual_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (Pdat : Lehmer.Audit.CaseC.AuditCaseCParamsData n)
    (Ddat : Lehmer.Audit.CaseC.AuditCaseCClosureData n)
    (NIData : Lehmer.Audit.CaseC.AuditCaseCNonIntegralityData n)
    (EData : Lehmer.Audit.CaseC.CaseCExhaustivityData n)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (caseCParamsOf hC) (caseCClosureDataOf hC))
    (U : Lehmer.CaseC.StateMachine.ResidualState
      (caseCParamsOf hC) (caseCClosureDataOf hC))
    (R : Lehmer.CaseC.StateMachine.ResidualClosurePackage
      (caseCParamsOf hC) (caseCClosureDataOf hC)) :
    (AuditCaseCReconstructionPieces.mk
      hC Pdat Ddat NIData EData NI U R).residual = R := rfl

def auditCaseCReconstructionPiecesOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCReconstructionPieces n :=
  { inCaseC := hC
    paramsData := Lehmer.Audit.CaseC.auditCaseCParamsDataOf hC
    closureData := Lehmer.Audit.CaseC.auditCaseCClosureDataDataOf hC
    nonIntegralityData := Lehmer.Audit.CaseC.auditCaseCNonIntegralityDataOf hC
    exhaustivityData := Lehmer.Audit.CaseC.caseCExhaustivityDataOf hC
    nonIntegrality := caseCNonIntegralityOf hC
    residualState := caseCResidualStateOf hC
    residual := caseCResidualClosureOf hC }

@[simp] theorem auditCaseCReconstructionPiecesOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_nonIntegrality
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).nonIntegrality =
      caseCNonIntegralityOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_residualState
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).residualState =
      caseCResidualStateOf hC := rfl

@[simp] theorem auditCaseCReconstructionPiecesOf_residual
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCReconstructionPiecesOf hC).residual =
      caseCResidualClosureOf hC := rfl

theorem AuditCaseCReconstructionPieces.residual_closed
    {n : ℕ} (_X : AuditCaseCReconstructionPieces n) :
    Lehmer.CaseC.StateMachine.ResidualClosed
      (caseCParamsOf _X.inCaseC)
      (caseCClosureDataOf _X.inCaseC)
      _X.residual.state := by
  exact _X.residual.closed

def CaseCReconstructionTotal : Prop :=
  ∀ n : ℕ, Lehmer.Pipeline.InCaseC n →
    ∃ _X : AuditCaseCReconstructionPieces n, True

@[simp] theorem CaseCReconstructionTotal_def :
    CaseCReconstructionTotal =
      (∀ n : ℕ, Lehmer.Pipeline.InCaseC n →
        ∃ _X : AuditCaseCReconstructionPieces n, True) := rfl

theorem caseC_reconstruction_total :
    CaseCReconstructionTotal := by
  intro n hC
  exact ⟨auditCaseCReconstructionPiecesOf hC, trivial⟩

theorem exists_caseCReconstructionPieces_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ _X : AuditCaseCReconstructionPieces n, True := by
  exact ⟨auditCaseCReconstructionPiecesOf hC, trivial⟩

end CaseC
end Lehmer