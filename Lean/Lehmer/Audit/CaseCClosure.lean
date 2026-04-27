-- FILE: Lean/Lehmer/Audit/CaseCClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.CaseC.Main : assemble
- Lehmer.CaseC.StateMachine.Canonicalization : def thm
- Lehmer.Audit.CaseCReconstruction : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit
import Lehmer.CaseC.Main
import Lehmer.CaseC.StateMachine.Canonicalization
import Lehmer.Audit.CaseCReconstruction

namespace Lehmer
namespace Audit

open Lehmer.Basic
open Lehmer.Pipeline
open Lehmer.CaseC

def AuditCandidate (n : ℕ) : Prop :=
  LehmerComposite n

@[simp] theorem AuditCandidate_def (n : ℕ) :
    AuditCandidate n = LehmerComposite n := rfl

def AuditCaseCClass (n : ℕ) : Prop :=
  InCaseC n

@[simp] theorem AuditCaseCClass_def (n : ℕ) :
    AuditCaseCClass n = InCaseC n := rfl

def CaseCEmptyAuditFromPackage
    (P : CaseC.Params) (D : CaseC.ClosureData P) (_X : CaseC.CaseCMainPackage P D) : Prop :=
  ∀ n : ℕ, AuditCandidate n → AuditCaseCClass n → False

@[simp] theorem CaseCEmptyAuditFromPackage_def
    (P : CaseC.Params) (D : CaseC.ClosureData P) (_X : CaseC.CaseCMainPackage P D) :
    CaseCEmptyAuditFromPackage P D _X =
      (∀ n : ℕ, AuditCandidate n → AuditCaseCClass n → False) := rfl

theorem audit_caseC_empty_pointwise_from_package
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D)
    {n : ℕ} (hCand : AuditCandidate n) (hC : AuditCaseCClass n) :
    False := by
  exact CaseC.caseC_impossible_from_package P D X hCand hC

theorem caseC_empty_audit_from_package
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseCEmptyAuditFromPackage P D X := by
  intro n hCand hC
  exact audit_caseC_empty_pointwise_from_package P D X hCand hC

theorem no_audit_candidate_in_caseC_from_package
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    ¬ ∃ n : ℕ, AuditCandidate n ∧ AuditCaseCClass n := by
  intro h
  rcases h with ⟨n, hCand, hC⟩
  exact caseC_empty_audit_from_package P D X n hCand hC

theorem no_LehmerComposite_in_caseC_from_package
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    ¬ ∃ n : ℕ, LehmerComposite n ∧ InCaseC n := by
  intro h
  rcases h with ⟨n, hL, hC⟩
  exact CaseC.caseC_impossible_from_package P D X hL hC

theorem not_AuditCaseCClass_of_AuditCandidate_from_package
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D)
    {n : ℕ} (hCand : AuditCandidate n) :
    ¬ AuditCaseCClass n := by
  intro hC
  exact audit_caseC_empty_pointwise_from_package P D X hCand hC

theorem audit_not_inCaseC_of_LehmerComposite_from_package
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  exact CaseC.not_inCaseC_of_LehmerComposite_from_package P D X hL

def caseCResidualCanonicalRouting
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseC.StateMachine.ResidualClosureRouting P D :=
  CaseC.StateMachine.canonicalResidualRouting P D X.residual.state

@[simp] theorem caseCResidualCanonicalRouting_def
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    caseCResidualCanonicalRouting P D X =
      CaseC.StateMachine.residualClosureRoutingOfState P D X.residual.state := rfl

theorem caseCResidualCanonicalRouting_state
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseC.StateMachine.ResidualClosureRouting.state P D
      (caseCResidualCanonicalRouting P D X) = X.residual.state := by
  simp [caseCResidualCanonicalRouting_def]

theorem caseCResidualCanonicalRouting_family
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseC.StateMachine.ResidualClosureRouting.family P D
      (caseCResidualCanonicalRouting P D X) =
        CaseC.StateMachine.residualFamily P D X.residual.state := by
  simp [caseCResidualCanonicalRouting_def]

def caseCResidualCanonicalView
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseC.StateMachine.CanonicalResidualView P D :=
  CaseC.StateMachine.canonicalResidualViewOfState P D X.residual.state

@[simp] theorem caseCResidualCanonicalView_def
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    caseCResidualCanonicalView P D X =
      CaseC.StateMachine.canonicalResidualViewOfState P D X.residual.state := rfl

theorem caseCResidualCanonicalView_state
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseC.StateMachine.CanonicalResidualView.state P D
      (caseCResidualCanonicalView P D X) = X.residual.state := by
  simp [caseCResidualCanonicalView_def]

theorem caseCResidualCanonicalView_family
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseC.StateMachine.CanonicalResidualView.family P D
      (caseCResidualCanonicalView P D X) =
        CaseC.StateMachine.residualFamily P D X.residual.state := by
  simp [caseCResidualCanonicalView_def]

theorem caseCResidualCanonicalView_closed
    (P : CaseC.Params) (D : CaseC.ClosureData P) (X : CaseC.CaseCMainPackage P D) :
    CaseC.StateMachine.ResidualClosed P D
      (CaseC.StateMachine.CanonicalResidualView.state P D
        (caseCResidualCanonicalView P D X)) := by
  rw [caseCResidualCanonicalView_state]
  exact X.residual.closed

def CaseCStructuralClosureAudit : Prop :=
  ∀ n : ℕ, AuditCandidate n → AuditCaseCClass n →
    ∃ _X : AuditCaseCReconstructionPieces n, True

@[simp] theorem CaseCStructuralClosureAudit_def :
    CaseCStructuralClosureAudit =
      (∀ n : ℕ, AuditCandidate n → AuditCaseCClass n →
        ∃ _X : AuditCaseCReconstructionPieces n, True) := rfl

theorem caseC_structural_closure_audit :
    CaseCStructuralClosureAudit := by
  intro n _hCand hC
  exact CaseC.exists_caseCReconstructionPieces_of_inCaseC hC

theorem exists_caseC_reconstruction_of_audit_class
    {n : ℕ} (hC : AuditCaseCClass n) :
    ∃ _X : AuditCaseCReconstructionPieces n, True := by
  exact CaseC.exists_caseCReconstructionPieces_of_inCaseC hC

theorem exists_caseC_reconstruction_of_candidate_and_audit_class
    {n : ℕ} (_hCand : AuditCandidate n) (hC : AuditCaseCClass n) :
    ∃ _X : AuditCaseCReconstructionPieces n, True := by
  exact exists_caseC_reconstruction_of_audit_class hC

theorem audit_caseC_reconstruction_total :
    ∀ n : ℕ, AuditCaseCClass n →
      ∃ _X : AuditCaseCReconstructionPieces n, True := by
  intro n hC
  exact exists_caseC_reconstruction_of_audit_class hC

theorem audit_caseC_reconstruction_strong
    {n : ℕ} (hC : AuditCaseCClass n) :
    ∃ X : AuditCaseCReconstructionPieces n,
      X.inCaseC = hC ∧
      X.closureData.level = Lehmer.Pipeline.pivotOf n ∧
      X.closureData.width = Lehmer.Pipeline.pivotOf n ∧
      X.closureData.cap = Lehmer.Pipeline.pivotOf n ∧
      X.closureData.omegaBound = Lehmer.Pipeline.pivotOf n ∧
      Lehmer.CaseC.StateMachine.ResidualClosed
        (Lehmer.CaseC.caseCParamsOf X.inCaseC)
        (Lehmer.CaseC.caseCClosureDataOf X.inCaseC)
        X.residual.state := by
  refine ⟨Lehmer.CaseC.auditCaseCReconstructionPiecesOf hC, ?_⟩
  constructor
  · rfl
  constructor
  · exact (Lehmer.Audit.CaseC.CaseCExhaustivityData.level_eq_pivot'
      (Lehmer.Audit.CaseC.caseCExhaustivityDataOf hC))
  constructor
  · exact (Lehmer.Audit.CaseC.CaseCExhaustivityData.width_eq_pivot'
      (Lehmer.Audit.CaseC.caseCExhaustivityDataOf hC))
  constructor
  · exact (Lehmer.Audit.CaseC.CaseCExhaustivityData.cap_eq_pivot'
      (Lehmer.Audit.CaseC.caseCExhaustivityDataOf hC))
  constructor
  · exact (Lehmer.Audit.CaseC.CaseCExhaustivityData.omegaBound_eq_pivot'
      (Lehmer.Audit.CaseC.caseCExhaustivityDataOf hC))
  · exact Lehmer.CaseC.AuditCaseCReconstructionPieces.residual_closed
      (Lehmer.CaseC.auditCaseCReconstructionPiecesOf hC)

end Audit
end Lehmer