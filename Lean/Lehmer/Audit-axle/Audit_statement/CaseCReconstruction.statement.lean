-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseCReconstruction.statement.lean
import Mathlib

def CaseCReconstructionTotal
    (InCaseC : Nat -> Prop)
    (AuditCaseCReconstructionPieces : Nat -> Type) :
    Prop :=
  forall n : Nat,
    InCaseC n ->
      Exists fun _X : AuditCaseCReconstructionPieces n => True

theorem caseC_reconstruction_total
    (InCaseC : Nat -> Prop)
    (AuditCaseCReconstructionPieces : Nat -> Type)
    (auditCaseCReconstructionPiecesOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCReconstructionPieces n) :
    CaseCReconstructionTotal InCaseC AuditCaseCReconstructionPieces := by
  sorry

theorem exists_caseCReconstructionPieces_of_inCaseC
    (InCaseC : Nat -> Prop)
    (AuditCaseCReconstructionPieces : Nat -> Type)
    (auditCaseCReconstructionPiecesOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCReconstructionPieces n)
    {n : Nat}
    (hC : InCaseC n) :
    Exists fun _X : AuditCaseCReconstructionPieces n => True := by
  sorry