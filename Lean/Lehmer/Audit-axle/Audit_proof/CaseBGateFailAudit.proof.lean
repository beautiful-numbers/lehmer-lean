-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseBGateFailAudit.proof.lean
import Mathlib

theorem exists_final_gateFail_audit_branch_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (AuditCaseBGateFailData : Context -> Type)
    (auditCaseBGateFailData_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        AuditCaseBGateFailData C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : AuditCaseBGateFailData C => True := by
  exact Exists.intro (auditCaseBGateFailData_of_state C hC) True.intro