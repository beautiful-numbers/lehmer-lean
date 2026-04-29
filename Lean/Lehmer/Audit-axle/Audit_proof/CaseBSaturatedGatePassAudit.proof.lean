-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseBSaturatedGatePassAudit.proof.lean
import Mathlib

theorem exists_gatePass_progress_audit_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (AuditCaseBGatePassData : Context -> Type)
    (exists_gatePass_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : AuditCaseBGatePassData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : AuditCaseBGatePassData C => True := by
  exact exists_gatePass_of_state C hC

theorem exists_final_gatePass_audit_branch_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (AuditCaseBGatePassData : Context -> Type)
    (final_gatePass_branch_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : AuditCaseBGatePassData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : AuditCaseBGatePassData C => True := by
  exact final_gatePass_branch_of_state C hC