-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGatePassLockAudit.proof.lean
import Mathlib

theorem exists_caseBGatePassLockRouting_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (CaseBGatePassLockRouting : Context -> Type)
    (caseBGatePassLockRouting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        CaseBGatePassLockRouting C)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : CaseBGatePassLockRouting C => True := by
  exact Exists.intro
    (caseBGatePassLockRouting_of_state C hC)
    True.intro

theorem exists_gatePass_lockRouting_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (AuditCaseBGatePassData : Context -> Type)
    (gatePass_lockRouting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : AuditCaseBGatePassData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : AuditCaseBGatePassData C => True := by
  exact gatePass_lockRouting_of_state C hC