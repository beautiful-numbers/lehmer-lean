-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGateFailLockAudit.proof.lean
import Mathlib

theorem exists_caseBGateFailLockRouting_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailLockRouting : Context -> Type)
    (caseBGateFailLockRouting_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        CaseBGateFailLockRouting C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailLockRouting C => True := by
  exact Exists.intro
    (caseBGateFailLockRouting_of_state C hC)
    True.intro

theorem exists_gateFail_lockRouting_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (AuditCaseBGateFailData : Context -> Type)
    (gateFail_lockRouting_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        Exists fun _ : AuditCaseBGateFailData C => True)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : AuditCaseBGateFailData C => True := by
  exact gateFail_lockRouting_of_state C hC

theorem exists_caseBGateFailLockAssembly_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailLockAssembly : Context -> Type)
    (caseBGateFailLockAssembly_of_state :
      forall {C : Context},
        AuditCaseBGateFailState C ->
        CaseBGateFailLockAssembly C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailLockAssembly C => True := by
  exact Exists.intro
    (caseBGateFailLockAssembly_of_state hC)
    True.intro