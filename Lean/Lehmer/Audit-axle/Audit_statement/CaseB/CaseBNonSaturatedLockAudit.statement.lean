-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseB/CaseBNonSaturatedLockAudit.statement.lean
import Mathlib

theorem exists_caseBNonSaturatedLockRouting_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBNonSaturatedLockRouting : Context -> Type)
    (caseBNonSaturatedLockRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        CaseBNonSaturatedLockRouting C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    Exists fun _ : CaseBNonSaturatedLockRouting C => True := by
  sorry

theorem exists_discharge_or_entangled_lockRouting_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (discharge_or_entangled_lockRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : AuditCaseBDischargeData C => True) \/
          (Exists fun _ : AuditCaseBEntangledStepData C => True))
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : AuditCaseBDischargeData C => True) \/
    (Exists fun _ : AuditCaseBEntangledStepData C => True) := by
  sorry

theorem exists_caseBNonSaturatedLockAssembly_of_branch
    (Context : Type)
    (AuditCaseBNonSaturatedBranch : Context -> Type)
    (CaseBNonSaturatedLockAssembly : Context -> Type)
    (caseBNonSaturatedLockAssembly_of_branch :
      forall {C : Context},
        AuditCaseBNonSaturatedBranch C ->
        CaseBNonSaturatedLockAssembly C)
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    Exists fun _ : CaseBNonSaturatedLockAssembly C => True := by
  sorry

theorem exists_genericChainToSSLock_of_auditCaseBNonSaturatedBranch
    (Context : Type)
    (AuditCaseBNonSaturatedBranch : Context -> Type)
    (GenericChainToSSLock : Context -> Type)
    (genericChainToSSLock_of_auditCaseBNonSaturatedBranch :
      forall {C : Context},
        AuditCaseBNonSaturatedBranch C ->
        GenericChainToSSLock C)
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    Exists fun _ : GenericChainToSSLock C => True := by
  sorry