-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseBNonSaturatedAudit.statement.lean
import Mathlib

theorem progress_audit_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBExhaustiveLocalOutcome : Context -> Prop)
    (AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState :
      forall {C : Context},
        AuditCaseBNonSaturatedState C ->
        AuditCaseBExhaustiveLocalOutcome C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBExhaustiveLocalOutcome C := by
  sorry

theorem exists_final_audit_branch_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (final_branch_of_nonSaturatedState :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : AuditCaseBDischargeData C => True) \/
          (Exists fun _ : AuditCaseBEntangledStepData C => True))
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : AuditCaseBDischargeData C => True) \/
    (Exists fun _ : AuditCaseBEntangledStepData C => True) := by
  sorry