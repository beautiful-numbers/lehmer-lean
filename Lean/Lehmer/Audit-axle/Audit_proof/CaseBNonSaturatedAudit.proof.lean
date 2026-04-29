-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseBNonSaturatedAudit.proof.lean
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
  exact AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC

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
  exact final_branch_of_nonSaturatedState C hC