-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseB/CaseBNonSaturatedWitnessAccountingAudit.statement.lean
import Mathlib

theorem exists_caseBNonSaturatedWitnessAccountingRouting_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBNonSaturatedWitnessAccountingRouting : Context -> Type)
    (caseBNonSaturatedWitnessAccountingRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        CaseBNonSaturatedWitnessAccountingRouting C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    Exists fun _ : CaseBNonSaturatedWitnessAccountingRouting C => True := by
  sorry

theorem exists_witnessAccounting_branch_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (witnessAccounting_branch_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : AuditCaseBDischargeData C => True) \/
          (Exists fun _ : AuditCaseBEntangledStepData C => True))
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : AuditCaseBDischargeData C => True) \/
    (Exists fun _ : AuditCaseBEntangledStepData C => True) := by
  sorry

theorem exists_dischargeAccounting_or_none_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (WitnessAccounting : Context -> Type)
    (dischargeAccounting_or_none_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : WitnessAccounting C => True) \/ True)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : WitnessAccounting C => True) \/ True := by
  sorry