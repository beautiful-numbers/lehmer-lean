-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBNonSaturatedWitnessAccountingAudit.proof.lean
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
  exact Exists.intro
    (caseBNonSaturatedWitnessAccountingRouting_of_state C hC)
    True.intro

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
  exact witnessAccounting_branch_of_state C hC

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
  exact dischargeAccounting_or_none_of_state C hC