-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBNonSaturatedSupplyAudit.proof.lean
import Mathlib

theorem exists_caseBNonSaturatedSupplyRouting_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBNonSaturatedSupplyRouting : Context -> Type)
    (caseBNonSaturatedSupplyRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        CaseBNonSaturatedSupplyRouting C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    Exists fun _ : CaseBNonSaturatedSupplyRouting C => True := by
  exact Exists.intro
    (caseBNonSaturatedSupplyRouting_of_state C hC)
    True.intro

theorem exists_supply_branch_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (supply_branch_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : AuditCaseBDischargeData C => True) \/
          (Exists fun _ : AuditCaseBEntangledStepData C => True))
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : AuditCaseBDischargeData C => True) \/
    (Exists fun _ : AuditCaseBEntangledStepData C => True) := by
  exact supply_branch_of_state C hC

theorem exists_dischargeSupply_or_none_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (DischargeSupplyData : Context -> Type)
    (dischargeSupply_or_none_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : DischargeSupplyData C => True) \/ True)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : DischargeSupplyData C => True) \/ True := by
  exact dischargeSupply_or_none_of_state C hC