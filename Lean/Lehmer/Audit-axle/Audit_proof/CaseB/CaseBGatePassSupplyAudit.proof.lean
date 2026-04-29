-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGatePassSupplyAudit.proof.lean
import Mathlib

theorem exists_caseBGatePassSupplyRouting_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (CaseBGatePassSupplyRouting : Context -> Type)
    (caseBGatePassSupplyRouting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        CaseBGatePassSupplyRouting C)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : CaseBGatePassSupplyRouting C => True := by
  exact Exists.intro
    (caseBGatePassSupplyRouting_of_state C hC)
    True.intro

theorem exists_supply_gatePass_branch_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (AuditCaseBGatePassData : Context -> Type)
    (supply_gatePass_branch_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : AuditCaseBGatePassData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : AuditCaseBGatePassData C => True := by
  exact supply_gatePass_branch_of_state C hC

theorem exists_gatePassSupply_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (GatePassSupplyData : Context -> Type)
    (gatePassSupply_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : GatePassSupplyData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : GatePassSupplyData C => True := by
  exact gatePassSupply_of_state C hC