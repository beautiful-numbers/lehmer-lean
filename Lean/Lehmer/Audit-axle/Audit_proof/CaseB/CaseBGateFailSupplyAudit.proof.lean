-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGateFailSupplyAudit.proof.lean
import Mathlib

theorem exists_caseBGateFailSupplyRouting_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailSupplyRouting : Context -> Type)
    (caseBGateFailSupplyRouting_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        CaseBGateFailSupplyRouting C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailSupplyRouting C => True := by
  exact Exists.intro
    (caseBGateFailSupplyRouting_of_state C hC)
    True.intro

theorem exists_supply_gateFail_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (AuditCaseBGateFailData : Context -> Type)
    (supply_gateFail_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        Exists fun _ : AuditCaseBGateFailData C => True)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : AuditCaseBGateFailData C => True := by
  exact supply_gateFail_of_state C hC

theorem exists_gateFailSupply_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (GateFailSupplyData : Context -> Type)
    (gateFailSupply_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        Exists fun _ : GateFailSupplyData C => True)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : GateFailSupplyData C => True := by
  exact gateFailSupply_of_state C hC