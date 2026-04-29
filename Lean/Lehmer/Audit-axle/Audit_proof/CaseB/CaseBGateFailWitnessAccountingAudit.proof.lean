-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGateFailWitnessAccountingAudit.proof.lean
import Mathlib

theorem exists_caseBGateFailWitnessAccountingRouting_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailWitnessAccountingRouting : Context -> Type)
    (caseBGateFailWitnessAccountingRouting_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        CaseBGateFailWitnessAccountingRouting C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailWitnessAccountingRouting C => True := by
  exact Exists.intro
    (caseBGateFailWitnessAccountingRouting_of_state C hC)
    True.intro

theorem exists_witnessAccounting_gateFail_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (AuditCaseBGateFailData : Context -> Type)
    (witnessAccounting_gateFail_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        Exists fun _ : AuditCaseBGateFailData C => True)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : AuditCaseBGateFailData C => True := by
  exact witnessAccounting_gateFail_of_state C hC

theorem exists_gateFailAccounting_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (WitnessAccounting : Context -> Type)
    (gateFailAccounting_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        Exists fun _ : WitnessAccounting C => True)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : WitnessAccounting C => True := by
  exact gateFailAccounting_of_state C hC