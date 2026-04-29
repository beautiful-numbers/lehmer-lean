-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGatePassWitnessAccountingAudit.proof.lean
import Mathlib

theorem exists_caseBGatePassWitnessAccountingRouting_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (CaseBGatePassWitnessAccountingRouting : Context -> Type)
    (caseBGatePassWitnessAccountingRouting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        CaseBGatePassWitnessAccountingRouting C)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : CaseBGatePassWitnessAccountingRouting C => True := by
  exact Exists.intro
    (caseBGatePassWitnessAccountingRouting_of_state C hC)
    True.intro

theorem exists_witnessAccounting_gatePass_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (AuditCaseBGatePassData : Context -> Type)
    (witnessAccounting_gatePass_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : AuditCaseBGatePassData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : AuditCaseBGatePassData C => True := by
  exact witnessAccounting_gatePass_of_state C hC

theorem exists_gatePassAccounting_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (WitnessAccounting : Context -> Type)
    (gatePassAccounting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : WitnessAccounting C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : WitnessAccounting C => True := by
  exact gatePassAccounting_of_state C hC