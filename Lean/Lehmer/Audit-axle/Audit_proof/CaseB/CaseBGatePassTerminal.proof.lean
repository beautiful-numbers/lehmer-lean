-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGatePassTerminal.proof.lean
import Mathlib

theorem exists_caseBGatePassTerminalRouting_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (CaseBGatePassTerminalRouting : Context -> Type)
    (caseBGatePassTerminalRouting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        CaseBGatePassTerminalRouting C)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : CaseBGatePassTerminalRouting C => True := by
  exact Exists.intro
    (caseBGatePassTerminalRouting_of_state C hC)
    True.intro

theorem exists_terminal_gatePass_branch_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (AuditCaseBGatePassData : Context -> Type)
    (terminal_gatePass_branch_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : AuditCaseBGatePassData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : AuditCaseBGatePassData C => True := by
  exact terminal_gatePass_branch_of_state C hC

theorem exists_gatePassTerminal_of_state
    (Context : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (GatePassSupplyData : Context -> Type)
    (gatePassTerminal_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        Exists fun _ : GatePassSupplyData C => True)
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    Exists fun _ : GatePassSupplyData C => True := by
  exact gatePassTerminal_of_state C hC