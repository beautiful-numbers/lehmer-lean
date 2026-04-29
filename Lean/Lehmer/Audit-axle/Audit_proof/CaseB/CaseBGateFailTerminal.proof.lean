-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGateFailTerminal.proof.lean
import Mathlib

theorem exists_caseBGateFailTerminalRouting_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailTerminalRouting : Context -> Type)
    (caseBGateFailTerminalRouting_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        CaseBGateFailTerminalRouting C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailTerminalRouting C => True := by
  exact Exists.intro
    (caseBGateFailTerminalRouting_of_state C hC)
    True.intro

theorem exists_terminal_gateFail_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (AuditCaseBGateFailData : Context -> Type)
    (terminal_gateFail_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        Exists fun _ : AuditCaseBGateFailData C => True)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : AuditCaseBGateFailData C => True := by
  exact terminal_gateFail_of_state C hC

theorem exists_gateFailTerminal_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (GateFailSupplyData : Context -> Type)
    (gateFailTerminal_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        Exists fun _ : GateFailSupplyData C => True)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : GateFailSupplyData C => True := by
  exact gateFailTerminal_of_state C hC