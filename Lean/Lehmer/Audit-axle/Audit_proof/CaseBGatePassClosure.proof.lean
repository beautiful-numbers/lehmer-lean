-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseBGatePassClosure.proof.lean
import Mathlib

theorem false_of_caseBGatePassClosureRouting
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (CaseBGatePassClosureRouting : Context -> Type)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (false_of_terminalBridgeInput :
      forall {B : ClosedBudgetFunctions} {C : Context},
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (_R : CaseBGatePassClosureRouting C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_terminalBridgeInput I hno

theorem false_of_AuditCaseBGatePassState_via_terminalBridge
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (CaseBGatePassClosureRouting : Context -> Type)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (caseBGatePassClosureRouting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        CaseBGatePassClosureRouting C)
    (false_of_terminalBridgeInput :
      forall {B : ClosedBudgetFunctions} {C : Context},
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (hC : AuditCaseBGatePassState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_caseBGatePassClosureRouting
    Context
    ClosedBudgetFunctions
    CaseBGatePassClosureRouting
    CaseBTerminalBridgeInput
    NoCrossingGlobalCertificate
    false_of_terminalBridgeInput
    (caseBGatePassClosureRouting_of_state C hC)
    I
    hno

theorem caseBGatePassClosure_of_state
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (CaseBGatePassClosureRouting : Context -> Type)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (caseBGatePassClosureRouting_of_state :
      forall C : Context,
        AuditCaseBGatePassState C ->
        CaseBGatePassClosureRouting C)
    (false_of_terminalBridgeInput :
      forall {B : ClosedBudgetFunctions} {C : Context},
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (hC : AuditCaseBGatePassState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_AuditCaseBGatePassState_via_terminalBridge
    Context
    ClosedBudgetFunctions
    AuditCaseBGatePassState
    CaseBGatePassClosureRouting
    CaseBTerminalBridgeInput
    NoCrossingGlobalCertificate
    caseBGatePassClosureRouting_of_state
    false_of_terminalBridgeInput
    hC
    I
    hno