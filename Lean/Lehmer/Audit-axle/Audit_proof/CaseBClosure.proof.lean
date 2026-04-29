-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseBClosure.proof.lean
import Mathlib

theorem false_of_caseBClosureRouting_nonSaturated
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (false_of_AuditCaseBNonSaturatedState_via_terminalBridge :
      forall {B : ClosedBudgetFunctions} {C : Context},
        AuditCaseBNonSaturatedState C ->
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_AuditCaseBNonSaturatedState_via_terminalBridge hC I hno

theorem false_of_caseBClosureRouting_gatePass
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (AuditCaseBGatePassState : Context -> Prop)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (false_of_AuditCaseBGatePassState_via_terminalBridge :
      forall {B : ClosedBudgetFunctions} {C : Context},
        AuditCaseBGatePassState C ->
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (hC : AuditCaseBGatePassState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_AuditCaseBGatePassState_via_terminalBridge hC I hno

theorem false_of_caseBClosureRouting_gateFail
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailToCaseCBridgeInput : Context -> Type)
    (false_of_AuditCaseBGateFailState_via_caseC :
      forall {C : Context},
        AuditCaseBGateFailState C ->
        CaseBGateFailToCaseCBridgeInput C ->
        False)
    {C : Context}
    (hC : AuditCaseBGateFailState C)
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  exact false_of_AuditCaseBGateFailState_via_caseC hC I