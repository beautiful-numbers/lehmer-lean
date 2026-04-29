-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/NonSaturatedCaseBClosure.statement.lean
import Mathlib

theorem false_of_nonSaturatedCaseBClosureRouting
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (NonSaturatedCaseBClosureRouting : Context -> Type)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (false_of_terminalBridgeInput :
      forall {B : ClosedBudgetFunctions} {C : Context},
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (_R : NonSaturatedCaseBClosureRouting C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  sorry

theorem false_of_AuditCaseBNonSaturatedState_via_terminalBridge
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (NonSaturatedCaseBClosureRouting : Context -> Type)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (nonSaturatedCaseBClosureRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        NonSaturatedCaseBClosureRouting C)
    (false_of_terminalBridgeInput :
      forall {B : ClosedBudgetFunctions} {C : Context},
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  sorry

theorem nonSaturatedCaseBClosure_of_state
    (Context : Type)
    (ClosedBudgetFunctions : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (NonSaturatedCaseBClosureRouting : Context -> Type)
    (CaseBTerminalBridgeInput : ClosedBudgetFunctions -> Context -> Type)
    (NoCrossingGlobalCertificate : ClosedBudgetFunctions -> Prop)
    (nonSaturatedCaseBClosureRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        NonSaturatedCaseBClosureRouting C)
    (false_of_terminalBridgeInput :
      forall {B : ClosedBudgetFunctions} {C : Context},
        CaseBTerminalBridgeInput B C ->
        NoCrossingGlobalCertificate B ->
        False)
    {B : ClosedBudgetFunctions}
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  sorry