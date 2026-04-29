-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseBGateFailClosure.statement.lean
import Mathlib

theorem false_of_caseCClosure
    (Context : Type)
    (CaseBGateFailToCaseCBridgeInput : Context -> Type)
    (false_of_caseCClosure_external :
      forall {C : Context},
        CaseBGateFailToCaseCBridgeInput C ->
        False)
    {C : Context}
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  sorry

theorem false_of_AuditCaseBGateFailState_via_caseC
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailToCaseCBridgeInput : Context -> Type)
    (false_of_caseCClosure_external :
      forall {C : Context},
        CaseBGateFailToCaseCBridgeInput C ->
        False)
    {C : Context}
    (_hC : AuditCaseBGateFailState C)
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  sorry

theorem caseBGateFailClosure_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailToCaseCBridgeInput : Context -> Type)
    (false_of_caseCClosure_external :
      forall {C : Context},
        CaseBGateFailToCaseCBridgeInput C ->
        False)
    {C : Context}
    (hC : AuditCaseBGateFailState C)
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  sorry