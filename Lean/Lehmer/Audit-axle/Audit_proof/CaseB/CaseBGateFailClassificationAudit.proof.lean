-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGateFailClassificationAudit.proof.lean
import Mathlib

theorem exists_caseBGateFailExhaustiveTraceClassification_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailExhaustiveTraceClassification : Context -> Type)
    (caseBGateFailExhaustiveTraceClassification_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        CaseBGateFailExhaustiveTraceClassification C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailExhaustiveTraceClassification C => True := by
  exact Exists.intro
    (caseBGateFailExhaustiveTraceClassification_of_state C hC)
    True.intro

theorem exists_caseBGateFailTerminalTraceClassification_of_state
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailTerminalTraceClassification : Context -> Type)
    (caseBGateFailTerminalTraceClassification_of_state :
      forall {C : Context},
        AuditCaseBGateFailState C ->
        CaseBGateFailTerminalTraceClassification C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailTerminalTraceClassification C => True := by
  exact Exists.intro
    (caseBGateFailTerminalTraceClassification_of_state hC)
    True.intro