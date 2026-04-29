-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBGateFailTraceAudit.proof.lean
import Mathlib

theorem exists_exhaustiveTrace_of_gateFailState
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailExhaustiveTrace : Context -> Type)
    (caseBGateFailExhaustiveTrace_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        CaseBGateFailExhaustiveTrace C)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun _ : CaseBGateFailExhaustiveTrace C => True := by
  exact Exists.intro
    (caseBGateFailExhaustiveTrace_of_state C hC)
    True.intro

theorem caseBGateFailTerminalTrace_of_state_finite
    (Context : Type)
    (AuditCaseBGateFailState : Context -> Prop)
    (CaseBGateFailTerminalTrace : Context -> Type)
    (CaseBGateFailTerminalTrace_length :
      forall {C : Context},
        CaseBGateFailTerminalTrace C ->
        Nat)
    (caseBGateFailTerminalTrace_of_state :
      forall C : Context,
        AuditCaseBGateFailState C ->
        CaseBGateFailTerminalTrace C)
    (caseBGateFailTerminalTrace_of_state_length :
      forall (C : Context) (hC : AuditCaseBGateFailState C),
        CaseBGateFailTerminalTrace_length
          (caseBGateFailTerminalTrace_of_state C hC) = 0)
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    Exists fun n : Nat =>
      CaseBGateFailTerminalTrace_length
        (caseBGateFailTerminalTrace_of_state C hC) = n := by
  exact Exists.intro 0
    (caseBGateFailTerminalTrace_of_state_length C hC)