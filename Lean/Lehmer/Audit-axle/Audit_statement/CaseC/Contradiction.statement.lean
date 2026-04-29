-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseC/Contradiction.statement.lean
import Mathlib

theorem auditCaseC_terminal_contradiction
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (O : AuditCaseCTerminalObstruction n) :
    False := by
  sorry

theorem false_of_gap_residual_certificate_obstruction
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (O : AuditCaseCTerminalObstruction n) :
    False := by
  sorry

theorem false_of_AuditCaseCTerminalObstruction
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (O : AuditCaseCTerminalObstruction n) :
    False := by
  sorry

theorem false_of_AuditCaseCTerminalClosure
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (AuditCaseCTerminalClosure : Nat -> Type)
    (auditCaseCTerminalObstructionOf :
      forall {n : Nat},
        AuditCaseCTerminalClosure n ->
        AuditCaseCTerminalObstruction n)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (T : AuditCaseCTerminalClosure n) :
    False := by
  sorry

theorem false_of_AuditCaseCClosureInput
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (AuditCaseCTerminalClosure : Nat -> Type)
    (AuditCaseCClosureInput : Nat -> Type)
    (auditCaseCTerminalObstructionOf :
      forall {n : Nat},
        AuditCaseCTerminalClosure n ->
        AuditCaseCTerminalObstruction n)
    (auditCaseCTerminalClosureOf :
      forall {n : Nat},
        AuditCaseCClosureInput n ->
        AuditCaseCTerminalClosure n)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (I : AuditCaseCClosureInput n) :
    False := by
  sorry

theorem caseC_audit_empty_pointwise_core
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (AuditCaseCTerminalClosure : Nat -> Type)
    (AuditCaseCClosureInput : Nat -> Type)
    (auditCaseCTerminalObstructionOf :
      forall {n : Nat},
        AuditCaseCTerminalClosure n ->
        AuditCaseCTerminalObstruction n)
    (auditCaseCTerminalClosureOf :
      forall {n : Nat},
        AuditCaseCClosureInput n ->
        AuditCaseCTerminalClosure n)
    (auditCaseCClosureInputOf :
      forall {n : Nat},
        LehmerComposite n ->
        InCaseC n ->
        AuditCaseCClosureInput n)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (hCand : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  sorry