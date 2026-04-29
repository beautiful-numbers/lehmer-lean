-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseC/Contradiction.proof.lean
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
  exact terminalContradiction O

theorem false_of_gap_residual_certificate_obstruction
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (O : AuditCaseCTerminalObstruction n) :
    False := by
  exact auditCaseC_terminal_contradiction
    AuditCaseCTerminalObstruction
    terminalContradiction
    O

theorem false_of_AuditCaseCTerminalObstruction
    (AuditCaseCTerminalObstruction : Nat -> Type)
    (terminalContradiction :
      forall {n : Nat},
        AuditCaseCTerminalObstruction n ->
        False)
    {n : Nat}
    (O : AuditCaseCTerminalObstruction n) :
    False := by
  exact false_of_gap_residual_certificate_obstruction
    AuditCaseCTerminalObstruction
    terminalContradiction
    O

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
  exact false_of_AuditCaseCTerminalObstruction
    AuditCaseCTerminalObstruction
    terminalContradiction
    (auditCaseCTerminalObstructionOf T)

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
  exact false_of_AuditCaseCTerminalClosure
    AuditCaseCTerminalObstruction
    AuditCaseCTerminalClosure
    auditCaseCTerminalObstructionOf
    terminalContradiction
    (auditCaseCTerminalClosureOf I)

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
  exact false_of_AuditCaseCClosureInput
    AuditCaseCTerminalObstruction
    AuditCaseCTerminalClosure
    AuditCaseCClosureInput
    auditCaseCTerminalObstructionOf
    auditCaseCTerminalClosureOf
    terminalContradiction
    (auditCaseCClosureInputOf hCand hC)