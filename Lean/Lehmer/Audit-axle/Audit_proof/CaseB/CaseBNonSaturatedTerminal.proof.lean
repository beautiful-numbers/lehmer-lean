-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBNonSaturatedTerminal.proof.lean
import Mathlib

theorem exists_caseBNonSaturatedTerminalRouting_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBNonSaturatedTerminalRouting : Context -> Type)
    (caseBNonSaturatedTerminalRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        CaseBNonSaturatedTerminalRouting C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    Exists fun _ : CaseBNonSaturatedTerminalRouting C => True := by
  exact Exists.intro
    (caseBNonSaturatedTerminalRouting_of_state C hC)
    True.intro

theorem exists_terminal_branch_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (terminal_branch_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : AuditCaseBDischargeData C => True) \/
          (Exists fun _ : AuditCaseBEntangledStepData C => True))
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : AuditCaseBDischargeData C => True) \/
    (Exists fun _ : AuditCaseBEntangledStepData C => True) := by
  exact terminal_branch_of_state C hC

theorem exists_dischargeTerminal_or_none_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (DischargeSupplyData : Context -> Type)
    (dischargeTerminal_or_none_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : DischargeSupplyData C => True) \/ True)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : DischargeSupplyData C => True) \/ True := by
  exact dischargeTerminal_or_none_of_state C hC