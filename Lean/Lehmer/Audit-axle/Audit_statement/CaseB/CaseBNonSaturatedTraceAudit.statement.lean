-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseB/CaseBNonSaturatedTraceAudit.statement.lean
import Mathlib

theorem exists_exhaustiveTrace_of_nonSaturatedState
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBNonSaturatedExhaustiveTrace : Context -> Type)
    (caseBNonSaturatedExhaustiveTrace_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        CaseBNonSaturatedExhaustiveTrace C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    Exists fun _ : CaseBNonSaturatedExhaustiveTrace C => True := by
  sorry

theorem contextDescentLength_decreases_of_caseBNonSaturatedBackboneTrace_of_gainProgressData
    (Context : Type)
    (AuditCaseBGainProgressData : Context -> Prop)
    (CaseBNonSaturatedBackboneTrace : Context -> Type)
    (contextDescentLength : Context -> Nat)
    (terminal :
      forall {C : Context},
        CaseBNonSaturatedBackboneTrace C ->
        Context)
    (caseBNonSaturatedBackboneTrace_of_gainProgressData :
      forall C : Context,
        AuditCaseBGainProgressData C ->
        CaseBNonSaturatedBackboneTrace C)
    (decreases_of_gainProgressData :
      forall (C : Context) (hP : AuditCaseBGainProgressData C),
        contextDescentLength
          (terminal (caseBNonSaturatedBackboneTrace_of_gainProgressData C hP)) <
        contextDescentLength C)
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    contextDescentLength
      (terminal (caseBNonSaturatedBackboneTrace_of_gainProgressData C hP)) <
    contextDescentLength C := by
  sorry

theorem contextDescentLength_decreases_of_caseBNonSaturatedBackboneTrace_of_state_and_gainProgress
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBGainProgressData : Context -> Prop)
    (CaseBNonSaturatedBackboneTrace : Context -> Type)
    (contextDescentLength : Context -> Nat)
    (terminal :
      forall {C : Context},
        CaseBNonSaturatedBackboneTrace C ->
        Context)
    (caseBNonSaturatedBackboneTrace_of_state_and_gainProgress :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        AuditCaseBGainProgressData C ->
        CaseBNonSaturatedBackboneTrace C)
    (decreases_of_state_and_gainProgress :
      forall (C : Context)
        (hC : AuditCaseBNonSaturatedState C)
        (hP : AuditCaseBGainProgressData C),
        contextDescentLength
          (terminal
            (caseBNonSaturatedBackboneTrace_of_state_and_gainProgress C hC hP)) <
        contextDescentLength C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hP : AuditCaseBGainProgressData C) :
    contextDescentLength
      (terminal
        (caseBNonSaturatedBackboneTrace_of_state_and_gainProgress C hC hP)) <
    contextDescentLength C := by
  sorry

theorem caseBNonSaturatedBackboneTrace_of_branch_finite
    (Context : Type)
    (AuditCaseBNonSaturatedBranch : Context -> Type)
    (CaseBNonSaturatedBackboneTrace : Context -> Type)
    (length :
      forall {C : Context},
        CaseBNonSaturatedBackboneTrace C ->
        Nat)
    (caseBNonSaturatedBackboneTrace_of_branch :
      forall {C : Context},
        AuditCaseBNonSaturatedBranch C ->
        CaseBNonSaturatedBackboneTrace C)
    (length_of_branch :
      forall {C : Context} (B : AuditCaseBNonSaturatedBranch C),
        length (caseBNonSaturatedBackboneTrace_of_branch B) = 1)
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    Exists fun n : Nat =>
      length (caseBNonSaturatedBackboneTrace_of_branch B) = n := by
  sorry