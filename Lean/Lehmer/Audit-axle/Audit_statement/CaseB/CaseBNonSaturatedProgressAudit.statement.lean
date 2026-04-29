-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseB/CaseBNonSaturatedProgressAudit.statement.lean
import Mathlib

def AuditCaseBExhaustiveLocalOutcome
    (Context : Type)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (C : Context) :
    Prop :=
  (Exists fun _ : AuditCaseBDischargeData C => True) \/
  (Exists fun _ : AuditCaseBEntangledStepData C => True)

theorem AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (exhaustiveLocalOutcome_of_nonSaturatedState :
      forall {C : Context},
        AuditCaseBNonSaturatedState C ->
          AuditCaseBExhaustiveLocalOutcome
            Context
            AuditCaseBDischargeData
            AuditCaseBEntangledStepData
            C)
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBExhaustiveLocalOutcome
      Context
      AuditCaseBDischargeData
      AuditCaseBEntangledStepData
      C := by
  sorry

theorem exists_discharge_or_entangled_of_nonSaturatedState
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (exhaustiveLocalOutcome_of_nonSaturatedState :
      forall {C : Context},
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : AuditCaseBDischargeData C => True) \/
          (Exists fun _ : AuditCaseBEntangledStepData C => True))
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : AuditCaseBDischargeData C => True) \/
    (Exists fun _ : AuditCaseBEntangledStepData C => True) := by
  sorry

theorem exists_discharge_of_purelyGeneric
    (Context : Type)
    (AuditCaseBPurelyGenericBranch : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (auditCaseBDischargeData_of_purelyGeneric :
      forall {C : Context},
        AuditCaseBPurelyGenericBranch C ->
        AuditCaseBDischargeData C)
    (C : Context)
    (hpg : AuditCaseBPurelyGenericBranch C) :
    Exists fun _ : AuditCaseBDischargeData C => True := by
  sorry

theorem exists_entangled_of_boundary_not_purelyGeneric
    (Context : Type)
    (AuditCaseBLocalBoundaryData : Context -> Prop)
    (ContextPurelyGeneric : Context -> Prop)
    (AuditCaseBEntangledStepData : Context -> Type)
    (auditCaseBEntangledStepData_of_boundary :
      forall C : Context,
        AuditCaseBLocalBoundaryData C ->
        Not (ContextPurelyGeneric C) ->
        AuditCaseBEntangledStepData C)
    (C : Context)
    (hB : AuditCaseBLocalBoundaryData C)
    (hnot : Not (ContextPurelyGeneric C)) :
    Exists fun _ : AuditCaseBEntangledStepData C => True := by
  sorry

theorem exists_AuditCaseBNonSaturatedBranch_of_gainProgressData
    (Context : Type)
    (AuditCaseBGainProgressData : Context -> Prop)
    (AuditCaseBNonSaturatedBranch : Context -> Type)
    (auditCaseBNonSaturatedBranch_of_gainProgressData :
      forall C : Context,
        AuditCaseBGainProgressData C ->
        AuditCaseBNonSaturatedBranch C)
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    Exists fun _ : AuditCaseBNonSaturatedBranch C => True := by
  sorry

theorem exists_AuditCaseBNonSaturatedBranch_of_state_and_gainProgress
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBGainProgressData : Context -> Prop)
    (AuditCaseBNonSaturatedBranch : Context -> Type)
    (auditCaseBNonSaturatedBranch_of_state_and_gainProgress :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        AuditCaseBGainProgressData C ->
        AuditCaseBNonSaturatedBranch C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hP : AuditCaseBGainProgressData C) :
    Exists fun _ : AuditCaseBNonSaturatedBranch C => True := by
  sorry