-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBPurelyGenericDischarge.proof.lean
import Mathlib

theorem purelyGeneric_of_AuditCaseBPurelyGenericBranch
    (Context : Type)
    (AuditCaseBPurelyGenericBranch : Context -> Prop)
    (ContextPurelyGeneric : Context -> Prop)
    (purelyGeneric_of_branch :
      forall {C : Context},
        AuditCaseBPurelyGenericBranch C ->
        ContextPurelyGeneric C)
    {C : Context}
    (hpg : AuditCaseBPurelyGenericBranch C) :
    ContextPurelyGeneric C := by
  exact purelyGeneric_of_branch hpg

theorem exists_AuditCaseBDischargeData_of_purelyGeneric
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
  exact Exists.intro
    (auditCaseBDischargeData_of_purelyGeneric hpg)
    True.intro

theorem exists_AuditCaseBDischargeData_of_boundary_and_no_entangled
    (Context : Type)
    (AuditCaseBLocalBoundaryData : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (EntangledPrimeAt : Context -> Nat -> Prop)
    (auditCaseBDischargeData_of_boundary_and_no_entangled :
      forall C : Context,
        AuditCaseBLocalBoundaryData C ->
        Not (Exists fun p : Nat => EntangledPrimeAt C p) ->
        AuditCaseBDischargeData C)
    (C : Context)
    (hB : AuditCaseBLocalBoundaryData C)
    (hno : Not (Exists fun p : Nat => EntangledPrimeAt C p)) :
    Exists fun _ : AuditCaseBDischargeData C => True := by
  exact Exists.intro
    (auditCaseBDischargeData_of_boundary_and_no_entangled C hB hno)
    True.intro

theorem exists_AuditCaseBDischargeData_of_state_and_no_entangled
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (EntangledPrimeAt : Context -> Nat -> Prop)
    (auditCaseBDischargeData_of_state_and_no_entangled :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        Not (Exists fun p : Nat => EntangledPrimeAt C p) ->
        AuditCaseBDischargeData C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hno : Not (Exists fun p : Nat => EntangledPrimeAt C p)) :
    Exists fun _ : AuditCaseBDischargeData C => True := by
  exact Exists.intro
    (auditCaseBDischargeData_of_state_and_no_entangled C hC hno)
    True.intro