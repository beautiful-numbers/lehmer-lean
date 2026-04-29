-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseC/ClosureData.statement.lean
import Mathlib

def AuditCaseCClosureDataAvailable
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureData : Nat -> Type)
    (_auditCaseCClosureDataDataOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCClosureData n)
    {n : Nat}
    (_hC : InCaseC n) :
    Prop :=
  Nonempty (AuditCaseCClosureData n)

theorem auditCaseCClosureDataAvailable
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureData : Nat -> Type)
    (auditCaseCClosureDataDataOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCClosureData n)
    {n : Nat}
    (hC : InCaseC n) :
    AuditCaseCClosureDataAvailable
      InCaseC
      AuditCaseCClosureData
      auditCaseCClosureDataDataOf
      hC := by
  sorry

theorem auditCaseCClosureData_level_eq_pivot
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureData : Nat -> Type)
    (auditCaseCClosureDataDataOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCClosureData n)
    (level : forall {n : Nat}, AuditCaseCClosureData n -> Nat)
    (pivotOf : Nat -> Nat)
    (level_eq_pivot :
      forall {n : Nat} (hC : InCaseC n),
        level (auditCaseCClosureDataDataOf hC) = pivotOf n)
    {n : Nat}
    (hC : InCaseC n) :
    level (auditCaseCClosureDataDataOf hC) = pivotOf n := by
  sorry

theorem auditCaseCClosureData_cap_eq_pivot
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureData : Nat -> Type)
    (auditCaseCClosureDataDataOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCClosureData n)
    (cap : forall {n : Nat}, AuditCaseCClosureData n -> Nat)
    (pivotOf : Nat -> Nat)
    (cap_eq_pivot :
      forall {n : Nat} (hC : InCaseC n),
        cap (auditCaseCClosureDataDataOf hC) = pivotOf n)
    {n : Nat}
    (hC : InCaseC n) :
    cap (auditCaseCClosureDataDataOf hC) = pivotOf n := by
  sorry

theorem auditCaseCClosureData_omegaBound_eq_pivot
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureData : Nat -> Type)
    (auditCaseCClosureDataDataOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCClosureData n)
    (omegaBound : forall {n : Nat}, AuditCaseCClosureData n -> Nat)
    (pivotOf : Nat -> Nat)
    (omegaBound_eq_pivot :
      forall {n : Nat} (hC : InCaseC n),
        omegaBound (auditCaseCClosureDataDataOf hC) = pivotOf n)
    {n : Nat}
    (hC : InCaseC n) :
    omegaBound (auditCaseCClosureDataDataOf hC) = pivotOf n := by
  sorry

theorem auditCaseCClosureData_cap_ge_YA
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureData : Nat -> Type)
    (auditCaseCClosureDataDataOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCClosureData n)
    (cap : forall {n : Nat}, AuditCaseCClosureData n -> Nat)
    (pivotOf : Nat -> Nat)
    (YA : Nat)
    (cap_eq_pivot :
      forall {n : Nat} (hC : InCaseC n),
        cap (auditCaseCClosureDataDataOf hC) = pivotOf n)
    (pivot_ge_YA :
      forall {n : Nat},
        InCaseC n ->
        YA <= pivotOf n)
    {n : Nat}
    (hC : InCaseC n) :
    YA <= cap (auditCaseCClosureDataDataOf hC) := by
  sorry

theorem auditCaseCClosureData_cap_lt_YC
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureData : Nat -> Type)
    (auditCaseCClosureDataDataOf :
      forall {n : Nat},
        InCaseC n ->
        AuditCaseCClosureData n)
    (cap : forall {n : Nat}, AuditCaseCClosureData n -> Nat)
    (pivotOf : Nat -> Nat)
    (YC : Nat)
    (cap_eq_pivot :
      forall {n : Nat} (hC : InCaseC n),
        cap (auditCaseCClosureDataDataOf hC) = pivotOf n)
    (pivot_lt_YC :
      forall {n : Nat},
        InCaseC n ->
        pivotOf n < YC)
    {n : Nat}
    (hC : InCaseC n) :
    cap (auditCaseCClosureDataDataOf hC) < YC := by
  sorry