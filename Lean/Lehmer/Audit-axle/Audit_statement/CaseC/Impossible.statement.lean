-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseC/Impossible.statement.lean
import Mathlib

theorem auditCaseCImpossibleOf_pointwise
    (Params : Type)
    (ClosureData : Params -> Type)
    (CaseCMainPackage : forall P : Params, ClosureData P -> Type)
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (caseC_impossible_from_package :
      forall (P : Params)
        (D : ClosureData P)
        (X : CaseCMainPackage P D)
        {n : Nat},
        LehmerComposite n ->
        InCaseC n ->
        False)
    (P : Params)
    (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : Nat}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  sorry

theorem auditCaseCImpossibleOf_not_inCaseC
    (Params : Type)
    (ClosureData : Params -> Type)
    (CaseCMainPackage : forall P : Params, ClosureData P -> Type)
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (not_inCaseC_of_LehmerComposite_from_package :
      forall (P : Params)
        (D : ClosureData P)
        (X : CaseCMainPackage P D)
        {n : Nat},
        LehmerComposite n ->
        Not (InCaseC n))
    (P : Params)
    (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : Nat}
    (hL : LehmerComposite n) :
    Not (InCaseC n) := by
  sorry

theorem auditCaseCImpossibleDataOf_pointwise
    (Params : Type)
    (ClosureData : Params -> Type)
    (CaseCMainPackage : forall P : Params, ClosureData P -> Type)
    (AuditCaseCImpossibleData : forall P : Params, ClosureData P -> Type)
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (auditCaseCImpossibleDataOf :
      forall (P : Params)
        (D : ClosureData P),
        CaseCMainPackage P D ->
        AuditCaseCImpossibleData P D)
    (data_pointwise :
      forall (P : Params)
        (D : ClosureData P)
        (X : AuditCaseCImpossibleData P D)
        {n : Nat},
        LehmerComposite n ->
        InCaseC n ->
        False)
    (P : Params)
    (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : Nat}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  sorry

theorem auditCaseCImpossibleDataOf_not_inCaseC
    (Params : Type)
    (ClosureData : Params -> Type)
    (CaseCMainPackage : forall P : Params, ClosureData P -> Type)
    (AuditCaseCImpossibleData : forall P : Params, ClosureData P -> Type)
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (auditCaseCImpossibleDataOf :
      forall (P : Params)
        (D : ClosureData P),
        CaseCMainPackage P D ->
        AuditCaseCImpossibleData P D)
    (data_not_inCaseC :
      forall (P : Params)
        (D : ClosureData P)
        (X : AuditCaseCImpossibleData P D)
        {n : Nat},
        LehmerComposite n ->
        Not (InCaseC n))
    (P : Params)
    (D : ClosureData P)
    (X : CaseCMainPackage P D)
    {n : Nat}
    (hL : LehmerComposite n) :
    Not (InCaseC n) := by
  sorry