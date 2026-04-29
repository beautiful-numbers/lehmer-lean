-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseC/Exhaustivity.statement.lean
import Mathlib

def CaseCStructuralExhaustivity
    (InCaseC : Nat -> Prop)
    (CaseCExhaustivityData : Nat -> Type) :
    Prop :=
  forall n : Nat,
    InCaseC n ->
      Exists fun _X : CaseCExhaustivityData n => True

def CaseCAuditStructuralExhaustivity
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (CaseCExhaustivityData : Nat -> Type) :
    Prop :=
  forall n : Nat,
    LehmerComposite n ->
    InCaseC n ->
      Exists fun _X : CaseCExhaustivityData n => True

def CaseCClosureInputExhaustivity
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureInput : Nat -> Type) :
    Prop :=
  forall n : Nat,
    LehmerComposite n ->
    InCaseC n ->
      Exists fun _I : AuditCaseCClosureInput n => True

theorem caseC_structural_exhaustivity
    (InCaseC : Nat -> Prop)
    (CaseCExhaustivityData : Nat -> Type)
    (caseCExhaustivityDataOf :
      forall {n : Nat},
        InCaseC n ->
        CaseCExhaustivityData n) :
    CaseCStructuralExhaustivity
      InCaseC
      CaseCExhaustivityData := by
  sorry

theorem caseC_audit_structural_exhaustivity
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (CaseCExhaustivityData : Nat -> Type)
    (caseCExhaustivityDataOf :
      forall {n : Nat},
        InCaseC n ->
        CaseCExhaustivityData n) :
    CaseCAuditStructuralExhaustivity
      LehmerComposite
      InCaseC
      CaseCExhaustivityData := by
  sorry

theorem exists_caseCExhaustivityData_of_inCaseC
    (InCaseC : Nat -> Prop)
    (CaseCExhaustivityData : Nat -> Type)
    (caseCExhaustivityDataOf :
      forall {n : Nat},
        InCaseC n ->
        CaseCExhaustivityData n)
    {n : Nat}
    (hC : InCaseC n) :
    Exists fun _X : CaseCExhaustivityData n => True := by
  sorry

theorem exists_caseCExhaustivityData_of_auditClass
    (InCaseC : Nat -> Prop)
    (CaseCExhaustivityData : Nat -> Type)
    (caseCExhaustivityDataOf :
      forall {n : Nat},
        InCaseC n ->
        CaseCExhaustivityData n)
    {n : Nat}
    (hC : InCaseC n) :
    Exists fun _X : CaseCExhaustivityData n => True := by
  sorry

theorem caseCExhaustivityData_sound
    (InCaseC : Nat -> Prop)
    (CaseCExhaustivityData : Nat -> Type)
    (caseCExhaustivityData_sound_core :
      forall {n : Nat},
        CaseCExhaustivityData n ->
        InCaseC n)
    {n : Nat}
    (X : CaseCExhaustivityData n) :
    InCaseC n := by
  sorry

theorem caseC_closure_input_exhaustivity
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureInput : Nat -> Type)
    (auditCaseCClosureInputOf :
      forall {n : Nat},
        LehmerComposite n ->
        InCaseC n ->
        AuditCaseCClosureInput n) :
    CaseCClosureInputExhaustivity
      LehmerComposite
      InCaseC
      AuditCaseCClosureInput := by
  sorry

theorem exists_auditCaseCClosureInput
    (LehmerComposite : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (AuditCaseCClosureInput : Nat -> Type)
    (auditCaseCClosureInputOf :
      forall {n : Nat},
        LehmerComposite n ->
        InCaseC n ->
        AuditCaseCClosureInput n)
    {n : Nat}
    (hCand : LehmerComposite n)
    (hC : InCaseC n) :
    Exists fun _I : AuditCaseCClosureInput n => True := by
  sorry