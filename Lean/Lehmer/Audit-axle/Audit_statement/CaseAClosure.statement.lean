-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CaseAClosure.statement.lean
import Mathlib

theorem audit_caseA_empty_pointwise
    (LehmerComposite : Nat -> Prop)
    (InCaseA : Nat -> Prop)
    (caseA_impossible :
      forall {n : Nat}, LehmerComposite n -> InCaseA n -> False)
    {n : Nat}
    (hCand : LehmerComposite n)
    (hA : InCaseA n) :
    False := by
  sorry

theorem caseA_empty_audit
    (LehmerComposite : Nat -> Prop)
    (InCaseA : Nat -> Prop)
    (caseA_impossible :
      forall {n : Nat}, LehmerComposite n -> InCaseA n -> False) :
    forall n : Nat, LehmerComposite n -> InCaseA n -> False := by
  sorry

theorem no_LehmerComposite_in_caseA
    (LehmerComposite : Nat -> Prop)
    (InCaseA : Nat -> Prop)
    (caseA_impossible :
      forall {n : Nat}, LehmerComposite n -> InCaseA n -> False) :
    Not (Exists fun n : Nat => LehmerComposite n /\ InCaseA n) := by
  sorry

theorem audit_not_inCaseA_of_LehmerComposite
    (LehmerComposite : Nat -> Prop)
    (InCaseA : Nat -> Prop)
    (not_inCaseA_of_LehmerComposite :
      forall {n : Nat}, LehmerComposite n -> Not (InCaseA n))
    {n : Nat}
    (hL : LehmerComposite n) :
    Not (InCaseA n) := by
  sorry