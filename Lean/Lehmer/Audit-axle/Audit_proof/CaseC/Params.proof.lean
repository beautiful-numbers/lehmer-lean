-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseC/Params.proof.lean
import Mathlib

theorem auditCaseCParams_level_ge_YA
    (Params : Type)
    (InCaseC : Nat -> Prop)
    (level : Params -> Nat)
    (auditCaseCParamsOf : forall {n : Nat}, InCaseC n -> Params)
    (YA : Nat)
    (inCaseC_ge_YA :
      forall {n : Nat} (hC : InCaseC n),
        YA <= level (auditCaseCParamsOf hC))
    {n : Nat}
    (hC : InCaseC n) :
    YA <= level (auditCaseCParamsOf hC) := by
  exact inCaseC_ge_YA hC

theorem auditCaseCParams_width_ge_YA
    (Params : Type)
    (InCaseC : Nat -> Prop)
    (width : Params -> Nat)
    (auditCaseCParamsOf : forall {n : Nat}, InCaseC n -> Params)
    (YA : Nat)
    (inCaseC_ge_YA :
      forall {n : Nat} (hC : InCaseC n),
        YA <= width (auditCaseCParamsOf hC))
    {n : Nat}
    (hC : InCaseC n) :
    YA <= width (auditCaseCParamsOf hC) := by
  exact inCaseC_ge_YA hC

theorem auditCaseCParams_level_lt_YC
    (Params : Type)
    (InCaseC : Nat -> Prop)
    (level : Params -> Nat)
    (auditCaseCParamsOf : forall {n : Nat}, InCaseC n -> Params)
    (YC : Nat)
    (inCaseC_lt_YC :
      forall {n : Nat} (hC : InCaseC n),
        level (auditCaseCParamsOf hC) < YC)
    {n : Nat}
    (hC : InCaseC n) :
    level (auditCaseCParamsOf hC) < YC := by
  exact inCaseC_lt_YC hC

theorem auditCaseCParams_width_lt_YC
    (Params : Type)
    (InCaseC : Nat -> Prop)
    (width : Params -> Nat)
    (auditCaseCParamsOf : forall {n : Nat}, InCaseC n -> Params)
    (YC : Nat)
    (inCaseC_lt_YC :
      forall {n : Nat} (hC : InCaseC n),
        width (auditCaseCParamsOf hC) < YC)
    {n : Nat}
    (hC : InCaseC n) :
    width (auditCaseCParamsOf hC) < YC := by
  exact inCaseC_lt_YC hC