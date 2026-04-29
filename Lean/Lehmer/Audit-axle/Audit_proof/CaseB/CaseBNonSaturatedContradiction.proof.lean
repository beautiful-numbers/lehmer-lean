-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBNonSaturatedContradiction.proof.lean
import Mathlib

theorem exists_caseBNonSaturatedContradictionRouting_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBNonSaturatedContradictionRouting : Context -> Type)
    (caseBNonSaturatedContradictionRouting_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        CaseBNonSaturatedContradictionRouting C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    Exists fun _ : CaseBNonSaturatedContradictionRouting C => True := by
  exact Exists.intro
    (caseBNonSaturatedContradictionRouting_of_state C hC)
    True.intro

theorem exists_contradiction_branch_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (AuditCaseBDischargeData : Context -> Type)
    (AuditCaseBEntangledStepData : Context -> Type)
    (contradiction_branch_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
          (Exists fun _ : AuditCaseBDischargeData C => True) \/
          (Exists fun _ : AuditCaseBEntangledStepData C => True))
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (Exists fun _ : AuditCaseBDischargeData C => True) \/
    (Exists fun _ : AuditCaseBEntangledStepData C => True) := by
  exact contradiction_branch_of_state C hC