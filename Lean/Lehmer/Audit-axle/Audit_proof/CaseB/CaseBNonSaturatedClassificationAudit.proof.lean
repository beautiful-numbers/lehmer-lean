-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseB/CaseBNonSaturatedClassificationAudit.proof.lean
import Mathlib

theorem exists_caseBNonSaturatedExhaustiveTraceClassification_of_state
    (Context : Type)
    (AuditCaseBNonSaturatedState : Context -> Prop)
    (CaseBNonSaturatedExhaustiveTraceClassification : Context -> Type)
    (caseBNonSaturatedExhaustiveTraceClassification_of_state :
      forall C : Context,
        AuditCaseBNonSaturatedState C ->
        CaseBNonSaturatedExhaustiveTraceClassification C)
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    Exists fun _ : CaseBNonSaturatedExhaustiveTraceClassification C => True := by
  exact Exists.intro
    (caseBNonSaturatedExhaustiveTraceClassification_of_state C hC)
    True.intro

theorem exists_caseBNonSaturatedCanonicalTraceClassification_of_branch
    (Context : Type)
    (AuditCaseBNonSaturatedBranch : Context -> Type)
    (CaseBNonSaturatedCanonicalTraceClassification : Context -> Type)
    (caseBNonSaturatedCanonicalTraceClassification_of_branch :
      forall {C : Context},
        AuditCaseBNonSaturatedBranch C ->
        CaseBNonSaturatedCanonicalTraceClassification C)
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    Exists fun _ : CaseBNonSaturatedCanonicalTraceClassification C => True := by
  exact Exists.intro
    (caseBNonSaturatedCanonicalTraceClassification_of_branch B)
    True.intro

theorem exists_caseBNonSaturatedTraceClassificationProfile_of_branch
    (Context : Type)
    (AuditCaseBNonSaturatedBranch : Context -> Type)
    (CaseBNonSaturatedTraceClassificationProfile : Context -> Type)
    (caseBNonSaturatedTraceClassificationProfile_of_branch :
      forall {C : Context},
        AuditCaseBNonSaturatedBranch C ->
        CaseBNonSaturatedTraceClassificationProfile C)
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    Exists fun _ : CaseBNonSaturatedTraceClassificationProfile C => True := by
  exact Exists.intro
    (caseBNonSaturatedTraceClassificationProfile_of_branch B)
    True.intro