-- FILE: Lean/Lehmer/Audit-axle/Audit_statement/CandidateCoverage.statement.lean
import Mathlib

inductive RangeBranch where
  | smallPivotRange
  | caseC
  | intermediate
  | caseB
  deriving DecidableEq, Repr

inductive GlobalBranch where
  | caseA
  | caseB
  | intermediate
  | caseC
  deriving DecidableEq, Repr

def ClassifiedInRange
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (n : Nat) :
    RangeBranch -> Prop
  | RangeBranch.smallPivotRange => InSmallPivotRange n
  | RangeBranch.caseC => InCaseC n
  | RangeBranch.intermediate => InIntermediate n
  | RangeBranch.caseB => InCaseB n

def RangeBranchHandled
    (InSmallPivotRange : Nat -> Prop)
    (CaseCHandled : Nat -> Prop)
    (IntermediateHandled : Nat -> Prop)
    (CaseBHandled : Nat -> Prop)
    (n : Nat) :
    RangeBranch -> Prop
  | RangeBranch.smallPivotRange => InSmallPivotRange n
  | RangeBranch.caseC => CaseCHandled n
  | RangeBranch.intermediate => IntermediateHandled n
  | RangeBranch.caseB => CaseBHandled n

def RangeBranchPresent : RangeBranch -> Prop
  | RangeBranch.smallPivotRange => True
  | RangeBranch.caseC => True
  | RangeBranch.intermediate => True
  | RangeBranch.caseB => True

def GlobalBranchPresent : GlobalBranch -> Prop
  | GlobalBranch.caseA => True
  | GlobalBranch.caseB => True
  | GlobalBranch.intermediate => True
  | GlobalBranch.caseC => True

def RangeTaxonomyExhaustiveAudit
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop) :
    Prop :=
  forall n : Nat,
    LehmerComposite n ->
      Exists fun b : RangeBranch =>
        ClassifiedInRange InSmallPivotRange InCaseC InIntermediate InCaseB n b

def RangeTaxonomyHandledAudit
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (CaseCHandled : Nat -> Prop)
    (IntermediateHandled : Nat -> Prop)
    (CaseBHandled : Nat -> Prop) :
    Prop :=
  forall n : Nat,
    LehmerComposite n ->
      Exists fun b : RangeBranch =>
        ClassifiedInRange InSmallPivotRange InCaseC InIntermediate InCaseB n b /\
        RangeBranchHandled InSmallPivotRange CaseCHandled IntermediateHandled CaseBHandled n b

def NoCandidateLeftOut
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop) :
    Prop :=
  RangeTaxonomyExhaustiveAudit
    LehmerComposite InSmallPivotRange InCaseC InIntermediate InCaseB

def NoActiveRangeBranchMissing : Prop :=
  forall b : RangeBranch, RangeBranchPresent b

theorem every_LehmerComposite_is_range_classified
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (global_range_split_exhaustive :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n)
    {n : Nat}
    (h : LehmerComposite n) :
    Exists fun b : RangeBranch =>
      ClassifiedInRange InSmallPivotRange InCaseC InIntermediate InCaseB n b := by
  sorry

theorem classified_range_branch_is_handled
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (CaseCHandled : Nat -> Prop)
    (IntermediateHandled : Nat -> Prop)
    (CaseBHandled : Nat -> Prop)
    (caseC_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseC n -> CaseCHandled n)
    (intermediate_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InIntermediate n -> IntermediateHandled n)
    (caseB_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseB n -> CaseBHandled n)
    {n : Nat}
    (h : LehmerComposite n) :
    forall b : RangeBranch,
      ClassifiedInRange InSmallPivotRange InCaseC InIntermediate InCaseB n b ->
      RangeBranchHandled InSmallPivotRange CaseCHandled IntermediateHandled CaseBHandled n b := by
  sorry

theorem every_LehmerComposite_is_range_classified_and_handled
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (CaseCHandled : Nat -> Prop)
    (IntermediateHandled : Nat -> Prop)
    (CaseBHandled : Nat -> Prop)
    (global_range_split_exhaustive :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n)
    (caseC_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseC n -> CaseCHandled n)
    (intermediate_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InIntermediate n -> IntermediateHandled n)
    (caseB_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseB n -> CaseBHandled n)
    {n : Nat}
    (h : LehmerComposite n) :
    Exists fun b : RangeBranch =>
      ClassifiedInRange InSmallPivotRange InCaseC InIntermediate InCaseB n b /\
      RangeBranchHandled InSmallPivotRange CaseCHandled IntermediateHandled CaseBHandled n b := by
  sorry

theorem range_taxonomy_exhaustive_audit
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (global_range_split_exhaustive :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n) :
    RangeTaxonomyExhaustiveAudit
      LehmerComposite InSmallPivotRange InCaseC InIntermediate InCaseB := by
  sorry

theorem range_taxonomy_handled_audit
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (CaseCHandled : Nat -> Prop)
    (IntermediateHandled : Nat -> Prop)
    (CaseBHandled : Nat -> Prop)
    (global_range_split_exhaustive :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n)
    (caseC_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseC n -> CaseCHandled n)
    (intermediate_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InIntermediate n -> IntermediateHandled n)
    (caseB_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseB n -> CaseBHandled n) :
    RangeTaxonomyHandledAudit
      LehmerComposite
      InSmallPivotRange
      InCaseC
      InIntermediate
      InCaseB
      CaseCHandled
      IntermediateHandled
      CaseBHandled := by
  sorry

theorem no_candidate_left_out
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (global_range_split_exhaustive :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n) :
    NoCandidateLeftOut
      LehmerComposite InSmallPivotRange InCaseC InIntermediate InCaseB := by
  sorry

theorem no_active_range_branch_missing :
    NoActiveRangeBranchMissing := by
  sorry

theorem candidate_coverage_audit_complete
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (CaseCHandled : Nat -> Prop)
    (IntermediateHandled : Nat -> Prop)
    (CaseBHandled : Nat -> Prop)
    (CaseAClosedAudit : Prop)
    (CaseBClosedAudit : Prop)
    (global_range_split_exhaustive :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n)
    (caseC_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseC n -> CaseCHandled n)
    (intermediate_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InIntermediate n -> IntermediateHandled n)
    (caseB_bridge_of_falls :
      forall {n : Nat}, LehmerComposite n -> InCaseB n -> CaseBHandled n)
    (caseA_audit_exhaustive : CaseAClosedAudit)
    (caseB_audit_exhaustive : CaseBClosedAudit) :
    RangeTaxonomyExhaustiveAudit
      LehmerComposite InSmallPivotRange InCaseC InIntermediate InCaseB /\
    RangeTaxonomyHandledAudit
      LehmerComposite
      InSmallPivotRange
      InCaseC
      InIntermediate
      InCaseB
      CaseCHandled
      IntermediateHandled
      CaseBHandled /\
    NoCandidateLeftOut
      LehmerComposite InSmallPivotRange InCaseC InIntermediate InCaseB /\
    NoActiveRangeBranchMissing /\
    CaseAClosedAudit /\
    CaseBClosedAudit /\
    (forall b : GlobalBranch, GlobalBranchPresent b) := by
  sorry

theorem candidate_coverage_from_pipeline
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (RangePipelineExhaustive : Prop)
    (global_range_split_exhaustive :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n)
    (range_pipeline_exhaustive : RangePipelineExhaustive) :
    RangeTaxonomyExhaustiveAudit
      LehmerComposite InSmallPivotRange InCaseC InIntermediate InCaseB /\
    RangePipelineExhaustive := by
  sorry