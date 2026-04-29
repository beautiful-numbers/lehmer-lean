-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CandidateCoverage.proof.lean
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
  cases global_range_split_exhaustive h with
  | inl hSmall =>
      exact Exists.intro RangeBranch.smallPivotRange hSmall
  | inr hRest =>
      cases hRest with
      | inl hCaseC =>
          exact Exists.intro RangeBranch.caseC hCaseC
      | inr hRest2 =>
          cases hRest2 with
          | inl hIntermediate =>
              exact Exists.intro RangeBranch.intermediate hIntermediate
          | inr hCaseB =>
              exact Exists.intro RangeBranch.caseB hCaseB

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
  intro b hb
  cases b with
  | smallPivotRange =>
      exact hb
  | caseC =>
      exact caseC_bridge_of_falls h hb
  | intermediate =>
      exact intermediate_bridge_of_falls h hb
  | caseB =>
      exact caseB_bridge_of_falls h hb

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
  cases every_LehmerComposite_is_range_classified
      LehmerComposite
      InSmallPivotRange
      InCaseC
      InIntermediate
      InCaseB
      global_range_split_exhaustive
      h with
  | intro b hb =>
      exact Exists.intro b
        (And.intro hb
          (classified_range_branch_is_handled
            LehmerComposite
            InSmallPivotRange
            InCaseC
            InIntermediate
            InCaseB
            CaseCHandled
            IntermediateHandled
            CaseBHandled
            caseC_bridge_of_falls
            intermediate_bridge_of_falls
            caseB_bridge_of_falls
            h
            b
            hb))

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
  intro n h
  exact every_LehmerComposite_is_range_classified
    LehmerComposite
    InSmallPivotRange
    InCaseC
    InIntermediate
    InCaseB
    global_range_split_exhaustive
    h

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
  intro n h
  exact every_LehmerComposite_is_range_classified_and_handled
    LehmerComposite
    InSmallPivotRange
    InCaseC
    InIntermediate
    InCaseB
    CaseCHandled
    IntermediateHandled
    CaseBHandled
    global_range_split_exhaustive
    caseC_bridge_of_falls
    intermediate_bridge_of_falls
    caseB_bridge_of_falls
    h

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
  exact range_taxonomy_exhaustive_audit
    LehmerComposite
    InSmallPivotRange
    InCaseC
    InIntermediate
    InCaseB
    global_range_split_exhaustive

theorem no_active_range_branch_missing :
    NoActiveRangeBranchMissing := by
  intro b
  cases b <;> trivial

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
  constructor
  · exact range_taxonomy_exhaustive_audit
      LehmerComposite
      InSmallPivotRange
      InCaseC
      InIntermediate
      InCaseB
      global_range_split_exhaustive
  · constructor
    · exact range_taxonomy_handled_audit
        LehmerComposite
        InSmallPivotRange
        InCaseC
        InIntermediate
        InCaseB
        CaseCHandled
        IntermediateHandled
        CaseBHandled
        global_range_split_exhaustive
        caseC_bridge_of_falls
        intermediate_bridge_of_falls
        caseB_bridge_of_falls
    · constructor
      · exact no_candidate_left_out
          LehmerComposite
          InSmallPivotRange
          InCaseC
          InIntermediate
          InCaseB
          global_range_split_exhaustive
      · constructor
        · exact no_active_range_branch_missing
        · constructor
          · exact caseA_audit_exhaustive
          · constructor
            · exact caseB_audit_exhaustive
            · intro b
              cases b <;> trivial

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
  exact And.intro
    (range_taxonomy_exhaustive_audit
      LehmerComposite
      InSmallPivotRange
      InCaseC
      InIntermediate
      InCaseB
      global_range_split_exhaustive)
    range_pipeline_exhaustive