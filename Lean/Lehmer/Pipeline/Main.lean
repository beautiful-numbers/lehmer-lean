-- FILE: Lean/Lehmer/Pipeline/Main.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Pipeline.CaseABridge : def thm
- Lehmer.Pipeline.CaseBBridge : def thm
- Lehmer.Pipeline.IntermediateBridge : def thm
- Lehmer.Pipeline.CaseCBridge : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Pipeline.CaseABridge
import Lehmer.Pipeline.CaseBBridge
import Lehmer.Pipeline.IntermediateBridge
import Lehmer.Pipeline.CaseCBridge

namespace Lehmer
namespace Pipeline

open Lehmer.Basic

/--
Pipeline-level handledness predicate for the global taxonomy.

A Lehmer candidate is pipeline-handled if it is taken in charge by one of the
mathematical branch bridges currently exposed by the pipeline.
-/
def PipelineHandled (n : ℕ) : Prop :=
  CaseAHandled n ∨ CaseBHandled n ∨ IntermediateHandled n ∨ CaseCHandled n

@[simp] theorem PipelineHandled_def (n : ℕ) :
    PipelineHandled n =
      (CaseAHandled n ∨ CaseBHandled n ∨ IntermediateHandled n ∨ CaseCHandled n) := rfl

/--
If a Lehmer candidate falls in the global Case A branch, then it is handled by
the pipeline.
-/
theorem pipelineHandled_of_caseA
    {n : ℕ} (hL : LehmerComposite n)
    (hA : FallsInGlobalBranch n GlobalBranch.caseA) :
    PipelineHandled n := by
  exact Or.inl (caseA_bridge_of_falls hL hA)

/--
If a Lehmer candidate falls in the global Case B branch, then it is handled by
the pipeline.
-/
theorem pipelineHandled_of_caseB
    {n : ℕ} (hL : LehmerComposite n)
    (hB : FallsInGlobalBranch n GlobalBranch.caseB) :
    PipelineHandled n := by
  exact Or.inr (Or.inl (caseB_bridge_of_falls hL hB))

/--
If a Lehmer candidate falls in the global intermediate branch, then it is
handled by the pipeline.
-/
theorem pipelineHandled_of_intermediate
    {n : ℕ} (hL : LehmerComposite n)
    (hI : FallsInGlobalBranch n GlobalBranch.intermediate) :
    PipelineHandled n := by
  exact Or.inr (Or.inr (Or.inl (intermediate_bridge_of_falls hL hI)))

/--
If a Lehmer candidate falls in the global Case C branch, then it is handled by
the pipeline.
-/
theorem pipelineHandled_of_caseC
    {n : ℕ} (hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC) :
    PipelineHandled n := by
  exact Or.inr (Or.inr (Or.inr (caseC_bridge_of_falls hL hC)))

/--
Local pipeline closure of the mathematical Case A branch.

This theorem is the pipeline-facing export of the completed Case A closure.
It does not alter the untouched Case B / intermediate / Case C bridges.
-/
theorem pipeline_closes_caseA
    {n : ℕ} (hL : LehmerComposite n)
    (hA : InCaseA n) :
    False := by
  exact caseA_bridge_terminal hL hA

/--
Equivalent local closure statement using the abstract branch relation.
-/
theorem pipeline_closes_caseA_of_falls
    {n : ℕ} (hL : LehmerComposite n)
    (hA : FallsInGlobalBranch n GlobalBranch.caseA) :
    False := by
  exact caseA_bridge_terminal_of_falls hL hA

/--
Range-level exhaustivity statement for the current transition architecture.

Interpretation:
every Lehmer candidate is covered by the stable range taxonomy consisting of the
legacy small-pivot range together with the unchanged Case C / intermediate /
Case B ranges.
-/
def RangePipelineExhaustive : Prop :=
  ∀ n : ℕ, LehmerComposite n →
    InSmallPivotRange n ∨ InCaseC n ∨ InIntermediate n ∨ InCaseB n

@[simp] theorem RangePipelineExhaustive_def :
    RangePipelineExhaustive =
      (∀ n : ℕ, LehmerComposite n →
        InSmallPivotRange n ∨ InCaseC n ∨ InIntermediate n ∨ InCaseB n) := rfl

/--
Main range-exhaustivity theorem for the pipeline layer at the current Case A
refactor stage.
-/
theorem range_pipeline_exhaustive :
    RangePipelineExhaustive := by
  intro n hL
  exact global_range_split_exhaustive hL

/--
Combined summary theorem for the stable range-based part of the pipeline
taxonomy.
-/
theorem pipeline_range_taxonomy_complete :
    RangeTaxonomyExhaustive ∧ RangePipelineExhaustive := by
  exact ⟨range_taxonomy_exhaustive, range_pipeline_exhaustive⟩

/--
Terminal closure interface for the whole pipeline at the current Case A refactor
stage.

To rule out every Lehmer candidate, it is enough to know:
- the legacy small-pivot range closes;
- the still range-routed branches B / intermediate / C close.

Case A itself is already closed locally by `pipeline_closes_caseA`; the present
theorem is the non-regression assembly interface for the remaining global range
split.
-/
theorem pipeline_closes_all_cases_by_range_assumptions
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    (hcloseI : ∀ {n : ℕ}, LehmerComposite n → InIntermediate n → False)
    (hcloseC : ∀ {n : ℕ}, LehmerComposite n → InCaseC n → False)
    {n : ℕ} (hL : LehmerComposite n) :
    False := by
  rcases global_range_split_exhaustive hL with hA | hC | hI | hB
  · exact hcloseSmallA hL hA
  · exact hcloseC hL hC
  · exact hcloseI hL hI
  · exact hcloseB hL hB

/--
A convenience variant isolating the already-completed mathematical Case A
closure from the remaining range-based closure obligations.
-/
theorem pipeline_closes_completed_caseA_and_remaining_ranges
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    (hcloseI : ∀ {n : ℕ}, LehmerComposite n → InIntermediate n → False)
    (hcloseC : ∀ {n : ℕ}, LehmerComposite n → InCaseC n → False)
    {n : ℕ} (hL : LehmerComposite n) :
    False := by
  exact pipeline_closes_all_cases_by_range_assumptions
    hcloseSmallA hcloseB hcloseI hcloseC hL

end Pipeline
end Lehmer