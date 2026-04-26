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
def PipelineHandled
    (_BI : IntermediateBridgeData)
    (_BC : CaseCBridgeData)
    (n : ℕ) : Prop :=
  CaseAHandled n ∨
    CaseBHandled n ∨
      IntermediateHandled _BI n ∨
        CaseCHandled n

@[simp] theorem PipelineHandled_def
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    (n : ℕ) :
    PipelineHandled BI BC n =
      (CaseAHandled n ∨
        CaseBHandled n ∨
          IntermediateHandled BI n ∨
            CaseCHandled n) := rfl

/--
If a Lehmer candidate falls in the global Case A branch, then it is handled by
the pipeline.
-/
theorem pipelineHandled_of_caseA
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hA : FallsInGlobalBranch n GlobalBranch.caseA) :
    PipelineHandled BI BC n := by
  exact Or.inl (caseA_bridge_of_falls hL hA)

/--
If a Lehmer candidate falls in the global Case B branch, then it is handled by
the pipeline.
-/
theorem pipelineHandled_of_caseB
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hB : FallsInGlobalBranch n GlobalBranch.caseB) :
    PipelineHandled BI BC n := by
  exact Or.inr (Or.inl (caseB_bridge_of_falls hL hB))

/--
If a Lehmer candidate falls in the global intermediate branch, then it is
handled by the pipeline.
-/
theorem pipelineHandled_of_intermediate
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hI : FallsInGlobalBranch n GlobalBranch.intermediate) :
    PipelineHandled BI BC n := by
  exact Or.inr (Or.inr (Or.inl (intermediate_bridge_of_falls BI hL hI)))

/--
If a Lehmer candidate falls in the global Case C branch, then it is handled by
the pipeline, provided the Case C reconstruction bridge data is available.
-/
theorem pipelineHandled_of_caseC
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC) :
    PipelineHandled BI BC n := by
  exact Or.inr (Or.inr (Or.inr (caseC_bridge_of_falls BC hL hC)))

/--
Local pipeline closure of the mathematical Case A branch.
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
Local pipeline closure of the mathematical intermediate branch from bridge data.
-/
theorem pipeline_closes_intermediate
    (BI : IntermediateBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hI : InIntermediate n) :
    False := by
  exact intermediate_bridge_terminal BI hL hI

/--
Equivalent local intermediate closure statement using the abstract branch
relation.
-/
theorem pipeline_closes_intermediate_of_falls
    (BI : IntermediateBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hI : FallsInGlobalBranch n GlobalBranch.intermediate) :
    False := by
  exact intermediate_bridge_terminal_of_falls BI hL hI

/--
Local pipeline closure of the mathematical Case C branch from reconstruction
bridge data.
-/
theorem pipeline_closes_caseC
    (BC : CaseCBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  exact caseC_bridge_terminal BC hL hC

/--
Equivalent local Case C closure statement using the abstract branch relation.
-/
theorem pipeline_closes_caseC_of_falls
    (BC : CaseCBridgeData)
    {n : ℕ} (hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC) :
    False := by
  exact caseC_bridge_terminal_of_falls BC hL hC

/--
Assumption-based local closure of the global Case B branch.
-/
theorem pipeline_closes_caseB_of_assumption
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    {n : ℕ} (hL : LehmerComposite n)
    (hB : InCaseB n) :
    False := by
  exact hcloseB hL hB

/--
Equivalent assumption-based local Case B closure statement using the abstract
branch relation.
-/
theorem pipeline_closes_caseB_of_falls_assumption
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    {n : ℕ} (hL : LehmerComposite n)
    (hB : FallsInGlobalBranch n GlobalBranch.caseB) :
    False := by
  exact hcloseB hL hB

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
Main range-exhaustivity theorem for the pipeline layer at the current
Case A / Case B refactor stage.
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
Terminal closure interface for the whole pipeline at the current transition
stage.

To rule out every Lehmer candidate, it is enough to know:
- the legacy small-pivot range closes;
- the Case B branch closes under an explicit assumption;
- the intermediate branch closes through structured bridge data;
- Case C reconstruction bridge data is available.

Case A itself is already closed locally by `pipeline_closes_caseA`, the
intermediate branch is closed locally by `pipeline_closes_intermediate`, and
Case C is closed locally by `pipeline_closes_caseC`.
-/
theorem pipeline_closes_all_cases_by_range_assumptions
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    {n : ℕ} (hL : LehmerComposite n) :
    False := by
  rcases global_range_split_exhaustive hL with hA | hC | hI | hB
  · exact hcloseSmallA hL hA
  · exact caseC_bridge_terminal BC hL hC
  · exact intermediate_bridge_terminal BI hL hI
  · exact hcloseB hL hB

/--
A convenience variant isolating the already-completed mathematical Case A
closure and the bridge-driven intermediate / Case C closures from the remaining
range-based closure obligations.
-/
theorem pipeline_closes_completed_caseA_and_remaining_ranges
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    {n : ℕ} (hL : LehmerComposite n) :
    False := by
  exact pipeline_closes_all_cases_by_range_assumptions
    BI BC hcloseSmallA hcloseB hL

/--
Structured bridge data for the terminal pipeline closure.
-/
structure PipelineBridgeData where
  intermediate : IntermediateBridgeData
  caseC : CaseCBridgeData
  closeSmallA :
    ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False
  closeB :
    ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False

/--
The pipeline closes all range-taxonomy branches from structured bridge data.
-/
theorem pipeline_closes_all_cases_from_bridge_data
    (BI : IntermediateBridgeData)
    (BC : CaseCBridgeData)
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    {n : ℕ} (hL : LehmerComposite n) :
    False := by
  exact pipeline_closes_all_cases_by_range_assumptions
    BI BC hcloseSmallA hcloseB hL

/--
Bundled terminal closure of the whole pipeline from `PipelineBridgeData`.
-/
theorem pipeline_closes_all_cases
    (B : PipelineBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n) :
    False := by
  exact pipeline_closes_all_cases_by_range_assumptions
    B.intermediate B.caseC B.closeSmallA B.closeB hL

end Pipeline
end Lehmer