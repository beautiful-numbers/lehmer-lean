-- FILE: Lean/Lehmer/Pipeline/CaseBBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Main : assemble
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : thm
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.CaseB.Dominance.Contradiction : thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Main
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.ClosedMajorantBound
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.Contradiction
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Pipeline

open Lehmer.Basic
open Lehmer.CaseB

/--
Pipeline-level handledness predicate for the global Case B branch.

As for Case A, the pipeline bridge does not carry the mathematical proof.
It only records that the candidate lies in the global Case B branch and is
therefore routed to the Case B mathematical layer.
-/
def CaseBHandled (n : ℕ) : Prop :=
  InCaseB n

@[simp] theorem CaseBHandled_def (n : ℕ) :
    CaseBHandled n = InCaseB n := rfl

/--
Bridge theorem: any candidate classified in the global Case B branch is handled
by the Case B side of the pipeline.
-/
theorem caseB_bridge
    {n : ℕ} (_hL : LehmerComposite n)
    (hB : InCaseB n) :
    CaseBHandled n := by
  exact hB

/--
Equivalent bridge theorem written using the abstract branch relation from
`GlobalSplit`.
-/
theorem caseB_bridge_of_falls
    {n : ℕ} (_hL : LehmerComposite n)
    (hB : FallsInGlobalBranch n GlobalBranch.caseB) :
    CaseBHandled n := by
  exact hB

/--
Case B handledness implies membership in the declared global Case B branch.
-/
theorem caseB_handled_implies_in_caseB
    {n : ℕ} (h : CaseBHandled n) :
    InCaseB n := by
  exact h

/--
Case B handledness is exactly the current global Case B branch condition.
-/
theorem caseB_handled_iff_in_caseB
    {n : ℕ} :
    CaseBHandled n ↔ InCaseB n := by
  rfl

/--
Terminal closure predicate for the global Case B branch.

As for Case A, the closure interface is correctly relative to the
`LehmerComposite` hypothesis, which is the mathematical scope in which the
Case B contradiction is valid.
-/
def CaseBClosed : Prop :=
  ∀ n : ℕ, LehmerComposite n → CaseBHandled n → False

@[simp] theorem CaseBClosed_def :
    CaseBClosed = (∀ n : ℕ, LehmerComposite n → CaseBHandled n → False) := rfl

/--
Case B contradiction data exported at pipeline level.

The bridge itself does not prove these ingredients; it only packages the exact
mathematical data that the Case B contradiction layer consumes.
-/
structure CaseBPipelineData (n : ℕ) where
  accounting : WitnessAccounting ⟨pivotOf n, primeSupport n⟩
  hdemand : MeetsPivotDemand ⟨pivotOf n, primeSupport n⟩
  hsupply : HasSupplyBound ⟨pivotOf n, primeSupport n⟩ accounting
  hclosed : ClosedWitnessBound accounting
  hlarge : LargePivotRegime ⟨pivotOf n, primeSupport n⟩

/--
Mathematical closure of Case B, imported from the Case B contradiction layer
and repackaged at the pipeline level.

This theorem is the exact analogue of `CaseA`:
the proof lives in `CaseB.Dominance.Contradiction`,
while the pipeline only consumes it.
-/
theorem caseB_impossible
    {n : ℕ} (_hL : LehmerComposite n)
    (hB : InCaseB n)
    (D : CaseBPipelineData n)
    (hno : NoCrossingBeyondYstar) :
    False := by
  exact contradiction_of_supply_closedMajorant_largePivot
    ⟨pivotOf n, primeSupport n⟩
    D.accounting
    D.hdemand
    D.hsupply
    D.hclosed
    D.hlarge
    hno

/--
Case B is closed once the contradiction data and the uniform no-crossing
interface are available.
-/
theorem caseB_closed_of_data
    (hdata : ∀ n : ℕ, LehmerComposite n → InCaseB n → CaseBPipelineData n)
    (hno : NoCrossingBeyondYstar) :
    CaseBClosed := by
  intro n hL hB
  exact caseB_impossible hL hB (hdata n hL hB) hno

/--
Direct terminal bridge for the global Case B branch.
-/
theorem caseB_bridge_terminal
    {n : ℕ} (hL : LehmerComposite n)
    (hB : InCaseB n)
    (D : CaseBPipelineData n)
    (hno : NoCrossingBeyondYstar) :
    False := by
  exact caseB_impossible hL hB D hno

/--
Equivalent terminal interface using the abstract branch relation.
-/
theorem caseB_bridge_terminal_of_falls
    {n : ℕ} (hL : LehmerComposite n)
    (hB : FallsInGlobalBranch n GlobalBranch.caseB)
    (D : CaseBPipelineData n)
    (hno : NoCrossingBeyondYstar) :
    False := by
  exact caseB_impossible hL hB D hno

end Pipeline
end Lehmer