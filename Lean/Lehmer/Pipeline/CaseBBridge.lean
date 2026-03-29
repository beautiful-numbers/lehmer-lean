-- FILE: Lean/Lehmer/Pipeline/CaseBBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Main : assemble
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Main
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Pipeline

open Lehmer.Basic
open Lehmer.CaseB

/--
Pipeline-level handledness predicate for the global Case B branch.

The pipeline bridge does not carry the mathematical proof.
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

end Pipeline
end Lehmer