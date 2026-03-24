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

/--
Pipeline-level handledness predicate for the global Case B branch.

At the current stage, this bridge records that the candidate has entered the
global Case B branch. A stronger terminal closure theorem can later consume
this handledness predicate.
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
Terminal interface for the Case B branch.

This theorem is the correct shape for the next strengthening step:
once a terminal closure proof for `CaseBHandled n` is available, it can be
consumed here to close the global Case B branch.
-/
theorem caseB_bridge_terminal_of_assumption
    {n : ℕ} (_hL : LehmerComposite n)
    (hB : InCaseB n)
    (hclose : CaseBHandled n → False) :
    False := by
  exact hclose (caseB_bridge _hL hB)

/--
Equivalent terminal interface using the abstract branch relation.
-/
theorem caseB_bridge_terminal_of_falls_assumption
    {n : ℕ} (_hL : LehmerComposite n)
    (hB : FallsInGlobalBranch n GlobalBranch.caseB)
    (hclose : CaseBHandled n → False) :
    False := by
  exact hclose (caseB_bridge_of_falls _hL hB)

end Pipeline
end Lehmer