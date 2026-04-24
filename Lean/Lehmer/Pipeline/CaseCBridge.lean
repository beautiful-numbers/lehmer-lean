-- FILE: Lean/Lehmer/Pipeline/CaseCBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Main : assemble
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Main
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Pipeline

open Lehmer.Basic

/--
Pipeline-level handledness predicate for the global Case C branch.

At the current bridge stage, handledness records that the candidate is routed to
the global Case C branch. Richer Case C-facing data can be added once the
corresponding canonical API is exposed by the Case C layer.
-/
def CaseCHandled (n : ℕ) : Prop :=
  InCaseC n

@[simp] theorem CaseCHandled_def (n : ℕ) :
    CaseCHandled n = InCaseC n := rfl

/--
Case C handledness exposes the global Case C branch membership.
-/
theorem CaseCHandled.in_caseC
    {n : ℕ} (h : CaseCHandled n) :
    InCaseC n := by
  exact h

/--
Bridge theorem: any candidate classified in the global Case C branch is handled
by the Case C side of the pipeline.
-/
theorem caseC_bridge
    {n : ℕ} (_hL : LehmerComposite n)
    (hC : InCaseC n) :
    CaseCHandled n := by
  exact hC

/--
Equivalent bridge theorem written using the abstract branch relation from
`GlobalSplit`.
-/
theorem caseC_bridge_of_falls
    {n : ℕ} (_hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC) :
    CaseCHandled n := by
  exact hC

/--
Case C handledness implies membership in the declared global Case C branch.
-/
theorem caseC_handled_implies_in_caseC
    {n : ℕ} (h : CaseCHandled n) :
    InCaseC n := by
  exact h

/--
Case C handledness is exactly the current global Case C branch condition.
-/
theorem caseC_handled_iff_in_caseC
    {n : ℕ} :
    CaseCHandled n ↔ InCaseC n := by
  rfl

/--
Terminal interface for the Case C branch.

This theorem is the correct shape for the next strengthening step:
once a terminal closure proof for `CaseCHandled n` is available, it can be
consumed here to close the global Case C branch.
-/
theorem caseC_bridge_terminal_of_assumption
    {n : ℕ} (_hL : LehmerComposite n)
    (hC : InCaseC n)
    (hclose : CaseCHandled n → False) :
    False := by
  exact hclose (caseC_bridge _hL hC)

/--
Equivalent terminal interface using the abstract branch relation.
-/
theorem caseC_bridge_terminal_of_falls_assumption
    {n : ℕ} (_hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC)
    (hclose : CaseCHandled n → False) :
    False := by
  exact hclose (caseC_bridge_of_falls _hL hC)

end Pipeline
end Lehmer