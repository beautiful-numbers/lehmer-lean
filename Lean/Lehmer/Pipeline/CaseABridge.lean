-- FILE: Lean/Lehmer/Pipeline/CaseABridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.CaseAContradiction : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.CaseAContradiction
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Pipeline

open Lehmer.Basic

/--
Pipeline-level handledness predicate for the global Case A branch.

After the Case A refactor, this is the pipeline-facing wrapper around the
mathematical Case A predicate imported from the pivot layer through
`GlobalSplit`.
-/
def CaseAHandled (n : ℕ) : Prop :=
  InCaseA n

@[simp] theorem CaseAHandled_def (n : ℕ) :
    CaseAHandled n = InCaseA n := rfl

/--
Bridge theorem: any candidate classified in the global Case A branch is handled
by the Case A side of the pipeline.
-/
theorem caseA_bridge
    {n : ℕ} (_hL : LehmerComposite n)
    (hA : InCaseA n) :
    CaseAHandled n := by
  exact hA

/--
Equivalent bridge theorem written using the abstract branch relation from
`GlobalSplit`.
-/
theorem caseA_bridge_of_falls
    {n : ℕ} (_hL : LehmerComposite n)
    (hA : FallsInGlobalBranch n GlobalBranch.caseA) :
    CaseAHandled n := by
  exact hA

/--
Case A handledness implies that the candidate lies in the declared global
Case A branch.
-/
theorem caseA_handled_implies_in_caseA
    {n : ℕ} (h : CaseAHandled n) :
    InCaseA n := by
  exact h

/--
Case A handledness is exactly the current global Case A branch condition.
-/
theorem caseA_handled_iff_in_caseA
    {n : ℕ} :
    CaseAHandled n ↔ InCaseA n := by
  rfl

/--
Terminal closure predicate for the global Case A branch.

Unlike the MVP version, this closure interface is now correctly relative to the
Lehmer-composite hypothesis, which is the mathematical scope in which the Case A
contradiction is valid.
-/
def CaseAClosed : Prop :=
  ∀ n : ℕ, LehmerComposite n → CaseAHandled n → False

@[simp] theorem CaseAClosed_def :
    CaseAClosed = (∀ n : ℕ, LehmerComposite n → CaseAHandled n → False) := rfl

/--
Mathematical closure of Case A, imported from the pivot layer and repackaged at
the pipeline level.

This is the local non-regression point of the refactor: Case A is now genuinely
closed, while Case B and Case C remain untouched.
-/
theorem caseA_impossible
    {n : ℕ} (hL : LehmerComposite n)
    (hA : InCaseA n) :
    False := by
  exact Lehmer.Pivot.caseA_impossible hL hA

/--
Case A is closed without any residual hypothesis.
-/
theorem caseA_closed :
    CaseAClosed := by
  intro n hL hA
  exact caseA_impossible hL hA

/--
Direct terminal bridge for the global Case A branch.
-/
theorem caseA_bridge_terminal
    {n : ℕ} (hL : LehmerComposite n)
    (hA : InCaseA n) :
    False := by
  exact caseA_closed n hL (caseA_bridge hL hA)

/--
Equivalent terminal interface using the abstract branch relation.
-/
theorem caseA_bridge_terminal_of_falls
    {n : ℕ} (hL : LehmerComposite n)
    (hA : FallsInGlobalBranch n GlobalBranch.caseA) :
    False := by
  exact caseA_closed n hL (caseA_bridge_of_falls hL hA)

end Pipeline
end Lehmer