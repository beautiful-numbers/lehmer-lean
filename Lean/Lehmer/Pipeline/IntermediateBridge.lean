-- FILE: Lean/Lehmer/Pipeline/IntermediateBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Pipeline

open Lehmer.Basic

/--
Pipeline-level handledness predicate for the global intermediate branch.

At the current stage, this bridge only records that the candidate has entered
the global intermediate branch. A stronger terminal closure theorem can later
consume this handledness predicate.
-/
def IntermediateHandled (n : ℕ) : Prop :=
  InIntermediate n

@[simp] theorem IntermediateHandled_def (n : ℕ) :
    IntermediateHandled n = InIntermediate n := rfl

/--
Bridge theorem: any candidate classified in the global intermediate branch is
handled by the intermediate side of the pipeline.
-/
theorem intermediate_bridge
    {n : ℕ} (_hL : LehmerComposite n)
    (hI : InIntermediate n) :
    IntermediateHandled n := by
  exact hI

/--
Equivalent bridge theorem written using the abstract branch relation from
`GlobalSplit`.
-/
theorem intermediate_bridge_of_falls
    {n : ℕ} (_hL : LehmerComposite n)
    (hI : FallsInGlobalBranch n GlobalBranch.intermediate) :
    IntermediateHandled n := by
  exact hI

/--
Intermediate handledness implies membership in the declared global
intermediate branch.
-/
theorem intermediate_handled_implies_in_intermediate
    {n : ℕ} (h : IntermediateHandled n) :
    InIntermediate n := by
  exact h

/--
Intermediate handledness is exactly the current global intermediate
branch condition.
-/
theorem intermediate_handled_iff_in_intermediate
    {n : ℕ} :
    IntermediateHandled n ↔ InIntermediate n := by
  rfl

/--
Terminal interface for the intermediate branch.

This is the correct shape for the next strengthening step:
once a terminal closure proof for `IntermediateHandled n` is available, it can
be consumed here to close the global intermediate branch.
-/
theorem intermediate_bridge_terminal_of_assumption
    {n : ℕ} (_hL : LehmerComposite n)
    (hI : InIntermediate n)
    (hclose : IntermediateHandled n → False) :
    False := by
  exact hclose (intermediate_bridge _hL hI)

/--
Equivalent terminal interface using the abstract branch relation.
-/
theorem intermediate_bridge_terminal_of_falls_assumption
    {n : ℕ} (_hL : LehmerComposite n)
    (hI : FallsInGlobalBranch n GlobalBranch.intermediate)
    (hclose : IntermediateHandled n → False) :
    False := by
  exact hclose (intermediate_bridge_of_falls _hL hI)

end Pipeline
end Lehmer