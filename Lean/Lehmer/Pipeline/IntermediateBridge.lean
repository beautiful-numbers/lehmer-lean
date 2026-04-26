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
Bridge data for the global intermediate branch.

This is the honest terminal interface for the intermediate branch: the paper-side
or reconstruction-side data must provide a closure theorem for every Lehmer
candidate in the intermediate range.
-/
structure IntermediateBridgeData where
  terminal :
    ∀ {n : ℕ},
      LehmerComposite n →
      InIntermediate n →
      False

/--
Pipeline-level handledness predicate for the global intermediate branch,
relative to terminal intermediate bridge data.

A candidate is handled by the intermediate bridge when the bridge data supplies
a terminal closure for that candidate.
-/
def IntermediateHandled
    (_B : IntermediateBridgeData) (n : ℕ) : Prop :=
  ∀ _hL : LehmerComposite n, InIntermediate n → False

@[simp] theorem IntermediateHandled_def
    (_B : IntermediateBridgeData) (n : ℕ) :
    IntermediateHandled _B n =
      (∀ _hL : LehmerComposite n, InIntermediate n → False) := rfl

/--
Handledness supplied by the intermediate bridge data.
-/
theorem intermediate_bridge
    (B : IntermediateBridgeData)
    {n : ℕ}
    (_hL : LehmerComposite n)
    (_hI : InIntermediate n) :
    IntermediateHandled B n := by
  intro hL hI
  exact B.terminal hL hI

/--
Equivalent bridge theorem written using the abstract branch relation from
`GlobalSplit`.
-/
theorem intermediate_bridge_of_falls
    (B : IntermediateBridgeData)
    {n : ℕ}
    (_hL : LehmerComposite n)
    (_hI : FallsInGlobalBranch n GlobalBranch.intermediate) :
    IntermediateHandled B n := by
  exact intermediate_bridge B _hL _hI

/--
Terminal closure of the intermediate branch from bridge data.
-/
theorem intermediate_bridge_terminal
    (B : IntermediateBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hI : InIntermediate n) :
    False := by
  exact B.terminal hL hI

/--
Equivalent terminal closure using the abstract branch relation.
-/
theorem intermediate_bridge_terminal_of_falls
    (B : IntermediateBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hI : FallsInGlobalBranch n GlobalBranch.intermediate) :
    False := by
  exact intermediate_bridge_terminal B hL hI

/--
Intermediate bridge data yields a pointwise impossibility theorem for the
intermediate branch.
-/
theorem intermediate_impossible_of_bridge
    (B : IntermediateBridgeData) :
    ∀ n : ℕ, LehmerComposite n → InIntermediate n → False := by
  intro n hL hI
  exact intermediate_bridge_terminal B hL hI

/--
A Lehmer composite cannot lie in the intermediate branch once intermediate
bridge data is available.
-/
theorem not_inIntermediate_of_LehmerComposite_bridge
    (B : IntermediateBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ InIntermediate n := by
  intro hI
  exact intermediate_bridge_terminal B hL hI

/--
Compatibility wrapper: if a closure proof for handledness is supplied, the
intermediate branch closes.
-/
theorem intermediate_bridge_terminal_of_assumption
    (B : IntermediateBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hI : InIntermediate n)
    (hclose : IntermediateHandled B n → False) :
    False := by
  exact hclose (intermediate_bridge B hL hI)

/--
Compatibility wrapper using the abstract branch relation.
-/
theorem intermediate_bridge_terminal_of_falls_assumption
    (B : IntermediateBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hI : FallsInGlobalBranch n GlobalBranch.intermediate)
    (hclose : IntermediateHandled B n → False) :
    False := by
  exact hclose (intermediate_bridge_of_falls B hL hI)

end Pipeline
end Lehmer