-- FILE: Lean/Lehmer/Pipeline/CaseCBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Main : assemble
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Main
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Pipeline

open Lehmer.Basic

/--
Pipeline-level handledness predicate for the global Case C branch.

A Case C candidate is handled exactly when the Case C side supplies a complete
assembled `CaseCMainPackage` for some parameters and closure data.
-/
def CaseCHandled (_n : ℕ) : Prop :=
  ∃ P : CaseC.Params,
  ∃ D : CaseC.ClosureData P,
    Nonempty (CaseC.CaseCMainPackage P D)

@[simp] theorem CaseCHandled_def (n : ℕ) :
    CaseCHandled n =
      (∃ P : CaseC.Params,
        ∃ D : CaseC.ClosureData P,
          Nonempty (CaseC.CaseCMainPackage P D)) := rfl

/--
Case C handledness exposes the reconstructed Case C main package.
-/
theorem CaseCHandled.exists_main
    {n : ℕ} (h : CaseCHandled n) :
    ∃ P : CaseC.Params,
    ∃ D : CaseC.ClosureData P,
      Nonempty (CaseC.CaseCMainPackage P D) := by
  exact h

/--
Eliminator for handled Case C data.
-/
theorem CaseCHandled.elim
    {n : ℕ}
    (h : CaseCHandled n)
    {α : Prop}
    (k :
      ∀ P : CaseC.Params,
      ∀ D : CaseC.ClosureData P,
        CaseC.CaseCMainPackage P D → α) :
    α := by
  rcases h with ⟨P, D, ⟨X⟩⟩
  exact k P D X

/--
Pipeline-to-Case-C reconstruction interface.

This is the external paper/data input needed by the pipeline: every Lehmer
composite routed to global Case C admits a complete Case C main package.
-/
structure CaseCBridgeData where
  handled :
    ∀ {n : ℕ},
      LehmerComposite n →
      InCaseC n →
      CaseCHandled n

/--
Bridge theorem: any Lehmer composite classified in the global Case C branch is
handled by the reconstructed Case C package.
-/
theorem caseC_bridge
    (B : CaseCBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    CaseCHandled n := by
  exact B.handled hL hC

/--
Equivalent bridge theorem written using the abstract branch relation from
`GlobalSplit`.
-/
theorem caseC_bridge_of_falls
    (B : CaseCBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC) :
    CaseCHandled n := by
  exact caseC_bridge B hL hC

/--
Terminal Case C bridge: a reconstructed Case C main package closes the branch.
-/
theorem caseC_bridge_terminal
    (B : CaseCBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n) :
    False := by
  have h := caseC_bridge B hL hC
  rcases h with ⟨P, D, ⟨X⟩⟩
  exact CaseC.CaseCMainPackage.impossible_pointwise P D X hL hC

/--
Terminal Case C bridge using the abstract branch relation from `GlobalSplit`.
-/
theorem caseC_bridge_terminal_of_falls
    (B : CaseCBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC) :
    False := by
  exact caseC_bridge_terminal B hL hC

/--
Pointwise Case C impossibility obtained from bridge data.
-/
theorem caseC_impossible_of_bridge
    (B : CaseCBridgeData) :
    ∀ n : ℕ, LehmerComposite n → InCaseC n → False := by
  intro n hL hC
  exact caseC_bridge_terminal B hL hC

/--
A Lehmer composite cannot lie in Case C once bridge reconstruction data is
available.
-/
theorem not_inCaseC_of_LehmerComposite_bridge
    (B : CaseCBridgeData)
    {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  intro hC
  exact caseC_bridge_terminal B hL hC

end Pipeline
end Lehmer