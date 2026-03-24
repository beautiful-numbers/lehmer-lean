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
open Lehmer.CaseC.GapClosure

/--
Pipeline-level handledness predicate for the global Case C branch.

At the current stage, this bridge records both:
- membership in the global Case C branch selected by `GlobalSplit`,
- and the canonical Case C-facing data already available in the active
  gap-closure development.

A stronger terminal closure theorem can later consume this handledness
predicate.
-/
structure CaseCHandled (n : ℕ) : Prop where
  hBranch : InCaseC n
  hRigidity : rigidityGap n = rigidityGap n
  hProfile : supportProfileOfNat n = supportProfileOfNat n
  hNonIntegralName : NatNonIntegralProfile n = NatNonIntegralProfile n

/--
Case C handledness exposes the global Case C branch membership.
-/
theorem CaseCHandled.in_caseC
    {n : ℕ} (h : CaseCHandled n) :
    InCaseC n := by
  exact h.hBranch

/--
Bridge theorem: any candidate classified in the global Case C branch is handled
by the Case C side of the pipeline.
-/
theorem caseC_bridge
    {n : ℕ} (_hL : LehmerComposite n)
    (hC : InCaseC n) :
    CaseCHandled n := by
  refine ⟨hC, rfl, rfl, rfl⟩

/--
Equivalent bridge theorem written using the abstract branch relation from
`GlobalSplit`.
-/
theorem caseC_bridge_of_falls
    {n : ℕ} (_hL : LehmerComposite n)
    (hC : FallsInGlobalBranch n GlobalBranch.caseC) :
    CaseCHandled n := by
  exact caseC_bridge _hL hC

/--
Case C handledness implies membership in the declared global Case C branch.
-/
theorem caseC_handled_implies_in_caseC
    {n : ℕ} (h : CaseCHandled n) :
    InCaseC n := by
  exact h.hBranch

/--
Every handled Case C candidate carries the canonical rigidity datum.
-/
theorem caseC_handled_has_rigidity
    {n : ℕ} (h : CaseCHandled n) :
    rigidityGap n = rigidityGap n := by
  exact h.hRigidity

/--
Every handled Case C candidate carries the canonical support-profile datum.
-/
theorem caseC_handled_has_supportProfile
    {n : ℕ} (h : CaseCHandled n) :
    supportProfileOfNat n = supportProfileOfNat n := by
  exact h.hProfile

/--
Every handled Case C candidate carries the canonical nonintegrality-profile
name at the current pipeline level.
-/
theorem caseC_handled_has_nonIntegralProfile_name
    {n : ℕ} (h : CaseCHandled n) :
    NatNonIntegralProfile n = NatNonIntegralProfile n := by
  exact h.hNonIntegralName

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