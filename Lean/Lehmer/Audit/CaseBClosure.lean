-- FILE: Lean/Lehmer/Audit/CaseBClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.Audit.NonSaturatedCaseBClosure : def thm
- Lehmer.Audit.CaseBGatePassClosure : def thm
- Lehmer.Audit.CaseBGateFailClosure : def thm

FILE ROLE
Thin top-level closure aggregator for the three already-closed local Case B states:
- non-saturated
- gate-pass
- gate-fail

This file must only route to the three already-established closure files.
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.Audit.NonSaturatedCaseBClosure
import Lehmer.Audit.CaseBGatePassClosure
import Lehmer.Audit.CaseBGateFailClosure

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBClosureTag (C : Context) : Type where
  | nonSaturated (hC : AuditCaseBNonSaturatedState C)
  | gatePass (hC : AuditCaseBGatePassState C)
  | gateFail (hC : AuditCaseBGateFailState C)

inductive CaseBClosureRouting (C : Context) : Type where
  | nonSaturated (hC : AuditCaseBNonSaturatedState C) :
      CaseBClosureRouting C
  | gatePass (hC : AuditCaseBGatePassState C) :
      CaseBClosureRouting C
  | gateFail (hC : AuditCaseBGateFailState C) :
      CaseBClosureRouting C

namespace CaseBClosureRouting

def tag
    {C : Context} :
    CaseBClosureRouting C → CaseBClosureTag C
  | .nonSaturated hC => CaseBClosureTag.nonSaturated hC
  | .gatePass hC => CaseBClosureTag.gatePass hC
  | .gateFail hC => CaseBClosureTag.gateFail hC

@[simp] theorem tag_nonSaturated
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C) :
    tag (.nonSaturated hC) = CaseBClosureTag.nonSaturated hC := rfl

@[simp] theorem tag_gatePass
    {C : Context}
    (hC : AuditCaseBGatePassState C) :
    tag (.gatePass hC) = CaseBClosureTag.gatePass hC := rfl

@[simp] theorem tag_gateFail
    {C : Context}
    (hC : AuditCaseBGateFailState C) :
    tag (.gateFail hC) = CaseBClosureTag.gateFail hC := rfl

theorem sound
    {C : Context}
    (R : CaseBClosureRouting C) :
    (∃ _ : AuditCaseBNonSaturatedState C, True) ∨
    (∃ _ : AuditCaseBGatePassState C, True) ∨
    (∃ _ : AuditCaseBGateFailState C, True) := by
  cases R with
  | nonSaturated hC =>
      exact Or.inl ⟨hC, trivial⟩
  | gatePass hC =>
      exact Or.inr (Or.inl ⟨hC, trivial⟩)
  | gateFail hC =>
      exact Or.inr (Or.inr ⟨hC, trivial⟩)

end CaseBClosureRouting

def caseBClosureRouting_of_nonSaturated
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBClosureRouting C :=
  .nonSaturated hC

def caseBClosureRouting_of_gatePass
    {C : Context}
    (hC : AuditCaseBGatePassState C) :
    CaseBClosureRouting C :=
  .gatePass hC

def caseBClosureRouting_of_gateFail
    {C : Context}
    (hC : AuditCaseBGateFailState C) :
    CaseBClosureRouting C :=
  .gateFail hC

@[simp] theorem caseBClosureRouting_of_nonSaturated_def
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C) :
    caseBClosureRouting_of_nonSaturated hC =
      CaseBClosureRouting.nonSaturated hC := rfl

@[simp] theorem caseBClosureRouting_of_gatePass_def
    {C : Context}
    (hC : AuditCaseBGatePassState C) :
    caseBClosureRouting_of_gatePass hC =
      CaseBClosureRouting.gatePass hC := rfl

@[simp] theorem caseBClosureRouting_of_gateFail_def
    {C : Context}
    (hC : AuditCaseBGateFailState C) :
    caseBClosureRouting_of_gateFail hC =
      CaseBClosureRouting.gateFail hC := rfl

theorem caseBClosureRouting_sound
    {C : Context}
    (R : CaseBClosureRouting C) :
    (∃ _ : AuditCaseBNonSaturatedState C, True) ∨
    (∃ _ : AuditCaseBGatePassState C, True) ∨
    (∃ _ : AuditCaseBGateFailState C, True) := by
  exact CaseBClosureRouting.sound R

theorem exists_caseBClosureRouting_of_nonSaturated
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBClosureRouting C, True := by
  exact ⟨caseBClosureRouting_of_nonSaturated hC, trivial⟩

theorem exists_caseBClosureRouting_of_gatePass
    {C : Context}
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBClosureRouting C, True := by
  exact ⟨caseBClosureRouting_of_gatePass hC, trivial⟩

theorem exists_caseBClosureRouting_of_gateFail
    {C : Context}
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBClosureRouting C, True := by
  exact ⟨caseBClosureRouting_of_gateFail hC, trivial⟩

theorem false_of_caseBClosureRouting_nonSaturated
    {B : Lehmer.CaseB.Dominance.ClosedBudgetFunctions} {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : Lehmer.CaseB.Dominance.NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_AuditCaseBNonSaturatedState_via_terminalBridge hC I hno

theorem false_of_caseBClosureRouting_gatePass
    {B : Lehmer.CaseB.Dominance.ClosedBudgetFunctions} {C : Context}
    (hC : AuditCaseBGatePassState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : Lehmer.CaseB.Dominance.NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_AuditCaseBGatePassState_via_terminalBridge hC I hno

theorem false_of_caseBClosureRouting_gateFail
    {C : Context}
    (hC : AuditCaseBGateFailState C)
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  exact false_of_AuditCaseBGateFailState_via_caseC hC I

end CaseB
end Lehmer