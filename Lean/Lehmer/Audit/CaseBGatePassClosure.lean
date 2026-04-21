-- FILE: Lean/Lehmer/Audit/CaseBGatePassClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassSupplyAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassTerminal : def thm
- Lehmer.Audit.CaseB.CaseBGatePassContradiction : def thm
- Lehmer.Audit.CaseBSaturatedGatePassAudit : def thm
- Lehmer.CaseB.CaseBTerminalBridge : def thm
- Lehmer.CaseB.CaseBContradiction : def thm
- Lehmer.CaseB.Dominance.NoCrossingGlobal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGatePassTraceAudit
import Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit
import Lehmer.Audit.CaseB.CaseBGatePassLockAudit
import Lehmer.Audit.CaseB.CaseBGatePassWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBGatePassSupplyAudit
import Lehmer.Audit.CaseB.CaseBGatePassTerminal
import Lehmer.Audit.CaseB.CaseBGatePassContradiction
import Lehmer.Audit.CaseBSaturatedGatePassAudit
import Lehmer.CaseB.CaseBTerminalBridge
import Lehmer.CaseB.CaseBContradiction
import Lehmer.CaseB.Dominance.NoCrossingGlobal

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Dominance

inductive CaseBGatePassClosureTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

inductive CaseBGatePassClosureRouting (C : Context) : Type where
  | gatePass
      (G : AuditCaseBGatePassData C)
      (audit : CaseBSaturatedGatePassAuditRouting C)
      (haudit : audit = caseBSaturatedGatePassAuditRouting_of_gatePass G) :
      CaseBGatePassClosureRouting C

def caseBGatePassClosureRouting_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBGatePassClosureRouting C :=
  CaseBGatePassClosureRouting.gatePass
    G
    (caseBSaturatedGatePassAuditRouting_of_gatePass G)
    rfl

noncomputable def caseBGatePassClosureRouting_of_auditRouting
    (C : Context)
    (R : CaseBSaturatedGatePassAuditRouting C) :
    CaseBGatePassClosureRouting C := by
  cases R with
  | gatePass G _ _ =>
      exact caseBGatePassClosureRouting_of_gatePass G

noncomputable def caseBGatePassClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassClosureRouting C :=
  caseBGatePassClosureRouting_of_auditRouting C
    (caseBSaturatedGatePassAuditRouting_of_state C hC)

namespace CaseBGatePassClosureRouting

def tag
    {C : Context} :
    CaseBGatePassClosureRouting C → CaseBGatePassClosureTag C
  | .gatePass G _ _ => CaseBGatePassClosureTag.gatePass G

def auditRouting
    {C : Context} :
    CaseBGatePassClosureRouting C → CaseBSaturatedGatePassAuditRouting C
  | .gatePass _ R _ => R

@[simp] theorem tag_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBSaturatedGatePassAuditRouting C)
    (hR : R = caseBSaturatedGatePassAuditRouting_of_gatePass G) :
    tag (.gatePass G R hR) = CaseBGatePassClosureTag.gatePass G := rfl

@[simp] theorem auditRouting_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBSaturatedGatePassAuditRouting C)
    (hR : R = caseBSaturatedGatePassAuditRouting_of_gatePass G) :
    auditRouting (.gatePass G R hR) = R := rfl

theorem auditRouting_sound
    {C : Context}
    (R : CaseBGatePassClosureRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBSaturatedGatePassAuditRouting_sound R.auditRouting

theorem is_gatePass
    {C : Context}
    (R : CaseBGatePassClosureRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

end CaseBGatePassClosureRouting

theorem caseBGatePassClosureRouting_sound
    {C : Context}
    (R : CaseBGatePassClosureRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

theorem exists_caseBGatePassClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassClosureRouting C, True := by
  exact ⟨caseBGatePassClosureRouting_of_state C hC, trivial⟩

theorem exists_final_caseBGatePassClosure_branch_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassClosureRouting_sound
    (caseBGatePassClosureRouting_of_state C hC)

theorem false_of_caseBGatePassClosureRouting
    {B : ClosedBudgetFunctions} {C : Context}
    (_R : CaseBGatePassClosureRouting C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_terminalBridgeInput I hno

theorem false_of_AuditCaseBGatePassState_via_terminalBridge
    {B : ClosedBudgetFunctions} {C : Context}
    (hC : AuditCaseBGatePassState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_caseBGatePassClosureRouting
    (caseBGatePassClosureRouting_of_state C hC)
    I
    hno

theorem caseBGatePassClosure_of_state
    {B : ClosedBudgetFunctions} {C : Context}
    (hC : AuditCaseBGatePassState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_AuditCaseBGatePassState_via_terminalBridge hC I hno

end CaseB
end Lehmer