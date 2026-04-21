-- FILE: Lean/Lehmer/Audit/CaseBSaturatedGatePassAudit.lean
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

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBSaturatedGatePassAuditTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

inductive CaseBSaturatedGatePassAuditRouting (C : Context) : Type where
  | gatePass
      (G : AuditCaseBGatePassData C)
      (contradictionRouting : CaseBGatePassContradictionRouting C)
      (hcontr :
        contradictionRouting = caseBGatePassContradictionRouting_of_gatePass G) :
      CaseBSaturatedGatePassAuditRouting C

def caseBSaturatedGatePassAuditRouting_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBSaturatedGatePassAuditRouting C :=
  CaseBSaturatedGatePassAuditRouting.gatePass
    G
    (caseBGatePassContradictionRouting_of_gatePass G)
    rfl

noncomputable def caseBSaturatedGatePassAuditRouting_of_contradictionRouting
    (C : Context)
    (R : CaseBGatePassContradictionRouting C) :
    CaseBSaturatedGatePassAuditRouting C := by
  cases R with
  | gatePass G _ _ =>
      exact caseBSaturatedGatePassAuditRouting_of_gatePass G

noncomputable def caseBSaturatedGatePassAuditRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBSaturatedGatePassAuditRouting C :=
  caseBSaturatedGatePassAuditRouting_of_contradictionRouting C
    (caseBGatePassContradictionRouting_of_state C hC)

namespace CaseBSaturatedGatePassAuditRouting

def tag
    {C : Context} :
    CaseBSaturatedGatePassAuditRouting C → CaseBSaturatedGatePassAuditTag C
  | .gatePass G _ _ => CaseBSaturatedGatePassAuditTag.gatePass G

def contradictionRouting
    {C : Context} :
    CaseBSaturatedGatePassAuditRouting C → CaseBGatePassContradictionRouting C
  | .gatePass _ R _ => R

@[simp] theorem tag_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBGatePassContradictionRouting C)
    (hR : R = caseBGatePassContradictionRouting_of_gatePass G) :
    tag (.gatePass G R hR) = CaseBSaturatedGatePassAuditTag.gatePass G := rfl

@[simp] theorem contradictionRouting_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBGatePassContradictionRouting C)
    (hR : R = caseBGatePassContradictionRouting_of_gatePass G) :
    contradictionRouting (.gatePass G R hR) = R := rfl

theorem contradictionRouting_sound
    {C : Context}
    (R : CaseBSaturatedGatePassAuditRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassContradictionRouting_sound R.contradictionRouting

theorem is_gatePass
    {C : Context}
    (R : CaseBSaturatedGatePassAuditRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

end CaseBSaturatedGatePassAuditRouting

theorem caseBSaturatedGatePassAuditRouting_sound
    {C : Context}
    (R : CaseBSaturatedGatePassAuditRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

theorem progress_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact exists_gatePass_of_state C hC

theorem exists_trace_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassExhaustiveTrace C, True := by
  exact ⟨caseBGatePassExhaustiveTrace_of_state C hC, trivial⟩

theorem exists_classification_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassExhaustiveTraceClassification C, True := by
  exact exists_caseBGatePassExhaustiveTraceClassification_of_state C hC

theorem exists_lock_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassLockRouting C, True := by
  exact exists_caseBGatePassLockRouting_of_state C hC

theorem exists_witness_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassWitnessAccountingRouting C, True := by
  exact exists_caseBGatePassWitnessAccountingRouting_of_state C hC

theorem exists_supply_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassSupplyRouting C, True := by
  exact exists_caseBGatePassSupplyRouting_of_state C hC

theorem exists_terminal_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassTerminalRouting C, True := by
  exact exists_caseBGatePassTerminalRouting_of_state C hC

theorem exists_contradiction_audit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassContradictionRouting C, True := by
  exact exists_caseBGatePassContradictionRouting_of_state C hC

theorem exists_saturatedGatePassAudit_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBSaturatedGatePassAuditRouting C, True := by
  exact ⟨caseBSaturatedGatePassAuditRouting_of_state C hC, trivial⟩

theorem exists_final_audit_branch_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBSaturatedGatePassAuditRouting_sound
    (caseBSaturatedGatePassAuditRouting_of_state C hC)

end CaseB
end Lehmer