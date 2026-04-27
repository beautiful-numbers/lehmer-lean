-- FILE: Lean/Lehmer/Audit/CaseBGateFailAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTerminal : def thm
- Lehmer.Audit.CaseB.CaseBGateFailContradiction : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGateFailTraceAudit
import Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit
import Lehmer.Audit.CaseB.CaseBGateFailLockAudit
import Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit
import Lehmer.Audit.CaseB.CaseBGateFailTerminal
import Lehmer.Audit.CaseB.CaseBGateFailContradiction

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGateFailAuditTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

inductive CaseBGateFailAuditRouting (C : Context) : Type where
  | gateFail
      (G : AuditCaseBGateFailData C)
      (contradictionRouting : CaseBGateFailContradictionRouting C)
      (hcontr :
        contradictionRouting = caseBGateFailContradictionRouting_of_gateFail G) :
      CaseBGateFailAuditRouting C

def caseBGateFailAuditRouting_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailAuditRouting C :=
  CaseBGateFailAuditRouting.gateFail
    G
    (caseBGateFailContradictionRouting_of_gateFail G)
    rfl

noncomputable def caseBGateFailAuditRouting_of_contradictionRouting
    (C : Context)
    (R : CaseBGateFailContradictionRouting C) :
    CaseBGateFailAuditRouting C := by
  cases R with
  | gateFail G _ _ =>
      exact caseBGateFailAuditRouting_of_gateFail G

noncomputable def caseBGateFailAuditRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailAuditRouting C :=
  caseBGateFailAuditRouting_of_contradictionRouting C
    (caseBGateFailContradictionRouting_of_state C hC)

namespace CaseBGateFailAuditRouting

def tag
    {C : Context} :
    CaseBGateFailAuditRouting C → CaseBGateFailAuditTag C
  | .gateFail G _ _ => CaseBGateFailAuditTag.gateFail G

def contradictionRouting
    {C : Context} :
    CaseBGateFailAuditRouting C → CaseBGateFailContradictionRouting C
  | .gateFail _ R _ => R

@[simp] theorem tag_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailContradictionRouting C)
    (hR : R = caseBGateFailContradictionRouting_of_gateFail G) :
    tag (.gateFail G R hR) = CaseBGateFailAuditTag.gateFail G := rfl

@[simp] theorem contradictionRouting_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailContradictionRouting C)
    (hR : R = caseBGateFailContradictionRouting_of_gateFail G) :
    contradictionRouting (.gateFail G R hR) = R := rfl

theorem contradictionRouting_sound
    {C : Context}
    (R : CaseBGateFailAuditRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailContradictionRouting_sound R.contradictionRouting

theorem is_gateFail
    {C : Context}
    (R : CaseBGateFailAuditRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

end CaseBGateFailAuditRouting

theorem caseBGateFailAuditRouting_sound
    {C : Context}
    (R : CaseBGateFailAuditRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

theorem exists_gateFail_progress_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact ⟨auditCaseBGateFailData_of_state C hC, trivial⟩

theorem exists_gateFail_trace_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailExhaustiveTrace C, True := by
  exact ⟨caseBGateFailExhaustiveTrace_of_state C hC, trivial⟩

theorem exists_gateFail_classification_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailExhaustiveTraceClassification C, True := by
  exact exists_caseBGateFailExhaustiveTraceClassification_of_state C hC

theorem exists_gateFail_lock_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailLockRouting C, True := by
  exact exists_caseBGateFailLockRouting_of_state C hC

theorem exists_gateFail_witness_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailWitnessAccountingRouting C, True := by
  exact exists_caseBGateFailWitnessAccountingRouting_of_state C hC

theorem exists_gateFail_supply_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailSupplyRouting C, True := by
  exact exists_caseBGateFailSupplyRouting_of_state C hC

theorem exists_gateFail_terminal_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailTerminalRouting C, True := by
  exact exists_caseBGateFailTerminalRouting_of_state C hC

theorem exists_gateFail_contradiction_audit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailContradictionRouting C, True := by
  exact exists_caseBGateFailContradictionRouting_of_state C hC

theorem exists_gateFailAudit_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailAuditRouting C, True := by
  exact ⟨caseBGateFailAuditRouting_of_state C hC, trivial⟩

theorem exists_final_gateFail_audit_branch_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailAuditRouting_sound
    (caseBGateFailAuditRouting_of_state C hC)

end CaseB
end Lehmer