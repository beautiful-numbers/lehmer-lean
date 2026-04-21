-- FILE: Lean/Lehmer/Audit/CaseBNonSaturatedAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTerminal : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedContradiction : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge
import Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTerminal
import Lehmer.Audit.CaseB.CaseBNonSaturatedContradiction

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedAuditTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

inductive CaseBNonSaturatedAuditRouting (C : Context) : Type where
  | discharge
      (D : AuditCaseBDischargeData C)
      (contradictionRouting : CaseBNonSaturatedContradictionRouting C)
      (hcontr :
        contradictionRouting = caseBNonSaturatedContradictionRouting_of_discharge D) :
      CaseBNonSaturatedAuditRouting C
  | entangled
      (E : AuditCaseBEntangledStepData C)
      (contradictionRouting : CaseBNonSaturatedContradictionRouting C)
      (hcontr :
        contradictionRouting = caseBNonSaturatedContradictionRouting_of_entangled E) :
      CaseBNonSaturatedAuditRouting C

def caseBNonSaturatedAuditRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBNonSaturatedAuditRouting C :=
  CaseBNonSaturatedAuditRouting.discharge
    D
    (caseBNonSaturatedContradictionRouting_of_discharge D)
    rfl

def caseBNonSaturatedAuditRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBNonSaturatedAuditRouting C :=
  CaseBNonSaturatedAuditRouting.entangled
    E
    (caseBNonSaturatedContradictionRouting_of_entangled E)
    rfl

noncomputable def caseBNonSaturatedAuditRouting_of_contradictionRouting
    (C : Context)
    (R : CaseBNonSaturatedContradictionRouting C) :
    CaseBNonSaturatedAuditRouting C := by
  cases R with
  | discharge D _ _ =>
      exact caseBNonSaturatedAuditRouting_of_discharge D
  | entangled E _ _ =>
      exact caseBNonSaturatedAuditRouting_of_entangled E

noncomputable def caseBNonSaturatedAuditRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedAuditRouting C :=
  caseBNonSaturatedAuditRouting_of_contradictionRouting C
    (caseBNonSaturatedContradictionRouting_of_state C hC)

namespace CaseBNonSaturatedAuditRouting

def tag
    {C : Context} :
    CaseBNonSaturatedAuditRouting C → CaseBNonSaturatedAuditTag C
  | .discharge D _ _ => CaseBNonSaturatedAuditTag.discharge D
  | .entangled E _ _ => CaseBNonSaturatedAuditTag.entangled E

def contradictionRouting
    {C : Context} :
    CaseBNonSaturatedAuditRouting C → CaseBNonSaturatedContradictionRouting C
  | .discharge _ R _ => R
  | .entangled _ R _ => R

@[simp] theorem tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedContradictionRouting C)
    (hR : R = caseBNonSaturatedContradictionRouting_of_discharge D) :
    tag (.discharge D R hR) = CaseBNonSaturatedAuditTag.discharge D := rfl

@[simp] theorem tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedContradictionRouting C)
    (hR : R = caseBNonSaturatedContradictionRouting_of_entangled E) :
    tag (.entangled E R hR) = CaseBNonSaturatedAuditTag.entangled E := rfl

@[simp] theorem contradictionRouting_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedContradictionRouting C)
    (hR : R = caseBNonSaturatedContradictionRouting_of_discharge D) :
    contradictionRouting (.discharge D R hR) = R := rfl

@[simp] theorem contradictionRouting_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedContradictionRouting C)
    (hR : R = caseBNonSaturatedContradictionRouting_of_entangled E) :
    contradictionRouting (.entangled E R hR) = R := rfl

theorem contradictionRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedAuditRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedContradictionRouting_sound R.contradictionRouting

theorem is_discharge
    {C : Context}
    (R : CaseBNonSaturatedAuditRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBEntangledStepData C, True) :
    ∃ _ : AuditCaseBDischargeData C, True := by
  cases R with
  | discharge D _ _ =>
      exact ⟨D, trivial⟩
  | entangled E _ _ =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem is_entangled
    {C : Context}
    (R : CaseBNonSaturatedAuditRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBDischargeData C, True) :
    ∃ _ : AuditCaseBEntangledStepData C, True := by
  cases R with
  | discharge D _ _ =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E _ _ =>
      exact ⟨E, trivial⟩

end CaseBNonSaturatedAuditRouting

theorem caseBNonSaturatedAuditRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedAuditRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  cases R with
  | discharge D _ _ =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E _ _ =>
      exact Or.inr ⟨E, trivial⟩

theorem progress_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBExhaustiveLocalOutcome C := by
  exact AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC

theorem exists_trace_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedExhaustiveTrace C, True := by
  exact ⟨caseBNonSaturatedExhaustiveTrace_of_state C hC, trivial⟩

theorem exists_classification_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedExhaustiveTraceClassification C, True := by
  exact exists_caseBNonSaturatedExhaustiveTraceClassification_of_state C hC

theorem exists_lock_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedLockRouting C, True := by
  exact exists_caseBNonSaturatedLockRouting_of_state C hC

theorem exists_witness_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedWitnessAccountingRouting C, True := by
  exact exists_caseBNonSaturatedWitnessAccountingRouting_of_state C hC

theorem exists_supply_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedSupplyRouting C, True := by
  exact exists_caseBNonSaturatedSupplyRouting_of_state C hC

theorem exists_terminal_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedTerminalRouting C, True := by
  exact exists_caseBNonSaturatedTerminalRouting_of_state C hC

theorem exists_contradiction_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedContradictionRouting C, True := by
  exact exists_caseBNonSaturatedContradictionRouting_of_state C hC

theorem exists_nonSaturatedAudit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedAuditRouting C, True := by
  exact ⟨caseBNonSaturatedAuditRouting_of_state C hC, trivial⟩

theorem exists_final_audit_branch_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedAuditRouting_sound
    (caseBNonSaturatedAuditRouting_of_state C hC)

end CaseB
end Lehmer