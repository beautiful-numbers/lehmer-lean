-- FILE: Lean/Lehmer/Audit/CaseBClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.CaseAMreq : def thm
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.Contradiction : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTerminal : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedContradiction : def thm
- Lehmer.Audit.CaseBNonSaturatedAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.CaseAMreq
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.Contradiction
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge
import Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTerminal
import Lehmer.Audit.CaseB.CaseBNonSaturatedContradiction
import Lehmer.Audit.CaseBNonSaturatedAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Dominance

inductive CaseBClosureTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

inductive CaseBClosureRouting (C : Context) : Type where
  | discharge
      (D : AuditCaseBDischargeData C)
      (audit : CaseBNonSaturatedAuditRouting C)
      (haudit : audit = caseBNonSaturatedAuditRouting_of_discharge D) :
      CaseBClosureRouting C
  | entangled
      (E : AuditCaseBEntangledStepData C)
      (audit : CaseBNonSaturatedAuditRouting C)
      (haudit : audit = caseBNonSaturatedAuditRouting_of_entangled E) :
      CaseBClosureRouting C

def caseBClosureRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBClosureRouting C :=
  CaseBClosureRouting.discharge
    D
    (caseBNonSaturatedAuditRouting_of_discharge D)
    rfl

def caseBClosureRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBClosureRouting C :=
  CaseBClosureRouting.entangled
    E
    (caseBNonSaturatedAuditRouting_of_entangled E)
    rfl

noncomputable def caseBClosureRouting_of_auditRouting
    (C : Context)
    (R : CaseBNonSaturatedAuditRouting C) :
    CaseBClosureRouting C := by
  rcases caseBNonSaturatedAuditRouting_sound R with hD | hE
  · rcases hD with ⟨D, _⟩
    exact caseBClosureRouting_of_discharge D
  · rcases hE with ⟨E, _⟩
    exact caseBClosureRouting_of_entangled E

noncomputable def caseBClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBClosureRouting C :=
  caseBClosureRouting_of_auditRouting C
    (caseBNonSaturatedAuditRouting_of_state C hC)

namespace CaseBClosureRouting

def tag
    {C : Context} :
    CaseBClosureRouting C → CaseBClosureTag C
  | .discharge D _ _ => CaseBClosureTag.discharge D
  | .entangled E _ _ => CaseBClosureTag.entangled E

def auditRouting
    {C : Context} :
    CaseBClosureRouting C → CaseBNonSaturatedAuditRouting C
  | .discharge _ R _ => R
  | .entangled _ R _ => R

@[simp] theorem tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedAuditRouting C)
    (hR : R = caseBNonSaturatedAuditRouting_of_discharge D) :
    tag (.discharge D R hR) = CaseBClosureTag.discharge D := rfl

@[simp] theorem tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedAuditRouting C)
    (hR : R = caseBNonSaturatedAuditRouting_of_entangled E) :
    tag (.entangled E R hR) = CaseBClosureTag.entangled E := rfl

@[simp] theorem auditRouting_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedAuditRouting C)
    (hR : R = caseBNonSaturatedAuditRouting_of_discharge D) :
    auditRouting (.discharge D R hR) = R := rfl

@[simp] theorem auditRouting_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedAuditRouting C)
    (hR : R = caseBNonSaturatedAuditRouting_of_entangled E) :
    auditRouting (.entangled E R hR) = R := rfl

theorem auditRouting_sound
    {C : Context}
    (R : CaseBClosureRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedAuditRouting_sound R.auditRouting

theorem is_discharge
    {C : Context}
    (R : CaseBClosureRouting C)
    (hnot : ¬ ∃ E : AuditCaseBEntangledStepData C, True) :
    ∃ D : AuditCaseBDischargeData C, True := by
  cases R with
  | discharge D _ _ =>
      exact ⟨D, trivial⟩
  | entangled E _ _ =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem is_entangled
    {C : Context}
    (R : CaseBClosureRouting C)
    (hnot : ¬ ∃ D : AuditCaseBDischargeData C, True) :
    ∃ E : AuditCaseBEntangledStepData C, True := by
  cases R with
  | discharge D _ _ =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E _ _ =>
      exact ⟨E, trivial⟩

end CaseBClosureRouting

theorem caseBClosureRouting_sound
    {C : Context}
    (R : CaseBClosureRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  cases R with
  | discharge D _ _ =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E _ _ =>
      exact Or.inr ⟨E, trivial⟩

theorem exists_progress_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBExhaustiveLocalOutcome C := by
  exact AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC

theorem exists_trace_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ T : CaseBNonSaturatedExhaustiveTrace C, True := by
  exact ⟨caseBNonSaturatedExhaustiveTrace_of_state C hC, trivial⟩

theorem exists_classification_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ K : CaseBNonSaturatedExhaustiveTraceClassification C, True := by
  exact exists_caseBNonSaturatedExhaustiveTraceClassification_of_state C hC

theorem exists_lock_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedLockRouting C, True := by
  exact exists_caseBNonSaturatedLockRouting_of_state C hC

theorem exists_witness_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedWitnessAccountingRouting C, True := by
  exact exists_caseBNonSaturatedWitnessAccountingRouting_of_state C hC

theorem exists_supply_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedSupplyRouting C, True := by
  exact exists_caseBNonSaturatedSupplyRouting_of_state C hC

theorem exists_terminal_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedTerminalRouting C, True := by
  exact exists_caseBNonSaturatedTerminalRouting_of_state C hC

theorem exists_contradiction_audit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedContradictionRouting C, True := by
  exact exists_caseBNonSaturatedContradictionRouting_of_state C hC

theorem exists_caseBClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBClosureRouting C, True := by
  exact ⟨caseBClosureRouting_of_state C hC, trivial⟩

theorem exists_closed_supply
    (C : Context) :
    ∃ A : WitnessAccounting C, HasSupplyBound C A ∧ ClosedWitnessBound A := by
  refine ⟨emptyWitnessAccounting C, ?_, ?_⟩
  · simpa using hasSupplyBound_of_witnessAccounting (emptyWitnessAccounting C)
  · simpa using closedWitnessBound_empty C

theorem exists_closed_supply_of_discharge
    {C : Context}
    (_D : AuditCaseBDischargeData C) :
    ∃ A : WitnessAccounting C, HasSupplyBound C A ∧ ClosedWitnessBound A := by
  exact exists_closed_supply C

theorem false_of_AuditCaseBDischargeData
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (hdemand : MeetsPivotDemand C)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact contradiction_of_exists_data
    C
    hdemand
    (exists_closed_supply_of_discharge D)
    hlarge
    hno

theorem false_of_AuditCaseBEntangledStepData
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (hdemand : MeetsPivotDemand C)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact contradiction_of_exists_data
    C
    hdemand
    (exists_closed_supply C)
    hlarge
    hno

theorem false_of_caseBClosureRouting
    {C : Context}
    (R : CaseBClosureRouting C)
    (hdemand : MeetsPivotDemand C)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  cases R with
  | discharge D _ _ =>
      exact false_of_AuditCaseBDischargeData D hdemand hlarge hno
  | entangled E _ _ =>
      exact false_of_AuditCaseBEntangledStepData E hdemand hlarge hno

theorem false_of_AuditCaseBNonSaturatedState
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (hdemand : MeetsPivotDemand C)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact false_of_caseBClosureRouting
    (caseBClosureRouting_of_state C hC)
    hdemand
    hlarge
    hno

theorem caseBClosure_of_nonSaturatedState
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (hdemand : MeetsPivotDemand C)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact false_of_AuditCaseBNonSaturatedState hC hdemand hlarge hno

theorem false_of_AuditCaseBNonSaturatedState_of_no_entangled
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (_hnoent : ¬ ∃ E : AuditCaseBEntangledStepData C, True)
    (hdemand : MeetsPivotDemand C)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact false_of_AuditCaseBNonSaturatedState hC hdemand hlarge hno

theorem caseBClosure_of_nonSaturatedState_of_no_entangled
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (_hnoent : ¬ ∃ E : AuditCaseBEntangledStepData C, True)
    (hdemand : MeetsPivotDemand C)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact false_of_AuditCaseBNonSaturatedState hC hdemand hlarge hno

theorem exists_final_audit_branch_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBClosureRouting_sound
    (caseBClosureRouting_of_state C hC)

end CaseB
end Lehmer