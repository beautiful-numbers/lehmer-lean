-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedTerminal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedTerminalTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

inductive CaseBNonSaturatedTerminalRouting (C : Context) : Type where
  | discharge
      (D : AuditCaseBDischargeData C)
      (supplyRouting : CaseBNonSaturatedSupplyRouting C)
      (hsupply :
        supplyRouting = caseBNonSaturatedSupplyRouting_of_discharge D) :
      CaseBNonSaturatedTerminalRouting C
  | entangled
      (E : AuditCaseBEntangledStepData C)
      (supplyRouting : CaseBNonSaturatedSupplyRouting C)
      (hsupply :
        supplyRouting = caseBNonSaturatedSupplyRouting_of_entangled E) :
      CaseBNonSaturatedTerminalRouting C

def caseBNonSaturatedTerminalRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBNonSaturatedTerminalRouting C :=
  CaseBNonSaturatedTerminalRouting.discharge
    D
    (caseBNonSaturatedSupplyRouting_of_discharge D)
    rfl

def caseBNonSaturatedTerminalRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBNonSaturatedTerminalRouting C :=
  CaseBNonSaturatedTerminalRouting.entangled
    E
    (caseBNonSaturatedSupplyRouting_of_entangled E)
    rfl

noncomputable def caseBNonSaturatedTerminalRouting_of_supplyRouting
    (C : Context)
    (R : CaseBNonSaturatedSupplyRouting C) :
    CaseBNonSaturatedTerminalRouting C := by
  cases R with
  | discharge D =>
      exact caseBNonSaturatedTerminalRouting_of_discharge D
  | entangled E =>
      exact caseBNonSaturatedTerminalRouting_of_entangled E

noncomputable def caseBNonSaturatedTerminalRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedTerminalRouting C :=
  caseBNonSaturatedTerminalRouting_of_supplyRouting C
    (caseBNonSaturatedSupplyRouting_of_state C hC)

namespace CaseBNonSaturatedTerminalRouting

def tag
    {C : Context} :
    CaseBNonSaturatedTerminalRouting C → CaseBNonSaturatedTerminalTag C
  | .discharge D _ _ => CaseBNonSaturatedTerminalTag.discharge D
  | .entangled E _ _ => CaseBNonSaturatedTerminalTag.entangled E

def supplyRouting
    {C : Context} :
    CaseBNonSaturatedTerminalRouting C → CaseBNonSaturatedSupplyRouting C
  | .discharge _ R _ => R
  | .entangled _ R _ => R

def dischargeTerminal
    {C : Context} :
    CaseBNonSaturatedTerminalRouting C → Option (DischargeSupplyData C)
  | .discharge D _ _ =>
      (caseBNonSaturatedSupplyRouting_of_discharge D).dischargeSupply
  | .entangled E _ _ =>
      (caseBNonSaturatedSupplyRouting_of_entangled E).dischargeSupply

@[simp] theorem tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedSupplyRouting C)
    (hR : R = caseBNonSaturatedSupplyRouting_of_discharge D) :
    tag (.discharge D R hR) = CaseBNonSaturatedTerminalTag.discharge D := rfl

@[simp] theorem tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedSupplyRouting C)
    (hR : R = caseBNonSaturatedSupplyRouting_of_entangled E) :
    tag (.entangled E R hR) = CaseBNonSaturatedTerminalTag.entangled E := rfl

@[simp] theorem supplyRouting_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedSupplyRouting C)
    (hR : R = caseBNonSaturatedSupplyRouting_of_discharge D) :
    supplyRouting (.discharge D R hR) = R := rfl

@[simp] theorem supplyRouting_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedSupplyRouting C)
    (hR : R = caseBNonSaturatedSupplyRouting_of_entangled E) :
    supplyRouting (.entangled E R hR) = R := rfl

theorem dischargeTerminal_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedSupplyRouting C)
    (hR : R = caseBNonSaturatedSupplyRouting_of_discharge D) :
    dischargeTerminal (.discharge D R hR) =
      (caseBNonSaturatedSupplyRouting_of_discharge D).dischargeSupply := rfl

theorem dischargeTerminal_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedSupplyRouting C)
    (hR : R = caseBNonSaturatedSupplyRouting_of_entangled E) :
    dischargeTerminal (.entangled E R hR) =
      (caseBNonSaturatedSupplyRouting_of_entangled E).dischargeSupply := rfl

theorem supplyRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedSupplyRouting_sound R.supplyRouting

theorem dischargeTerminal_eq_supplyRouting
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C) :
    R.dischargeTerminal = R.supplyRouting.dischargeSupply := by
  cases R with
  | discharge _ _ hR =>
      cases hR
      rfl
  | entangled _ _ hR =>
      cases hR
      rfl

theorem dischargeTerminal_eq_some_or_none
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C) :
    (∃ P : DischargeSupplyData C, R.dischargeTerminal = some P) ∨
      R.dischargeTerminal = none := by
  cases R with
  | discharge D _ hR =>
      cases hR
      exact Or.inl ⟨dischargeSupplyData_of_discharge C D, rfl⟩
  | entangled _ _ hR =>
      cases hR
      exact Or.inr rfl

theorem dischargeTerminal_some_of_dischargeTag
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C)
    (h : ∃ D : AuditCaseBDischargeData C,
      R.tag = CaseBNonSaturatedTerminalTag.discharge D) :
    ∃ P : DischargeSupplyData C, R.dischargeTerminal = some P := by
  cases R with
  | discharge D _ hR =>
      cases hR
      exact ⟨dischargeSupplyData_of_discharge C D, rfl⟩
  | entangled _ _ _ =>
      rcases h with ⟨D, hD⟩
      cases hD

theorem dischargeTerminal_none_of_entangledTag
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C)
    (h : ∃ E : AuditCaseBEntangledStepData C,
      R.tag = CaseBNonSaturatedTerminalTag.entangled E) :
    R.dischargeTerminal = none := by
  cases R with
  | discharge _ _ _ =>
      rcases h with ⟨E, hE⟩
      cases hE
  | entangled _ _ hR =>
      cases hR
      rfl

theorem is_discharge
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBEntangledStepData C, True) :
    ∃ _ : AuditCaseBDischargeData C, True := by
  cases R with
  | discharge D _ _ =>
      exact ⟨D, trivial⟩
  | entangled E _ _ =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem is_entangled
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBDischargeData C, True) :
    ∃ _ : AuditCaseBEntangledStepData C, True := by
  cases R with
  | discharge D _ _ =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E _ _ =>
      exact ⟨E, trivial⟩

end CaseBNonSaturatedTerminalRouting

theorem caseBNonSaturatedTerminalRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedTerminalRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  cases R with
  | discharge D _ _ =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E _ _ =>
      exact Or.inr ⟨E, trivial⟩

theorem dischargeTerminal_eq_some_of_tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    ∃ P : DischargeSupplyData C,
      (caseBNonSaturatedTerminalRouting_of_discharge D).dischargeTerminal = some P := by
  exact ⟨dischargeSupplyData_of_discharge C D, rfl⟩

theorem dischargeTerminal_eq_none_of_tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    (caseBNonSaturatedTerminalRouting_of_entangled E).dischargeTerminal = none := by
  rfl

theorem exists_caseBNonSaturatedTerminalRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedTerminalRouting C, True := by
  exact ⟨caseBNonSaturatedTerminalRouting_of_state C hC, trivial⟩

theorem exists_terminal_branch_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedTerminalRouting_sound
    (caseBNonSaturatedTerminalRouting_of_state C hC)

theorem exists_dischargeTerminal_or_none_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ P : DischargeSupplyData C,
        (caseBNonSaturatedTerminalRouting_of_state C hC).dischargeTerminal = some P) ∨
      (caseBNonSaturatedTerminalRouting_of_state C hC).dischargeTerminal = none := by
  exact CaseBNonSaturatedTerminalRouting.dischargeTerminal_eq_some_or_none
    (caseBNonSaturatedTerminalRouting_of_state C hC)

end CaseB
end Lehmer