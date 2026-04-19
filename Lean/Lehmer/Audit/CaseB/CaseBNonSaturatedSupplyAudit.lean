-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedSupplyAudit.lean
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

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedSupplyTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

def dischargeSupplyData_of_discharge
    (C : Context)
    (_D : AuditCaseBDischargeData C) :
    Σ A : WitnessAccounting C, HasSupplyBound C A := by
  refine ⟨emptyWitnessAccounting C, ?_⟩
  exact hasSupplyBound_of_witnessAccounting (emptyWitnessAccounting C)

structure CaseBNonSaturatedSupplyRouting (C : Context) where
  witnessRouting : CaseBNonSaturatedWitnessAccountingRouting C
  tag : CaseBNonSaturatedSupplyTag C
  dischargeSupply :
    Option (Σ A : WitnessAccounting C, HasSupplyBound C A)

noncomputable def caseBNonSaturatedSupplyRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBNonSaturatedSupplyRouting C :=
  { witnessRouting := caseBNonSaturatedWitnessAccountingRouting_of_discharge D
    tag := CaseBNonSaturatedSupplyTag.discharge D
    dischargeSupply := some (dischargeSupplyData_of_discharge C D) }

noncomputable def caseBNonSaturatedSupplyRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBNonSaturatedSupplyRouting C :=
  { witnessRouting := caseBNonSaturatedWitnessAccountingRouting_of_entangled E
    tag := CaseBNonSaturatedSupplyTag.entangled E
    dischargeSupply := none }

noncomputable def caseBNonSaturatedSupplyRouting_of_witnessRouting
    (C : Context)
    (R : CaseBNonSaturatedWitnessAccountingRouting C) :
    CaseBNonSaturatedSupplyRouting C := by
  cases R.tag with
  | discharge D =>
      exact caseBNonSaturatedSupplyRouting_of_discharge D
  | entangled E =>
      exact caseBNonSaturatedSupplyRouting_of_entangled E

noncomputable def caseBNonSaturatedSupplyRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedSupplyRouting C :=
  caseBNonSaturatedSupplyRouting_of_witnessRouting C
    (caseBNonSaturatedWitnessAccountingRouting_of_state C hC)

theorem caseBNonSaturatedSupplyRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedSupplyRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  cases R.tag with
  | discharge D =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E =>
      exact Or.inr ⟨E, trivial⟩

theorem CaseBNonSaturatedSupplyRouting.is_discharge
    {C : Context}
    (R : CaseBNonSaturatedSupplyRouting C)
    (hnot : ¬ ∃ E : AuditCaseBEntangledStepData C, True) :
    ∃ D : AuditCaseBDischargeData C, True := by
  cases R.tag with
  | discharge D =>
      exact ⟨D, trivial⟩
  | entangled E =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem CaseBNonSaturatedSupplyRouting.is_entangled
    {C : Context}
    (R : CaseBNonSaturatedSupplyRouting C)
    (hnot : ¬ ∃ D : AuditCaseBDischargeData C, True) :
    ∃ E : AuditCaseBEntangledStepData C, True := by
  cases R.tag with
  | discharge D =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E =>
      exact ⟨E, trivial⟩

theorem CaseBNonSaturatedSupplyRouting.witnessRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedSupplyRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedWitnessAccountingRouting_sound R.witnessRouting

theorem dischargeSupply_eq_some_of_tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    ∃ P : Σ A : WitnessAccounting C, HasSupplyBound C A,
      (caseBNonSaturatedSupplyRouting_of_discharge D).dischargeSupply = some P := by
  exact ⟨dischargeSupplyData_of_discharge C D, rfl⟩

theorem dischargeSupply_eq_none_of_tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    (caseBNonSaturatedSupplyRouting_of_entangled E).dischargeSupply = none := rfl

theorem CaseBNonSaturatedSupplyRouting.dischargeSupply_eq_some_or_none
    {C : Context}
    (R : CaseBNonSaturatedSupplyRouting C) :
    (∃ P : Σ A : WitnessAccounting C, HasSupplyBound C A,
        R.dischargeSupply = some P) ∨
      R.dischargeSupply = none := by
  cases R.tag with
  | discharge D =>
      exact Or.inl ⟨dischargeSupplyData_of_discharge C D, rfl⟩
  | entangled E =>
      exact Or.inr rfl

theorem CaseBNonSaturatedSupplyRouting.dischargeSupply_some_of_dischargeTag
    {C : Context}
    (R : CaseBNonSaturatedSupplyRouting C)
    (h : ∃ D : AuditCaseBDischargeData C,
      R.tag = CaseBNonSaturatedSupplyTag.discharge D) :
    ∃ P : Σ A : WitnessAccounting C, HasSupplyBound C A,
      R.dischargeSupply = some P := by
  rcases h with ⟨D, hD⟩
  cases hD
  exact ⟨dischargeSupplyData_of_discharge C D, rfl⟩

theorem CaseBNonSaturatedSupplyRouting.dischargeSupply_none_of_entangledTag
    {C : Context}
    (R : CaseBNonSaturatedSupplyRouting C)
    (h : ∃ E : AuditCaseBEntangledStepData C,
      R.tag = CaseBNonSaturatedSupplyTag.entangled E) :
    R.dischargeSupply = none := by
  rcases h with ⟨E, hE⟩
  cases hE
  rfl

theorem exists_caseBNonSaturatedSupplyRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedSupplyRouting C, True := by
  exact ⟨caseBNonSaturatedSupplyRouting_of_state C hC, trivial⟩

theorem exists_supply_branch_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedSupplyRouting_sound
    (caseBNonSaturatedSupplyRouting_of_state C hC)

theorem exists_dischargeSupply_or_none_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ P : Σ A : WitnessAccounting C, HasSupplyBound C A,
        (caseBNonSaturatedSupplyRouting_of_state C hC).dischargeSupply = some P) ∨
      (caseBNonSaturatedSupplyRouting_of_state C hC).dischargeSupply = none := by
  exact CaseBNonSaturatedSupplyRouting.dischargeSupply_eq_some_or_none
    (caseBNonSaturatedSupplyRouting_of_state C hC)

end CaseB
end Lehmer