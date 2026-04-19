-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedWitnessAccountingAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedWitnessAccountingTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

def witnessAccounting_of_discharge
    (C : Context)
    (_D : AuditCaseBDischargeData C) :
    WitnessAccounting C :=
  emptyWitnessAccounting C

structure CaseBNonSaturatedWitnessAccountingRouting (C : Context) where
  lockRouting : CaseBNonSaturatedLockRouting C
  tag : CaseBNonSaturatedWitnessAccountingTag C
  dischargeAccounting : Option (WitnessAccounting C)

noncomputable def caseBNonSaturatedWitnessAccountingRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBNonSaturatedWitnessAccountingRouting C :=
  { lockRouting := caseBNonSaturatedLockRouting_of_discharge D
    tag := CaseBNonSaturatedWitnessAccountingTag.discharge D
    dischargeAccounting := some (witnessAccounting_of_discharge C D) }

noncomputable def caseBNonSaturatedWitnessAccountingRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBNonSaturatedWitnessAccountingRouting C :=
  { lockRouting := caseBNonSaturatedLockRouting_of_entangled E
    tag := CaseBNonSaturatedWitnessAccountingTag.entangled E
    dischargeAccounting := none }

noncomputable def caseBNonSaturatedWitnessAccountingRouting_of_lockRouting
    (C : Context)
    (R : CaseBNonSaturatedLockRouting C) :
    CaseBNonSaturatedWitnessAccountingRouting C := by
  cases R.tag with
  | discharge D =>
      exact caseBNonSaturatedWitnessAccountingRouting_of_discharge D
  | entangled E =>
      exact caseBNonSaturatedWitnessAccountingRouting_of_entangled E

noncomputable def caseBNonSaturatedWitnessAccountingRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedWitnessAccountingRouting C :=
  caseBNonSaturatedWitnessAccountingRouting_of_lockRouting C
    (caseBNonSaturatedLockRouting_of_state C hC)

theorem dischargeAccounting_eq_some_of_tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    (caseBNonSaturatedWitnessAccountingRouting_of_discharge D).dischargeAccounting =
      some (emptyWitnessAccounting C) := rfl

theorem dischargeAccounting_eq_none_of_tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    (caseBNonSaturatedWitnessAccountingRouting_of_entangled E).dischargeAccounting = none := rfl

theorem CaseBNonSaturatedWitnessAccountingRouting.dischargeAccounting_eq_some_or_none
    {C : Context}
    (R : CaseBNonSaturatedWitnessAccountingRouting C) :
    (∃ A : WitnessAccounting C, R.dischargeAccounting = some A) ∨
    R.dischargeAccounting = none := by
  cases R.tag with
  | discharge D =>
      exact Or.inl ⟨emptyWitnessAccounting C, rfl⟩
  | entangled E =>
      exact Or.inr rfl

theorem CaseBNonSaturatedWitnessAccountingRouting.dischargeAccounting_some_of_dischargeTag
    {C : Context}
    (R : CaseBNonSaturatedWitnessAccountingRouting C)
    (h : ∃ D : AuditCaseBDischargeData C,
      R.tag = CaseBNonSaturatedWitnessAccountingTag.discharge D) :
    ∃ A : WitnessAccounting C, R.dischargeAccounting = some A := by
  rcases h with ⟨D, hD⟩
  cases hD
  exact ⟨emptyWitnessAccounting C, rfl⟩

theorem CaseBNonSaturatedWitnessAccountingRouting.dischargeAccounting_none_of_entangledTag
    {C : Context}
    (R : CaseBNonSaturatedWitnessAccountingRouting C)
    (h : ∃ E : AuditCaseBEntangledStepData C,
      R.tag = CaseBNonSaturatedWitnessAccountingTag.entangled E) :
    R.dischargeAccounting = none := by
  rcases h with ⟨E, hE⟩
  cases hE
  rfl

theorem caseBNonSaturatedWitnessAccountingRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedWitnessAccountingRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  cases R.tag with
  | discharge D =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E =>
      exact Or.inr ⟨E, trivial⟩

theorem CaseBNonSaturatedWitnessAccountingRouting.is_discharge
    {C : Context}
    (R : CaseBNonSaturatedWitnessAccountingRouting C)
    (hnot : ¬ ∃ E : AuditCaseBEntangledStepData C, True) :
    ∃ D : AuditCaseBDischargeData C, True := by
  cases R.tag with
  | discharge D =>
      exact ⟨D, trivial⟩
  | entangled E =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem CaseBNonSaturatedWitnessAccountingRouting.is_entangled
    {C : Context}
    (R : CaseBNonSaturatedWitnessAccountingRouting C)
    (hnot : ¬ ∃ D : AuditCaseBDischargeData C, True) :
    ∃ E : AuditCaseBEntangledStepData C, True := by
  cases R.tag with
  | discharge D =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E =>
      exact ⟨E, trivial⟩

theorem CaseBNonSaturatedWitnessAccountingRouting.lockRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedWitnessAccountingRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedLockRouting_sound R.lockRouting

theorem exists_caseBNonSaturatedWitnessAccountingRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedWitnessAccountingRouting C, True := by
  exact ⟨caseBNonSaturatedWitnessAccountingRouting_of_state C hC, trivial⟩

theorem exists_witnessAccounting_branch_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedWitnessAccountingRouting_sound
    (caseBNonSaturatedWitnessAccountingRouting_of_state C hC)

theorem exists_dischargeAccounting_or_none_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ A : WitnessAccounting C,
        (caseBNonSaturatedWitnessAccountingRouting_of_state C hC).dischargeAccounting = some A) ∨
      (caseBNonSaturatedWitnessAccountingRouting_of_state C hC).dischargeAccounting = none := by
  exact CaseBNonSaturatedWitnessAccountingRouting.dischargeAccounting_eq_some_or_none
    (caseBNonSaturatedWitnessAccountingRouting_of_state C hC)

end CaseB
end Lehmer