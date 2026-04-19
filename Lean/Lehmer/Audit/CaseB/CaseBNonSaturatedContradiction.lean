-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedContradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.CaseBContradiction : def thm
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTerminal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.CaseBContradiction
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedLockAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedSupplyAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTerminal

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedContradictionTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

inductive CaseBNonSaturatedContradictionRouting (C : Context) : Type where
  | discharge
      (D : AuditCaseBDischargeData C)
      (terminalRouting : CaseBNonSaturatedTerminalRouting C)
      (hterminal :
        terminalRouting = caseBNonSaturatedTerminalRouting_of_discharge D) :
      CaseBNonSaturatedContradictionRouting C
  | entangled
      (E : AuditCaseBEntangledStepData C)
      (terminalRouting : CaseBNonSaturatedTerminalRouting C)
      (hterminal :
        terminalRouting = caseBNonSaturatedTerminalRouting_of_entangled E) :
      CaseBNonSaturatedContradictionRouting C

def caseBNonSaturatedContradictionRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBNonSaturatedContradictionRouting C :=
  CaseBNonSaturatedContradictionRouting.discharge
    D
    (caseBNonSaturatedTerminalRouting_of_discharge D)
    rfl

def caseBNonSaturatedContradictionRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBNonSaturatedContradictionRouting C :=
  CaseBNonSaturatedContradictionRouting.entangled
    E
    (caseBNonSaturatedTerminalRouting_of_entangled E)
    rfl

noncomputable def caseBNonSaturatedContradictionRouting_of_terminalRouting
    (C : Context)
    (R : CaseBNonSaturatedTerminalRouting C) :
    CaseBNonSaturatedContradictionRouting C := by
  rcases caseBNonSaturatedTerminalRouting_sound R with hD | hE
  · rcases hD with ⟨D, _⟩
    exact caseBNonSaturatedContradictionRouting_of_discharge D
  · rcases hE with ⟨E, _⟩
    exact caseBNonSaturatedContradictionRouting_of_entangled E

noncomputable def caseBNonSaturatedContradictionRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedContradictionRouting C :=
  caseBNonSaturatedContradictionRouting_of_terminalRouting C
    (caseBNonSaturatedTerminalRouting_of_state C hC)

namespace CaseBNonSaturatedContradictionRouting

def tag
    {C : Context} :
    CaseBNonSaturatedContradictionRouting C → CaseBNonSaturatedContradictionTag C
  | .discharge D _ _ => CaseBNonSaturatedContradictionTag.discharge D
  | .entangled E _ _ => CaseBNonSaturatedContradictionTag.entangled E

def terminalRouting
    {C : Context} :
    CaseBNonSaturatedContradictionRouting C → CaseBNonSaturatedTerminalRouting C
  | .discharge _ R _ => R
  | .entangled _ R _ => R

@[simp] theorem tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedTerminalRouting C)
    (hR : R = caseBNonSaturatedTerminalRouting_of_discharge D) :
    tag (.discharge D R hR) = CaseBNonSaturatedContradictionTag.discharge D := rfl

@[simp] theorem tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedTerminalRouting C)
    (hR : R = caseBNonSaturatedTerminalRouting_of_entangled E) :
    tag (.entangled E R hR) = CaseBNonSaturatedContradictionTag.entangled E := rfl

@[simp] theorem terminalRouting_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedTerminalRouting C)
    (hR : R = caseBNonSaturatedTerminalRouting_of_discharge D) :
    terminalRouting (.discharge D R hR) = R := rfl

@[simp] theorem terminalRouting_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedTerminalRouting C)
    (hR : R = caseBNonSaturatedTerminalRouting_of_entangled E) :
    terminalRouting (.entangled E R hR) = R := rfl

theorem terminalRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedContradictionRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedTerminalRouting_sound R.terminalRouting

theorem is_discharge
    {C : Context}
    (R : CaseBNonSaturatedContradictionRouting C)
    (hnot : ¬ ∃ E : AuditCaseBEntangledStepData C, True) :
    ∃ D : AuditCaseBDischargeData C, True := by
  cases R with
  | discharge D _ _ =>
      exact ⟨D, trivial⟩
  | entangled E _ _ =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem is_entangled
    {C : Context}
    (R : CaseBNonSaturatedContradictionRouting C)
    (hnot : ¬ ∃ D : AuditCaseBDischargeData C, True) :
    ∃ E : AuditCaseBEntangledStepData C, True := by
  cases R with
  | discharge D _ _ =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E _ _ =>
      exact ⟨E, trivial⟩

end CaseBNonSaturatedContradictionRouting

theorem caseBNonSaturatedContradictionRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedContradictionRouting C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  cases R with
  | discharge D _ _ =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E _ _ =>
      exact Or.inr ⟨E, trivial⟩

theorem exists_caseBNonSaturatedContradictionRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ R : CaseBNonSaturatedContradictionRouting C, True := by
  exact ⟨caseBNonSaturatedContradictionRouting_of_state C hC, trivial⟩

theorem exists_contradiction_branch_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedContradictionRouting_sound
    (caseBNonSaturatedContradictionRouting_of_state C hC)

end CaseB
end Lehmer