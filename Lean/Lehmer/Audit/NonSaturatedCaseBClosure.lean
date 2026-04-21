-- FILE: Lean/Lehmer/Audit/NonSaturatedCaseBClosure.lean
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
- Lehmer.Audit.CaseBNonSaturatedAudit : def thm
- Lehmer.CaseB.CaseBTerminalBridge : def thm
- Lehmer.CaseB.CaseBContradiction : def thm
- Lehmer.CaseB.Dominance.NoCrossingGlobal : def thm
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
import Lehmer.Audit.CaseBNonSaturatedAudit
import Lehmer.CaseB.CaseBTerminalBridge
import Lehmer.CaseB.CaseBContradiction
import Lehmer.CaseB.Dominance.NoCrossingGlobal

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Dominance

inductive NonSaturatedCaseBClosureTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

inductive NonSaturatedCaseBClosureRouting (C : Context) : Type where
  | discharge
      (D : AuditCaseBDischargeData C)
      (audit : CaseBNonSaturatedAuditRouting C)
      (haudit : audit = caseBNonSaturatedAuditRouting_of_discharge D) :
      NonSaturatedCaseBClosureRouting C
  | entangled
      (E : AuditCaseBEntangledStepData C)
      (audit : CaseBNonSaturatedAuditRouting C)
      (haudit : audit = caseBNonSaturatedAuditRouting_of_entangled E) :
      NonSaturatedCaseBClosureRouting C

def nonSaturatedCaseBClosureRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    NonSaturatedCaseBClosureRouting C :=
  NonSaturatedCaseBClosureRouting.discharge
    D
    (caseBNonSaturatedAuditRouting_of_discharge D)
    rfl

def nonSaturatedCaseBClosureRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    NonSaturatedCaseBClosureRouting C :=
  NonSaturatedCaseBClosureRouting.entangled
    E
    (caseBNonSaturatedAuditRouting_of_entangled E)
    rfl

noncomputable def nonSaturatedCaseBClosureRouting_of_auditRouting
    (C : Context)
    (R : CaseBNonSaturatedAuditRouting C) :
    NonSaturatedCaseBClosureRouting C := by
  cases R with
  | discharge D _ _ =>
      exact nonSaturatedCaseBClosureRouting_of_discharge D
  | entangled E _ _ =>
      exact nonSaturatedCaseBClosureRouting_of_entangled E

noncomputable def nonSaturatedCaseBClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    NonSaturatedCaseBClosureRouting C :=
  nonSaturatedCaseBClosureRouting_of_auditRouting C
    (caseBNonSaturatedAuditRouting_of_state C hC)

namespace NonSaturatedCaseBClosureRouting

def tag
    {C : Context} :
    NonSaturatedCaseBClosureRouting C → NonSaturatedCaseBClosureTag C
  | .discharge D _ _ => NonSaturatedCaseBClosureTag.discharge D
  | .entangled E _ _ => NonSaturatedCaseBClosureTag.entangled E

def auditRouting
    {C : Context} :
    NonSaturatedCaseBClosureRouting C → CaseBNonSaturatedAuditRouting C
  | .discharge _ R _ => R
  | .entangled _ R _ => R

@[simp] theorem tag_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C)
    (R : CaseBNonSaturatedAuditRouting C)
    (hR : R = caseBNonSaturatedAuditRouting_of_discharge D) :
    tag (.discharge D R hR) = NonSaturatedCaseBClosureTag.discharge D := rfl

@[simp] theorem tag_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C)
    (R : CaseBNonSaturatedAuditRouting C)
    (hR : R = caseBNonSaturatedAuditRouting_of_entangled E) :
    tag (.entangled E R hR) = NonSaturatedCaseBClosureTag.entangled E := rfl

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
    (R : NonSaturatedCaseBClosureRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedAuditRouting_sound R.auditRouting

theorem is_discharge
    {C : Context}
    (R : NonSaturatedCaseBClosureRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBEntangledStepData C, True) :
    ∃ _ : AuditCaseBDischargeData C, True := by
  cases R with
  | discharge D _ _ =>
      exact ⟨D, trivial⟩
  | entangled E _ _ =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem is_entangled
    {C : Context}
    (R : NonSaturatedCaseBClosureRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBDischargeData C, True) :
    ∃ _ : AuditCaseBEntangledStepData C, True := by
  cases R with
  | discharge D _ _ =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E _ _ =>
      exact ⟨E, trivial⟩

end NonSaturatedCaseBClosureRouting

theorem nonSaturatedCaseBClosureRouting_sound
    {C : Context}
    (R : NonSaturatedCaseBClosureRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  cases R with
  | discharge D _ _ =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E _ _ =>
      exact Or.inr ⟨E, trivial⟩

theorem exists_nonSaturatedCaseBProgressAudit_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    AuditCaseBExhaustiveLocalOutcome C := by
  exact AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC

theorem exists_nonSaturatedCaseBClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : NonSaturatedCaseBClosureRouting C, True := by
  exact ⟨nonSaturatedCaseBClosureRouting_of_state C hC, trivial⟩

theorem exists_final_nonSaturatedCaseBClosure_branch_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact nonSaturatedCaseBClosureRouting_sound
    (nonSaturatedCaseBClosureRouting_of_state C hC)

theorem false_of_nonSaturatedCaseBClosureRouting
    {B : ClosedBudgetFunctions} {C : Context}
    (_R : NonSaturatedCaseBClosureRouting C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_terminalBridgeInput I hno

theorem false_of_AuditCaseBNonSaturatedState_via_terminalBridge
    {B : ClosedBudgetFunctions} {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_nonSaturatedCaseBClosureRouting
    (nonSaturatedCaseBClosureRouting_of_state C hC)
    I
    hno

theorem nonSaturatedCaseBClosure_of_state
    {B : ClosedBudgetFunctions} {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_AuditCaseBNonSaturatedState_via_terminalBridge hC I hno

end CaseB
end Lehmer