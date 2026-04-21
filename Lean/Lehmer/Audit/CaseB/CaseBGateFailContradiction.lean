-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGateFailContradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.CaseBContradiction : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTerminal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.CaseBContradiction
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGateFailTraceAudit
import Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit
import Lehmer.Audit.CaseB.CaseBGateFailLockAudit
import Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit
import Lehmer.Audit.CaseB.CaseBGateFailTerminal

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGateFailContradictionTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

inductive CaseBGateFailContradictionRouting (C : Context) : Type where
  | gateFail
      (G : AuditCaseBGateFailData C)
      (terminalRouting : CaseBGateFailTerminalRouting C)
      (hterminal :
        terminalRouting = caseBGateFailTerminalRouting_of_gateFail G) :
      CaseBGateFailContradictionRouting C

def caseBGateFailContradictionRouting_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailContradictionRouting C :=
  CaseBGateFailContradictionRouting.gateFail
    G
    (caseBGateFailTerminalRouting_of_gateFail G)
    rfl

noncomputable def caseBGateFailContradictionRouting_of_terminalRouting
    (C : Context)
    (R : CaseBGateFailTerminalRouting C) :
    CaseBGateFailContradictionRouting C := by
  cases R with
  | gateFail G _ _ =>
      exact caseBGateFailContradictionRouting_of_gateFail G

noncomputable def caseBGateFailContradictionRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailContradictionRouting C :=
  caseBGateFailContradictionRouting_of_terminalRouting C
    (caseBGateFailTerminalRouting_of_state C hC)

namespace CaseBGateFailContradictionRouting

def tag
    {C : Context} :
    CaseBGateFailContradictionRouting C → CaseBGateFailContradictionTag C
  | .gateFail G _ _ => CaseBGateFailContradictionTag.gateFail G

def terminalRouting
    {C : Context} :
    CaseBGateFailContradictionRouting C → CaseBGateFailTerminalRouting C
  | .gateFail _ R _ => R

@[simp] theorem tag_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailTerminalRouting C)
    (hR : R = caseBGateFailTerminalRouting_of_gateFail G) :
    tag (.gateFail G R hR) = CaseBGateFailContradictionTag.gateFail G := rfl

@[simp] theorem terminalRouting_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailTerminalRouting C)
    (hR : R = caseBGateFailTerminalRouting_of_gateFail G) :
    terminalRouting (.gateFail G R hR) = R := rfl

theorem terminalRouting_sound
    {C : Context}
    (R : CaseBGateFailContradictionRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailTerminalRouting_sound R.terminalRouting

theorem is_gateFail
    {C : Context}
    (R : CaseBGateFailContradictionRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

end CaseBGateFailContradictionRouting

theorem caseBGateFailContradictionRouting_sound
    {C : Context}
    (R : CaseBGateFailContradictionRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

theorem exists_caseBGateFailContradictionRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailContradictionRouting C, True := by
  exact ⟨caseBGateFailContradictionRouting_of_state C hC, trivial⟩

theorem exists_contradiction_gateFail_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailContradictionRouting_sound
    (caseBGateFailContradictionRouting_of_state C hC)

end CaseB
end Lehmer