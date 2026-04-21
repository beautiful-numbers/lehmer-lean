-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGateFailTerminal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGateFailTraceAudit
import Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit
import Lehmer.Audit.CaseB.CaseBGateFailLockAudit
import Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGateFailTerminalTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

inductive CaseBGateFailTerminalRouting (C : Context) : Type where
  | gateFail
      (G : AuditCaseBGateFailData C)
      (supplyRouting : CaseBGateFailSupplyRouting C)
      (hsupply :
        supplyRouting = caseBGateFailSupplyRouting_of_gateFail G) :
      CaseBGateFailTerminalRouting C

def caseBGateFailTerminalRouting_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailTerminalRouting C :=
  CaseBGateFailTerminalRouting.gateFail
    G
    (caseBGateFailSupplyRouting_of_gateFail G)
    rfl

noncomputable def caseBGateFailTerminalRouting_of_supplyRouting
    (C : Context)
    (R : CaseBGateFailSupplyRouting C) :
    CaseBGateFailTerminalRouting C := by
  cases R with
  | gateFail G =>
      exact caseBGateFailTerminalRouting_of_gateFail G

noncomputable def caseBGateFailTerminalRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailTerminalRouting C :=
  caseBGateFailTerminalRouting_of_supplyRouting C
    (caseBGateFailSupplyRouting_of_state C hC)

namespace CaseBGateFailTerminalRouting

def tag
    {C : Context} :
    CaseBGateFailTerminalRouting C → CaseBGateFailTerminalTag C
  | .gateFail G _ _ => CaseBGateFailTerminalTag.gateFail G

def supplyRouting
    {C : Context} :
    CaseBGateFailTerminalRouting C → CaseBGateFailSupplyRouting C
  | .gateFail _ R _ => R

def gateFailTerminal
    {C : Context} :
    CaseBGateFailTerminalRouting C → GateFailSupplyData C
  | .gateFail G _ _ =>
      (caseBGateFailSupplyRouting_of_gateFail G).gateFailSupply

@[simp] theorem tag_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailSupplyRouting C)
    (hR : R = caseBGateFailSupplyRouting_of_gateFail G) :
    tag (.gateFail G R hR) = CaseBGateFailTerminalTag.gateFail G := rfl

@[simp] theorem supplyRouting_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailSupplyRouting C)
    (hR : R = caseBGateFailSupplyRouting_of_gateFail G) :
    supplyRouting (.gateFail G R hR) = R := rfl

theorem gateFailTerminal_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailSupplyRouting C)
    (hR : R = caseBGateFailSupplyRouting_of_gateFail G) :
    gateFailTerminal (.gateFail G R hR) =
      (caseBGateFailSupplyRouting_of_gateFail G).gateFailSupply := rfl

theorem supplyRouting_sound
    {C : Context}
    (R : CaseBGateFailTerminalRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailSupplyRouting_sound R.supplyRouting

theorem gateFailTerminal_eq_supplyRouting
    {C : Context}
    (R : CaseBGateFailTerminalRouting C) :
    R.gateFailTerminal = R.supplyRouting.gateFailSupply := by
  cases R with
  | gateFail _ _ hR =>
      cases hR
      rfl

theorem exists_gateFailTerminal
    {C : Context}
    (R : CaseBGateFailTerminalRouting C) :
    ∃ P : GateFailSupplyData C, R.gateFailTerminal = P := by
  cases R with
  | gateFail G _ hR =>
      cases hR
      exact ⟨gateFailSupplyData_of_gateFail C G, rfl⟩

theorem gateFailTerminal_of_gateFailTag
    {C : Context}
    (R : CaseBGateFailTerminalRouting C)
    (h : ∃ G : AuditCaseBGateFailData C,
      R.tag = CaseBGateFailTerminalTag.gateFail G) :
    ∃ P : GateFailSupplyData C, R.gateFailTerminal = P := by
  cases R with
  | gateFail G _ hR =>
      cases hR
      exact ⟨gateFailSupplyData_of_gateFail C G, rfl⟩

theorem is_gateFail
    {C : Context}
    (R : CaseBGateFailTerminalRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

end CaseBGateFailTerminalRouting

theorem caseBGateFailTerminalRouting_sound
    {C : Context}
    (R : CaseBGateFailTerminalRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

theorem gateFailTerminal_eq_of_tag_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    (caseBGateFailTerminalRouting_of_gateFail G).gateFailTerminal =
      gateFailSupplyData_of_gateFail C G := by
  rfl

theorem exists_caseBGateFailTerminalRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailTerminalRouting C, True := by
  exact ⟨caseBGateFailTerminalRouting_of_state C hC, trivial⟩

theorem exists_terminal_gateFail_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailTerminalRouting_sound
    (caseBGateFailTerminalRouting_of_state C hC)

theorem exists_gateFailTerminal_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ P : GateFailSupplyData C,
      (caseBGateFailTerminalRouting_of_state C hC).gateFailTerminal = P := by
  exact CaseBGateFailTerminalRouting.exists_gateFailTerminal
    (caseBGateFailTerminalRouting_of_state C hC)

end CaseB
end Lehmer