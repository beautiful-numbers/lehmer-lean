-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGatePassTerminal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassSupplyAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGatePassTraceAudit
import Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit
import Lehmer.Audit.CaseB.CaseBGatePassLockAudit
import Lehmer.Audit.CaseB.CaseBGatePassWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBGatePassSupplyAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGatePassTerminalTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

inductive CaseBGatePassTerminalRouting (C : Context) : Type where
  | gatePass
      (G : AuditCaseBGatePassData C)
      (supplyRouting : CaseBGatePassSupplyRouting C)
      (hsupply :
        supplyRouting = caseBGatePassSupplyRouting_of_gatePass G) :
      CaseBGatePassTerminalRouting C

def caseBGatePassTerminalRouting_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBGatePassTerminalRouting C :=
  CaseBGatePassTerminalRouting.gatePass
    G
    (caseBGatePassSupplyRouting_of_gatePass G)
    rfl

noncomputable def caseBGatePassTerminalRouting_of_supplyRouting
    (C : Context)
    (R : CaseBGatePassSupplyRouting C) :
    CaseBGatePassTerminalRouting C := by
  cases R with
  | gatePass G =>
      exact caseBGatePassTerminalRouting_of_gatePass G

noncomputable def caseBGatePassTerminalRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassTerminalRouting C :=
  caseBGatePassTerminalRouting_of_supplyRouting C
    (caseBGatePassSupplyRouting_of_state C hC)

namespace CaseBGatePassTerminalRouting

def tag
    {C : Context} :
    CaseBGatePassTerminalRouting C → CaseBGatePassTerminalTag C
  | .gatePass G _ _ => CaseBGatePassTerminalTag.gatePass G

def supplyRouting
    {C : Context} :
    CaseBGatePassTerminalRouting C → CaseBGatePassSupplyRouting C
  | .gatePass _ R _ => R

def gatePassTerminal
    {C : Context} :
    CaseBGatePassTerminalRouting C → GatePassSupplyData C
  | .gatePass G _ _ =>
      (caseBGatePassSupplyRouting_of_gatePass G).gatePassSupply

@[simp] theorem tag_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBGatePassSupplyRouting C)
    (hR : R = caseBGatePassSupplyRouting_of_gatePass G) :
    tag (.gatePass G R hR) = CaseBGatePassTerminalTag.gatePass G := rfl

@[simp] theorem supplyRouting_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBGatePassSupplyRouting C)
    (hR : R = caseBGatePassSupplyRouting_of_gatePass G) :
    supplyRouting (.gatePass G R hR) = R := rfl

theorem gatePassTerminal_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBGatePassSupplyRouting C)
    (hR : R = caseBGatePassSupplyRouting_of_gatePass G) :
    gatePassTerminal (.gatePass G R hR) =
      (caseBGatePassSupplyRouting_of_gatePass G).gatePassSupply := rfl

theorem supplyRouting_sound
    {C : Context}
    (R : CaseBGatePassTerminalRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassSupplyRouting_sound R.supplyRouting

theorem gatePassTerminal_eq_supplyRouting
    {C : Context}
    (R : CaseBGatePassTerminalRouting C) :
    R.gatePassTerminal = R.supplyRouting.gatePassSupply := by
  cases R with
  | gatePass _ _ hR =>
      cases hR
      rfl

theorem exists_gatePassTerminal
    {C : Context}
    (R : CaseBGatePassTerminalRouting C) :
    ∃ P : GatePassSupplyData C, R.gatePassTerminal = P := by
  cases R with
  | gatePass G _ hR =>
      cases hR
      exact ⟨gatePassSupplyData_of_gatePass C G, rfl⟩

theorem gatePassTerminal_of_gatePassTag
    {C : Context}
    (R : CaseBGatePassTerminalRouting C)
    (h : ∃ G : AuditCaseBGatePassData C,
      R.tag = CaseBGatePassTerminalTag.gatePass G) :
    ∃ P : GatePassSupplyData C, R.gatePassTerminal = P := by
  cases R with
  | gatePass G _ hR =>
      cases hR
      exact ⟨gatePassSupplyData_of_gatePass C G, rfl⟩

theorem is_gatePass
    {C : Context}
    (R : CaseBGatePassTerminalRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

end CaseBGatePassTerminalRouting

theorem caseBGatePassTerminalRouting_sound
    {C : Context}
    (R : CaseBGatePassTerminalRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

theorem gatePassTerminal_eq_of_tag_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    (caseBGatePassTerminalRouting_of_gatePass G).gatePassTerminal =
      gatePassSupplyData_of_gatePass C G := by
  rfl

theorem exists_caseBGatePassTerminalRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassTerminalRouting C, True := by
  exact ⟨caseBGatePassTerminalRouting_of_state C hC, trivial⟩

theorem exists_terminal_gatePass_branch_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassTerminalRouting_sound
    (caseBGatePassTerminalRouting_of_state C hC)

theorem exists_gatePassTerminal_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ P : GatePassSupplyData C,
      (caseBGatePassTerminalRouting_of_state C hC).gatePassTerminal = P := by
  exact CaseBGatePassTerminalRouting.exists_gatePassTerminal
    (caseBGatePassTerminalRouting_of_state C hC)

end CaseB
end Lehmer