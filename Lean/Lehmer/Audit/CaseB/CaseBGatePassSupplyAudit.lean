-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGatePassSupplyAudit.lean
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

namespace Lehmer
namespace CaseB

open Lehmer.Basic

abbrev GatePassSupplyData (C : Context) := WitnessAccounting C

inductive CaseBGatePassSupplyTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

def gatePassSupplyData_of_gatePass
    (C : Context)
    (_G : AuditCaseBGatePassData C) :
    GatePassSupplyData C :=
  emptyWitnessAccounting C

inductive CaseBGatePassSupplyRouting (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C) :
      CaseBGatePassSupplyRouting C

namespace CaseBGatePassSupplyRouting

def witnessRouting
    {C : Context} :
    CaseBGatePassSupplyRouting C → CaseBGatePassWitnessAccountingRouting C
  | .gatePass G => caseBGatePassWitnessAccountingRouting_of_gatePass G

def tag
    {C : Context} :
    CaseBGatePassSupplyRouting C → CaseBGatePassSupplyTag C
  | .gatePass G => CaseBGatePassSupplyTag.gatePass G

def gatePassSupply
    {C : Context} :
    CaseBGatePassSupplyRouting C → GatePassSupplyData C
  | .gatePass G => gatePassSupplyData_of_gatePass C G

@[simp] theorem witnessRouting_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    (CaseBGatePassSupplyRouting.gatePass G).witnessRouting =
      caseBGatePassWitnessAccountingRouting_of_gatePass G := rfl

@[simp] theorem tag_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    (CaseBGatePassSupplyRouting.gatePass G).tag =
      CaseBGatePassSupplyTag.gatePass G := rfl

@[simp] theorem gatePassSupply_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    (CaseBGatePassSupplyRouting.gatePass G).gatePassSupply =
      gatePassSupplyData_of_gatePass C G := rfl

theorem gatePassSupply_eq
    {C : Context}
    (R : CaseBGatePassSupplyRouting C) :
    ∃ P : GatePassSupplyData C, R.gatePassSupply = P := by
  cases R with
  | gatePass G =>
      exact ⟨gatePassSupplyData_of_gatePass C G, rfl⟩

theorem gatePassSupply_of_gatePassTag
    {C : Context}
    (R : CaseBGatePassSupplyRouting C)
    (h : ∃ G : AuditCaseBGatePassData C,
      R.tag = CaseBGatePassSupplyTag.gatePass G) :
    ∃ P : GatePassSupplyData C, R.gatePassSupply = P := by
  cases R with
  | gatePass G =>
      exact ⟨gatePassSupplyData_of_gatePass C G, rfl⟩

end CaseBGatePassSupplyRouting

def caseBGatePassSupplyRouting_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBGatePassSupplyRouting C :=
  .gatePass G

noncomputable def caseBGatePassSupplyRouting_of_witnessRouting
    (C : Context)
    (R : CaseBGatePassWitnessAccountingRouting C) :
    CaseBGatePassSupplyRouting C := by
  cases R.tag with
  | gatePass G =>
      exact caseBGatePassSupplyRouting_of_gatePass G

noncomputable def caseBGatePassSupplyRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassSupplyRouting C :=
  caseBGatePassSupplyRouting_of_witnessRouting C
    (caseBGatePassWitnessAccountingRouting_of_state C hC)

theorem gatePassSupply_eq_of_tag_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    (caseBGatePassSupplyRouting_of_gatePass G).gatePassSupply =
      emptyWitnessAccounting C := rfl

theorem caseBGatePassSupplyRouting_sound
    {C : Context}
    (R : CaseBGatePassSupplyRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem CaseBGatePassSupplyRouting.is_gatePass
    {C : Context}
    (R : CaseBGatePassSupplyRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem CaseBGatePassSupplyRouting.witnessRouting_sound
    {C : Context}
    (R : CaseBGatePassSupplyRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassWitnessAccountingRouting_sound R.witnessRouting

theorem exists_caseBGatePassSupplyRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassSupplyRouting C, True := by
  exact ⟨caseBGatePassSupplyRouting_of_state C hC, trivial⟩

theorem exists_supply_gatePass_branch_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassSupplyRouting_sound
    (caseBGatePassSupplyRouting_of_state C hC)

theorem exists_gatePassSupply_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ P : GatePassSupplyData C,
      (caseBGatePassSupplyRouting_of_state C hC).gatePassSupply = P := by
  exact CaseBGatePassSupplyRouting.gatePassSupply_eq
    (caseBGatePassSupplyRouting_of_state C hC)

end CaseB
end Lehmer