-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGateFailSupplyAudit.lean
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

namespace Lehmer
namespace CaseB

open Lehmer.Basic

abbrev GateFailSupplyData (C : Context) := WitnessAccounting C

inductive CaseBGateFailSupplyTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

def gateFailSupplyData_of_gateFail
    (C : Context)
    (_G : AuditCaseBGateFailData C) :
    GateFailSupplyData C :=
  emptyWitnessAccounting C

inductive CaseBGateFailSupplyRouting (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C) :
      CaseBGateFailSupplyRouting C

namespace CaseBGateFailSupplyRouting

def witnessRouting
    {C : Context} :
    CaseBGateFailSupplyRouting C → CaseBGateFailWitnessAccountingRouting C
  | .gateFail G => caseBGateFailWitnessAccountingRouting_of_gateFail G

def tag
    {C : Context} :
    CaseBGateFailSupplyRouting C → CaseBGateFailSupplyTag C
  | .gateFail G => CaseBGateFailSupplyTag.gateFail G

def gateFailSupply
    {C : Context} :
    CaseBGateFailSupplyRouting C → GateFailSupplyData C
  | .gateFail G => gateFailSupplyData_of_gateFail C G

@[simp] theorem witnessRouting_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    (CaseBGateFailSupplyRouting.gateFail G).witnessRouting =
      caseBGateFailWitnessAccountingRouting_of_gateFail G := rfl

@[simp] theorem tag_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    (CaseBGateFailSupplyRouting.gateFail G).tag =
      CaseBGateFailSupplyTag.gateFail G := rfl

@[simp] theorem gateFailSupply_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    (CaseBGateFailSupplyRouting.gateFail G).gateFailSupply =
      gateFailSupplyData_of_gateFail C G := rfl

theorem exists_gateFailSupply
    {C : Context}
    (R : CaseBGateFailSupplyRouting C) :
    ∃ P : GateFailSupplyData C, R.gateFailSupply = P := by
  cases R with
  | gateFail G =>
      exact ⟨gateFailSupplyData_of_gateFail C G, rfl⟩

theorem gateFailSupply_of_gateFailTag
    {C : Context}
    (R : CaseBGateFailSupplyRouting C)
    (h : ∃ G : AuditCaseBGateFailData C,
      R.tag = CaseBGateFailSupplyTag.gateFail G) :
    ∃ P : GateFailSupplyData C, R.gateFailSupply = P := by
  cases R with
  | gateFail G =>
      exact ⟨gateFailSupplyData_of_gateFail C G, rfl⟩

end CaseBGateFailSupplyRouting

def caseBGateFailSupplyRouting_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailSupplyRouting C :=
  .gateFail G

noncomputable def caseBGateFailSupplyRouting_of_witnessRouting
    (C : Context)
    (R : CaseBGateFailWitnessAccountingRouting C) :
    CaseBGateFailSupplyRouting C := by
  cases R.tag with
  | gateFail G =>
      exact caseBGateFailSupplyRouting_of_gateFail G

noncomputable def caseBGateFailSupplyRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailSupplyRouting C :=
  caseBGateFailSupplyRouting_of_witnessRouting C
    (caseBGateFailWitnessAccountingRouting_of_state C hC)

theorem gateFailSupply_eq_of_tag_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    (caseBGateFailSupplyRouting_of_gateFail G).gateFailSupply =
      emptyWitnessAccounting C := rfl

theorem caseBGateFailSupplyRouting_sound
    {C : Context}
    (R : CaseBGateFailSupplyRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem CaseBGateFailSupplyRouting.is_gateFail
    {C : Context}
    (R : CaseBGateFailSupplyRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem CaseBGateFailSupplyRouting.witnessRouting_sound
    {C : Context}
    (R : CaseBGateFailSupplyRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailWitnessAccountingRouting_sound R.witnessRouting

theorem exists_caseBGateFailSupplyRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailSupplyRouting C, True := by
  exact ⟨caseBGateFailSupplyRouting_of_state C hC, trivial⟩

theorem exists_supply_gateFail_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailSupplyRouting_sound
    (caseBGateFailSupplyRouting_of_state C hC)

theorem exists_gateFailSupply_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ P : GateFailSupplyData C,
      (caseBGateFailSupplyRouting_of_state C hC).gateFailSupply = P := by
  exact CaseBGateFailSupplyRouting.exists_gateFailSupply
    (caseBGateFailSupplyRouting_of_state C hC)

end CaseB
end Lehmer