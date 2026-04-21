-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGateFailWitnessAccountingAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailLockAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGateFailTraceAudit
import Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit
import Lehmer.Audit.CaseB.CaseBGateFailLockAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGateFailWitnessAccountingTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

def witnessAccounting_of_gateFail
    (C : Context)
    (_G : AuditCaseBGateFailData C) :
    WitnessAccounting C :=
  emptyWitnessAccounting C

inductive CaseBGateFailWitnessAccountingRouting (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C) :
      CaseBGateFailWitnessAccountingRouting C

namespace CaseBGateFailWitnessAccountingRouting

def lockRouting
    {C : Context} :
    CaseBGateFailWitnessAccountingRouting C → CaseBGateFailLockRouting C
  | .gateFail G => caseBGateFailLockRouting_of_gateFail G

def tag
    {C : Context} :
    CaseBGateFailWitnessAccountingRouting C → CaseBGateFailWitnessAccountingTag C
  | .gateFail G => CaseBGateFailWitnessAccountingTag.gateFail G

def gateFailAccounting
    {C : Context} :
    CaseBGateFailWitnessAccountingRouting C → WitnessAccounting C
  | .gateFail G => witnessAccounting_of_gateFail C G

@[simp] theorem lockRouting_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    (CaseBGateFailWitnessAccountingRouting.gateFail G).lockRouting =
      caseBGateFailLockRouting_of_gateFail G := rfl

@[simp] theorem tag_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    (CaseBGateFailWitnessAccountingRouting.gateFail G).tag =
      CaseBGateFailWitnessAccountingTag.gateFail G := rfl

@[simp] theorem gateFailAccounting_gateFail
    {C : Context} (G : AuditCaseBGateFailData C) :
    (CaseBGateFailWitnessAccountingRouting.gateFail G).gateFailAccounting =
      witnessAccounting_of_gateFail C G := rfl

theorem exists_gateFailAccounting
    {C : Context}
    (R : CaseBGateFailWitnessAccountingRouting C) :
    ∃ A : WitnessAccounting C, R.gateFailAccounting = A := by
  cases R with
  | gateFail G =>
      exact ⟨witnessAccounting_of_gateFail C G, rfl⟩

theorem gateFailAccounting_of_gateFailTag
    {C : Context}
    (R : CaseBGateFailWitnessAccountingRouting C)
    (h : ∃ G : AuditCaseBGateFailData C,
      R.tag = CaseBGateFailWitnessAccountingTag.gateFail G) :
    ∃ A : WitnessAccounting C, R.gateFailAccounting = A := by
  cases R with
  | gateFail G =>
      exact ⟨witnessAccounting_of_gateFail C G, rfl⟩

end CaseBGateFailWitnessAccountingRouting

def caseBGateFailWitnessAccountingRouting_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailWitnessAccountingRouting C :=
  .gateFail G

noncomputable def caseBGateFailWitnessAccountingRouting_of_lockRouting
    (C : Context)
    (R : CaseBGateFailLockRouting C) :
    CaseBGateFailWitnessAccountingRouting C := by
  cases R.tag with
  | gateFail G =>
      exact caseBGateFailWitnessAccountingRouting_of_gateFail G

noncomputable def caseBGateFailWitnessAccountingRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailWitnessAccountingRouting C :=
  caseBGateFailWitnessAccountingRouting_of_lockRouting C
    (caseBGateFailLockRouting_of_state C hC)

theorem gateFailAccounting_eq_of_tag_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    (caseBGateFailWitnessAccountingRouting_of_gateFail G).gateFailAccounting =
      emptyWitnessAccounting C := rfl

theorem caseBGateFailWitnessAccountingRouting_sound
    {C : Context}
    (R : CaseBGateFailWitnessAccountingRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem CaseBGateFailWitnessAccountingRouting.is_gateFail
    {C : Context}
    (R : CaseBGateFailWitnessAccountingRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem CaseBGateFailWitnessAccountingRouting.lockRouting_sound
    {C : Context}
    (R : CaseBGateFailWitnessAccountingRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailLockRouting_sound R.lockRouting

theorem exists_caseBGateFailWitnessAccountingRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailWitnessAccountingRouting C, True := by
  exact ⟨caseBGateFailWitnessAccountingRouting_of_state C hC, trivial⟩

theorem exists_witnessAccounting_gateFail_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailWitnessAccountingRouting_sound
    (caseBGateFailWitnessAccountingRouting_of_state C hC)

theorem exists_gateFailAccounting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ A : WitnessAccounting C,
      (caseBGateFailWitnessAccountingRouting_of_state C hC).gateFailAccounting = A := by
  exact CaseBGateFailWitnessAccountingRouting.exists_gateFailAccounting
    (caseBGateFailWitnessAccountingRouting_of_state C hC)

end CaseB
end Lehmer