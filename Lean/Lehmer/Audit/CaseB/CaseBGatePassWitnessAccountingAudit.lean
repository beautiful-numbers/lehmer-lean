-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGatePassWitnessAccountingAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGatePassLockAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGatePassTraceAudit
import Lehmer.Audit.CaseB.CaseBGatePassClassificationAudit
import Lehmer.Audit.CaseB.CaseBGatePassLockAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGatePassWitnessAccountingTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

def witnessAccounting_of_gatePass
    (C : Context)
    (_G : AuditCaseBGatePassData C) :
    WitnessAccounting C :=
  emptyWitnessAccounting C

inductive CaseBGatePassWitnessAccountingRouting (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C) :
      CaseBGatePassWitnessAccountingRouting C

namespace CaseBGatePassWitnessAccountingRouting

def lockRouting
    {C : Context} :
    CaseBGatePassWitnessAccountingRouting C → CaseBGatePassLockRouting C
  | .gatePass G => caseBGatePassLockRouting_of_gatePass G

def tag
    {C : Context} :
    CaseBGatePassWitnessAccountingRouting C → CaseBGatePassWitnessAccountingTag C
  | .gatePass G => CaseBGatePassWitnessAccountingTag.gatePass G

def gatePassAccounting
    {C : Context} :
    CaseBGatePassWitnessAccountingRouting C → WitnessAccounting C
  | .gatePass G => witnessAccounting_of_gatePass C G

@[simp] theorem lockRouting_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    (CaseBGatePassWitnessAccountingRouting.gatePass G).lockRouting =
      caseBGatePassLockRouting_of_gatePass G := rfl

@[simp] theorem tag_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    (CaseBGatePassWitnessAccountingRouting.gatePass G).tag =
      CaseBGatePassWitnessAccountingTag.gatePass G := rfl

@[simp] theorem gatePassAccounting_gatePass
    {C : Context} (G : AuditCaseBGatePassData C) :
    (CaseBGatePassWitnessAccountingRouting.gatePass G).gatePassAccounting =
      witnessAccounting_of_gatePass C G := rfl

theorem exists_gatePassAccounting
    {C : Context}
    (R : CaseBGatePassWitnessAccountingRouting C) :
    ∃ A : WitnessAccounting C, R.gatePassAccounting = A := by
  cases R with
  | gatePass G =>
      exact ⟨witnessAccounting_of_gatePass C G, rfl⟩

theorem gatePassAccounting_of_gatePassTag
    {C : Context}
    (R : CaseBGatePassWitnessAccountingRouting C)
    (h : ∃ G : AuditCaseBGatePassData C,
      R.tag = CaseBGatePassWitnessAccountingTag.gatePass G) :
    ∃ A : WitnessAccounting C, R.gatePassAccounting = A := by
  cases R with
  | gatePass G =>
      exact ⟨witnessAccounting_of_gatePass C G, rfl⟩

end CaseBGatePassWitnessAccountingRouting

def caseBGatePassWitnessAccountingRouting_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBGatePassWitnessAccountingRouting C :=
  .gatePass G

noncomputable def caseBGatePassWitnessAccountingRouting_of_lockRouting
    (C : Context)
    (R : CaseBGatePassLockRouting C) :
    CaseBGatePassWitnessAccountingRouting C := by
  cases R.tag with
  | gatePass G =>
      exact caseBGatePassWitnessAccountingRouting_of_gatePass G

noncomputable def caseBGatePassWitnessAccountingRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassWitnessAccountingRouting C :=
  caseBGatePassWitnessAccountingRouting_of_lockRouting C
    (caseBGatePassLockRouting_of_state C hC)

theorem gatePassAccounting_eq_of_tag_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    (caseBGatePassWitnessAccountingRouting_of_gatePass G).gatePassAccounting =
      emptyWitnessAccounting C := rfl

theorem caseBGatePassWitnessAccountingRouting_sound
    {C : Context}
    (R : CaseBGatePassWitnessAccountingRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem CaseBGatePassWitnessAccountingRouting.is_gatePass
    {C : Context}
    (R : CaseBGatePassWitnessAccountingRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem CaseBGatePassWitnessAccountingRouting.lockRouting_sound
    {C : Context}
    (R : CaseBGatePassWitnessAccountingRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassLockRouting_sound R.lockRouting

theorem exists_caseBGatePassWitnessAccountingRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassWitnessAccountingRouting C, True := by
  exact ⟨caseBGatePassWitnessAccountingRouting_of_state C hC, trivial⟩

theorem exists_witnessAccounting_gatePass_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassWitnessAccountingRouting_sound
    (caseBGatePassWitnessAccountingRouting_of_state C hC)

theorem exists_gatePassAccounting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ A : WitnessAccounting C,
      (caseBGatePassWitnessAccountingRouting_of_state C hC).gatePassAccounting = A := by
  exact CaseBGatePassWitnessAccountingRouting.exists_gatePassAccounting
    (caseBGatePassWitnessAccountingRouting_of_state C hC)

end CaseB
end Lehmer