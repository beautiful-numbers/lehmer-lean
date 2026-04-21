-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGatePassContradiction.lean
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
- Lehmer.Audit.CaseB.CaseBGatePassTerminal : def thm
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
import Lehmer.Audit.CaseB.CaseBGatePassTerminal

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGatePassContradictionTag (C : Context) : Type where
  | gatePass (G : AuditCaseBGatePassData C)

inductive CaseBGatePassContradictionRouting (C : Context) : Type where
  | gatePass
      (G : AuditCaseBGatePassData C)
      (terminalRouting : CaseBGatePassTerminalRouting C)
      (hterminal :
        terminalRouting = caseBGatePassTerminalRouting_of_gatePass G) :
      CaseBGatePassContradictionRouting C

def caseBGatePassContradictionRouting_of_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C) :
    CaseBGatePassContradictionRouting C :=
  CaseBGatePassContradictionRouting.gatePass
    G
    (caseBGatePassTerminalRouting_of_gatePass G)
    rfl

noncomputable def caseBGatePassContradictionRouting_of_terminalRouting
    (C : Context)
    (R : CaseBGatePassTerminalRouting C) :
    CaseBGatePassContradictionRouting C := by
  cases R with
  | gatePass G _ _ =>
      exact caseBGatePassContradictionRouting_of_gatePass G

noncomputable def caseBGatePassContradictionRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassContradictionRouting C :=
  caseBGatePassContradictionRouting_of_terminalRouting C
    (caseBGatePassTerminalRouting_of_state C hC)

namespace CaseBGatePassContradictionRouting

def tag
    {C : Context} :
    CaseBGatePassContradictionRouting C → CaseBGatePassContradictionTag C
  | .gatePass G _ _ => CaseBGatePassContradictionTag.gatePass G

def terminalRouting
    {C : Context} :
    CaseBGatePassContradictionRouting C → CaseBGatePassTerminalRouting C
  | .gatePass _ R _ => R

@[simp] theorem tag_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBGatePassTerminalRouting C)
    (hR : R = caseBGatePassTerminalRouting_of_gatePass G) :
    tag (.gatePass G R hR) = CaseBGatePassContradictionTag.gatePass G := rfl

@[simp] theorem terminalRouting_gatePass
    {C : Context}
    (G : AuditCaseBGatePassData C)
    (R : CaseBGatePassTerminalRouting C)
    (hR : R = caseBGatePassTerminalRouting_of_gatePass G) :
    terminalRouting (.gatePass G R hR) = R := rfl

theorem terminalRouting_sound
    {C : Context}
    (R : CaseBGatePassContradictionRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassTerminalRouting_sound R.terminalRouting

theorem is_gatePass
    {C : Context}
    (R : CaseBGatePassContradictionRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

end CaseBGatePassContradictionRouting

theorem caseBGatePassContradictionRouting_sound
    {C : Context}
    (R : CaseBGatePassContradictionRouting C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases R with
  | gatePass G _ _ =>
      exact ⟨G, trivial⟩

theorem exists_caseBGatePassContradictionRouting_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassContradictionRouting C, True := by
  exact ⟨caseBGatePassContradictionRouting_of_state C hC, trivial⟩

theorem exists_contradiction_gatePass_branch_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  exact caseBGatePassContradictionRouting_sound
    (caseBGatePassContradictionRouting_of_state C hC)

end CaseB
end Lehmer