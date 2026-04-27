-- FILE: Lean/Lehmer/Audit/CaseBGateFailClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailLockAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTerminal : def thm
- Lehmer.Audit.CaseB.CaseBGateFailContradiction : def thm
- Lehmer.Audit.CaseBGateFailAudit : def thm
- Lehmer.Audit.CaseCClosure : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGateFailTraceAudit
import Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit
import Lehmer.Audit.CaseB.CaseBGateFailLockAudit
import Lehmer.Audit.CaseB.CaseBGateFailWitnessAccountingAudit
import Lehmer.Audit.CaseB.CaseBGateFailSupplyAudit
import Lehmer.Audit.CaseB.CaseBGateFailTerminal
import Lehmer.Audit.CaseB.CaseBGateFailContradiction
import Lehmer.Audit.CaseBGateFailAudit
import Lehmer.Audit.CaseCClosure

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGateFailClosureTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

inductive CaseBGateFailClosureRouting (C : Context) : Type where
  | gateFail
      (G : AuditCaseBGateFailData C)
      (audit : CaseBGateFailAuditRouting C)
      (haudit : audit = caseBGateFailAuditRouting_of_gateFail G) :
      CaseBGateFailClosureRouting C

def caseBGateFailClosureRouting_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailClosureRouting C :=
  CaseBGateFailClosureRouting.gateFail
    G
    (caseBGateFailAuditRouting_of_gateFail G)
    rfl

noncomputable def caseBGateFailClosureRouting_of_auditRouting
    (C : Context)
    (R : CaseBGateFailAuditRouting C) :
    CaseBGateFailClosureRouting C := by
  cases R with
  | gateFail G _ _ =>
      exact caseBGateFailClosureRouting_of_gateFail G

noncomputable def caseBGateFailClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailClosureRouting C :=
  caseBGateFailClosureRouting_of_auditRouting C
    (caseBGateFailAuditRouting_of_state C hC)

namespace CaseBGateFailClosureRouting

def tag
    {C : Context} :
    CaseBGateFailClosureRouting C → CaseBGateFailClosureTag C
  | .gateFail G _ _ => CaseBGateFailClosureTag.gateFail G

def auditRouting
    {C : Context} :
    CaseBGateFailClosureRouting C → CaseBGateFailAuditRouting C
  | .gateFail _ R _ => R

@[simp] theorem tag_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailAuditRouting C)
    (hR : R = caseBGateFailAuditRouting_of_gateFail G) :
    tag (.gateFail G R hR) = CaseBGateFailClosureTag.gateFail G := rfl

@[simp] theorem auditRouting_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C)
    (R : CaseBGateFailAuditRouting C)
    (hR : R = caseBGateFailAuditRouting_of_gateFail G) :
    auditRouting (.gateFail G R hR) = R := rfl

theorem auditRouting_sound
    {C : Context}
    (R : CaseBGateFailClosureRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailAuditRouting_sound R.auditRouting

theorem is_gateFail
    {C : Context}
    (R : CaseBGateFailClosureRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

end CaseBGateFailClosureRouting

theorem caseBGateFailClosureRouting_sound
    {C : Context}
    (R : CaseBGateFailClosureRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R with
  | gateFail G _ _ =>
      exact ⟨G, trivial⟩

theorem exists_caseBGateFailClosureRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailClosureRouting C, True := by
  exact ⟨caseBGateFailClosureRouting_of_state C hC, trivial⟩

theorem exists_final_caseBGateFailClosure_branch_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailClosureRouting_sound
    (caseBGateFailClosureRouting_of_state C hC)

structure CaseBGateFailToCaseCBridgeInput (C : Context) where
  n : ℕ
  candidate : Lehmer.Audit.AuditCandidate n
  inCaseC : Lehmer.Audit.AuditCaseCClass n
  P : Lehmer.CaseC.Params
  D : Lehmer.CaseC.ClosureData P
  main : Lehmer.CaseC.CaseCMainPackage P D

@[simp] theorem CaseBGateFailToCaseCBridgeInput.n_mk
    {C : Context}
    (n : ℕ)
    (hCand : Lehmer.Audit.AuditCandidate n)
    (hC : Lehmer.Audit.AuditCaseCClass n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (CaseBGateFailToCaseCBridgeInput.mk (C := C) n hCand hC P D X).n = n := rfl

@[simp] theorem CaseBGateFailToCaseCBridgeInput.candidate_mk
    {C : Context}
    (n : ℕ)
    (hCand : Lehmer.Audit.AuditCandidate n)
    (hC : Lehmer.Audit.AuditCaseCClass n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (CaseBGateFailToCaseCBridgeInput.mk (C := C) n hCand hC P D X).candidate = hCand := rfl

@[simp] theorem CaseBGateFailToCaseCBridgeInput.inCaseC_mk
    {C : Context}
    (n : ℕ)
    (hCand : Lehmer.Audit.AuditCandidate n)
    (hC : Lehmer.Audit.AuditCaseCClass n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (CaseBGateFailToCaseCBridgeInput.mk (C := C) n hCand hC P D X).inCaseC = hC := rfl

@[simp] theorem CaseBGateFailToCaseCBridgeInput.P_mk
    {C : Context}
    (n : ℕ)
    (hCand : Lehmer.Audit.AuditCandidate n)
    (hC : Lehmer.Audit.AuditCaseCClass n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (CaseBGateFailToCaseCBridgeInput.mk (C := C) n hCand hC P D X).P = P := rfl

@[simp] theorem CaseBGateFailToCaseCBridgeInput.D_mk
    {C : Context}
    (n : ℕ)
    (hCand : Lehmer.Audit.AuditCandidate n)
    (hC : Lehmer.Audit.AuditCaseCClass n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (CaseBGateFailToCaseCBridgeInput.mk (C := C) n hCand hC P D X).D = D := rfl

@[simp] theorem CaseBGateFailToCaseCBridgeInput.main_mk
    {C : Context}
    (n : ℕ)
    (hCand : Lehmer.Audit.AuditCandidate n)
    (hC : Lehmer.Audit.AuditCaseCClass n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (CaseBGateFailToCaseCBridgeInput.mk (C := C) n hCand hC P D X).main = X := rfl

theorem false_of_caseCClosure
    {C : Context}
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  have hCand : LehmerComposite I.n := by
    simpa [Lehmer.Audit.AuditCandidate_def] using I.candidate
  have hCaseC : Lehmer.Pipeline.InCaseC I.n := by
    simpa [Lehmer.Audit.AuditCaseCClass_def] using I.inCaseC
  exact Lehmer.CaseC.caseC_impossible_from_package
    I.P I.D I.main hCand hCaseC

theorem false_of_caseBGateFailClosureRouting
    {C : Context}
    (_R : CaseBGateFailClosureRouting C)
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  exact false_of_caseCClosure I

theorem false_of_AuditCaseBGateFailState_via_caseC
    {C : Context}
    (hC : AuditCaseBGateFailState C)
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  exact false_of_caseBGateFailClosureRouting
    (caseBGateFailClosureRouting_of_state C hC)
    I

theorem caseBGateFailClosure_of_state
    {C : Context}
    (hC : AuditCaseBGateFailState C)
    (I : CaseBGateFailToCaseCBridgeInput C) :
    False := by
  exact false_of_AuditCaseBGateFailState_via_caseC hC I

end CaseB
end Lehmer