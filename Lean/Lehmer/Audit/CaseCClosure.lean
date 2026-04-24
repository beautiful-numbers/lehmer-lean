-- FILE: Lean/Lehmer/Audit/CaseCClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.CaseC.Main : assemble
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit
import Lehmer.CaseC.Main

namespace Lehmer
namespace Audit

open Lehmer.Basic
open Lehmer.Pipeline
open Lehmer.CaseC

def AuditCandidate (n : ℕ) : Prop :=
  LehmerComposite n

@[simp] theorem AuditCandidate_def (n : ℕ) :
    AuditCandidate n = LehmerComposite n := rfl

def AuditCaseCClass (n : ℕ) : Prop :=
  InCaseC n

@[simp] theorem AuditCaseCClass_def (n : ℕ) :
    AuditCaseCClass n = InCaseC n := rfl

def CaseCEmptyAudit (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D) : Prop :=
  ∀ n : ℕ, AuditCandidate n → AuditCaseCClass n → False

@[simp] theorem CaseCEmptyAudit_def (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D) :
    CaseCEmptyAudit P D X =
      (∀ n : ℕ, AuditCandidate n → AuditCaseCClass n → False) := rfl

theorem audit_caseC_empty_pointwise
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hCand : AuditCandidate n) (hC : AuditCaseCClass n) :
    False := by
  exact caseC_impossible_from_package P D X hCand hC

theorem caseC_empty_audit
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D) :
    CaseCEmptyAudit P D X := by
  intro n hCand hC
  exact audit_caseC_empty_pointwise P D X hCand hC

theorem no_audit_candidate_in_caseC
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D) :
    ¬ ∃ n : ℕ, AuditCandidate n ∧ AuditCaseCClass n := by
  intro h
  rcases h with ⟨n, hCand, hC⟩
  exact caseC_empty_audit P D X n hCand hC

theorem no_LehmerComposite_in_caseC
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D) :
    ¬ ∃ n : ℕ, LehmerComposite n ∧ InCaseC n := by
  intro h
  rcases h with ⟨n, hL, hC⟩
  exact caseC_impossible_from_package P D X hL hC

theorem not_AuditCaseCClass_of_AuditCandidate
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hCand : AuditCandidate n) :
    ¬ AuditCaseCClass n := by
  intro hC
  exact audit_caseC_empty_pointwise P D X hCand hC

theorem audit_not_inCaseC_of_LehmerComposite
    (P : Params) (D : ClosureData P) (X : CaseCMainPackage P D)
    {n : ℕ} (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  intro hC
  exact caseC_impossible_from_package P D X hL hC

end Audit
end Lehmer