-- FILE: Lean/Lehmer/Audit/CaseAClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.CaseAContradiction : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.CaseAContradiction

namespace Lehmer
namespace Audit

open Lehmer.Basic
open Lehmer.Pivot

def AuditCaseACandidate (n : ℕ) : Prop :=
  LehmerComposite n

@[simp] theorem AuditCaseACandidate_def (n : ℕ) :
    AuditCaseACandidate n = LehmerComposite n := rfl

def AuditCaseAClass (n : ℕ) : Prop :=
  InCaseA n

@[simp] theorem AuditCaseAClass_def (n : ℕ) :
    AuditCaseAClass n = InCaseA n := rfl

def CaseAEmptyAudit : Prop :=
  ∀ n : ℕ, AuditCaseACandidate n → AuditCaseAClass n → False

@[simp] theorem CaseAEmptyAudit_def :
    CaseAEmptyAudit =
      (∀ n : ℕ, AuditCaseACandidate n → AuditCaseAClass n → False) := rfl

theorem audit_caseA_empty_pointwise
    {n : ℕ} (hCand : AuditCaseACandidate n) (hA : AuditCaseAClass n) :
    False := by
  exact caseA_impossible hCand hA

theorem caseA_empty_audit :
    CaseAEmptyAudit := by
  intro n hCand hA
  exact audit_caseA_empty_pointwise hCand hA

theorem no_audit_candidate_in_caseA :
    ¬ ∃ n : ℕ, AuditCaseACandidate n ∧ AuditCaseAClass n := by
  intro h
  rcases h with ⟨n, hCand, hA⟩
  exact caseA_empty_audit n hCand hA

theorem no_LehmerComposite_in_caseA :
    ¬ ∃ n : ℕ, LehmerComposite n ∧ InCaseA n := by
  intro h
  rcases h with ⟨n, hL, hA⟩
  exact caseA_impossible hL hA

theorem not_AuditCaseAClass_of_AuditCaseACandidate
    {n : ℕ} (hCand : AuditCaseACandidate n) :
    ¬ AuditCaseAClass n := by
  intro hA
  exact audit_caseA_empty_pointwise hCand hA

theorem audit_not_inCaseA_of_LehmerComposite
    {n : ℕ} (hL : LehmerComposite n) :
    ¬ InCaseA n := by
  exact Pivot.not_inCaseA_of_LehmerComposite hL

end Audit
end Lehmer