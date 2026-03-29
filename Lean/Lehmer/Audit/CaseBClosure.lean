-- FILE: Lean/Lehmer/Audit/CaseBClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.CaseBContradiction : thm
- Lehmer.CaseB.Dominance.NoCrossingGlobal : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.CaseBContradiction
import Lehmer.CaseB.Dominance.NoCrossingGlobal

namespace Lehmer
namespace Audit

open Lehmer.Basic
open Lehmer.CaseB

/--
Audit candidate predicate.
-/
def AuditCandidate (n : ℕ) : Prop :=
  LehmerComposite n

@[simp] theorem AuditCandidate_def (n : ℕ) :
    AuditCandidate n = LehmerComposite n := rfl

/--
Audit-facing Case B class.

This is the complete audited Case B window:
the canonical pivot lies in the large-pivot regime `Ystar ≤ P⁻(n)`.
-/
def AuditCaseBClass (n : ℕ) : Prop :=
  InCaseB n

@[simp] theorem AuditCaseBClass_def (n : ℕ) :
    AuditCaseBClass n = InCaseB n := rfl

/--
Audit certificate: the audited Case B window is exactly the mathematical
large-pivot window `Ystar ≤ P⁻(n)`.
-/
theorem audit_windowB_exact (n : ℕ) :
    AuditCaseBClass n ↔ Ystar ≤ Lehmer.Pivot.pivotVal n := by
  rfl

/--
Case B audit closure predicate.

Interpretation:
every Lehmer candidate classified in the complete audited Case B window is
ruled out.
-/
def CaseBClosureAudit : Prop :=
  ∀ n : ℕ, AuditCandidate n → AuditCaseBClass n → False

@[simp] theorem CaseBClosureAudit_def :
    CaseBClosureAudit =
      (∀ n : ℕ, AuditCandidate n → AuditCaseBClass n → False) := rfl

/--
Audit certificate: every audit candidate in the exact Case B window is ruled
out.
-/
theorem audit_windowB_empty_pointwise
    {n : ℕ}
    (hCand : AuditCandidate n)
    (hB : AuditCaseBClass n) :
    False := by
  exact caseB_impossible hCand hB no_crossing_beyond_ystar

/--
Audit certificate: the whole audited Case B window is empty.
-/
theorem caseB_closure_audit :
    CaseBClosureAudit := by
  intro n hCand hB
  exact audit_windowB_empty_pointwise hCand hB

/--
Audit certificate: no audit candidate lies in the exact Case B window.
-/
theorem no_audit_candidate_in_caseB :
    ¬ ∃ n : ℕ, AuditCandidate n ∧ AuditCaseBClass n := by
  intro h
  rcases h with ⟨n, hCand, hB⟩
  exact caseB_closure_audit n hCand hB

/--
Paper-facing audit certificate: no Lehmer composite satisfies the large-pivot
condition `Ystar ≤ P⁻(n)`.
-/
theorem no_LehmerComposite_with_largePivot :
    ¬ ∃ n : ℕ, LehmerComposite n ∧ Ystar ≤ Lehmer.Pivot.pivotVal n := by
  intro h
  rcases h with ⟨n, hL, hB⟩
  exact caseB_impossible hL hB no_crossing_beyond_ystar

/--
Pointwise paper-facing audit certificate:
every Lehmer composite fails the large-pivot condition `Ystar ≤ P⁻(n)`.
-/
theorem not_largePivot_of_LehmerComposite
    {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ Ystar ≤ Lehmer.Pivot.pivotVal n := by
  intro hB
  exact caseB_impossible hL hB no_crossing_beyond_ystar

end Audit
end Lehmer