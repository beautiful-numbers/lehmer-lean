-- FILE: Lean/Lehmer/CaseB/CaseBClassAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.CaseBClass : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.CaseBClass

namespace Lehmer
namespace CaseB

open Lehmer.Pivot (pivotVal)

/--
Audit-facing Case B class.

This is the local semantic family audited for Case B. It is intentionally
defined through the existing local audit-facing window `WindowB`, so the audit
layer stays aligned with the mathematical Case B class while keeping a stable
API if the audit-facing window later evolves independently.
-/
def AuditCaseBClass (n : ℕ) : Prop :=
  WindowB n

@[simp] theorem AuditCaseBClass_def (n : ℕ) :
    AuditCaseBClass n = WindowB n := rfl

/--
Paper-facing semantic window for the audited Case B family.
-/
def AuditCaseBWindow (n : ℕ) : Prop :=
  Ystar ≤ pivotVal n

@[simp] theorem AuditCaseBWindow_def (n : ℕ) :
    AuditCaseBWindow n = (Ystar ≤ pivotVal n) := rfl

/--
The audited Case B class is exactly the existing mathematical Case B class.
-/
theorem audit_windowB_exact (n : ℕ) :
    AuditCaseBClass n ↔ InCaseB n := by
  rfl

/--
Semantic exactness of the audited Case B window.
-/
theorem audit_windowB_semantic_exact (n : ℕ) :
    AuditCaseBClass n ↔ Ystar ≤ pivotVal n := by
  rfl

/--
Every object classified in the audited Case B family satisfies the exact
semantic large-pivot condition.
-/
theorem audit_windowB_sound
    {n : ℕ}
    (h : AuditCaseBClass n) :
    Ystar ≤ pivotVal n := by
  simpa using h

/--
Every object satisfying the exact semantic large-pivot condition belongs to the
audited Case B family.
-/
theorem audit_windowB_complete
    {n : ℕ}
    (h : Ystar ≤ pivotVal n) :
    AuditCaseBClass n := by
  simpa using h

/--
The audited Case B family coincides with the paper-facing semantic window.
-/
theorem audit_windowB_window_exact (n : ℕ) :
    AuditCaseBClass n ↔ AuditCaseBWindow n := by
  rfl

end CaseB
end Lehmer