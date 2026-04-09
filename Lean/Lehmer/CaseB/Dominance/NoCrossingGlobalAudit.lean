-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossingGlobalAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.CaseB.Dominance.NoCrossingGlobal : thm
-/

import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.NoCrossingGlobal

namespace Lehmer
namespace CaseB

open Lehmer.Pivot

abbrev NoCrossingBeyondYstarAudit : Prop :=
  NoCrossingBeyondYstar

@[simp] theorem NoCrossingBeyondYstarAudit_def :
    NoCrossingBeyondYstarAudit = NoCrossingBeyondYstar := rfl

@[simp] theorem NoCrossingBeyondYstarAudit_iff :
    NoCrossingBeyondYstarAudit ↔
      (∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt y) := by
  rfl

theorem noCrossingBeyondYstarAudit_of_global
    (h : NoCrossingGlobalCertificate) :
    NoCrossingBeyondYstarAudit := by
  exact h

theorem noCrossingAt_of_NoCrossingBeyondYstarAudit
    (h : NoCrossingBeyondYstarAudit)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt y := by
  exact h y hy hp

theorem M_lt_mreq_of_NoCrossingBeyondYstarAudit
    (h : NoCrossingBeyondYstarAudit)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    M y < (mreq y : ℝ) := by
  exact noCrossingAt_of_noCrossingBeyondYstar h hy hp

theorem noCrossing_ready_for_contradictionAudit
    (h : NoCrossingBeyondYstarAudit)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt y := by
  exact noCrossing_ready_for_contradiction h hy hp

end CaseB
end Lehmer