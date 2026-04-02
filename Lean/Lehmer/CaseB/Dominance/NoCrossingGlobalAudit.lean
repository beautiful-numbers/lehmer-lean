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

/--
Audit-facing alias for the global no-crossing certificate beyond `Y*`.
-/
abbrev NoCrossingBeyondYstarAudit : Prop :=
  NoCrossingBeyondYstar

@[simp] theorem NoCrossingBeyondYstarAudit_def :
    NoCrossingBeyondYstarAudit = NoCrossingBeyondYstar := rfl

/--
Audit-facing alias for the remaining barrier connector needed to assemble the
global no-crossing certificate.
-/
abbrev BarrierToMreqConnectorAudit : Prop :=
  ∀ y : ℕ, Y0 ≤ y →
    Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y

@[simp] theorem BarrierToMreqConnectorAudit_def :
    BarrierToMreqConnectorAudit =
      (∀ y : ℕ, Y0 ≤ y →
        Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y) := rfl

/--
Audit-facing expansion of the global no-crossing certificate.
-/
theorem noCrossingBeyondYstarAudit_expand :
    NoCrossingBeyondYstarAudit ↔
      (∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt y) := by
  rfl

/--
Audit-facing expansion of the remaining barrier connector.
-/
theorem barrierToMreqConnectorAudit_expand :
    BarrierToMreqConnectorAudit ↔
      (∀ y : ℕ, Y0 ≤ y →
        Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y) := by
  rfl

/--
Audit-facing re-export of the analytic bounds assembly.

This makes explicit that the current global no-crossing assembly remains
conditional on the final pivot-side barrier connector.
-/
theorem caseB_analyticBoundsAudit
    (hbarrier : BarrierToMreqConnectorAudit) :
    CaseBAnalyticBounds := by
  exact caseB_analyticBounds hbarrier

/--
Audit-facing re-export of the global no-crossing assembly.

This theorem intentionally keeps the remaining connector explicit: in the
current state, the global no-crossing certificate is obtained only once the
barrier-to-`mreq` comparison is supplied.
-/
theorem no_crossing_beyond_ystarAudit
    (hbarrier : BarrierToMreqConnectorAudit) :
    NoCrossingBeyondYstarAudit := by
  exact no_crossing_beyond_ystar hbarrier

/--
Audit-facing elimination of the global no-crossing certificate to a local pivot.
-/
theorem noCrossingAt_of_NoCrossingBeyondYstarAudit
    (h : NoCrossingBeyondYstarAudit)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt y := by
  exact h y hy hp

/--
Audit-facing elimination of the global no-crossing certificate to the expanded
inequality `McNat y < mreq y`.
-/
theorem McNat_lt_mreq_of_NoCrossingBeyondYstarAudit
    (h : NoCrossingBeyondYstarAudit)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    McNat y < mreq y := by
  exact noCrossingAt_of_noCrossingBeyondYstar h hy hp

/--
Audit-facing local elimination from the assembled global no-crossing
certificate under the remaining barrier connector.
-/
theorem noCrossingAt_of_barrierConnectorAudit
    (hbarrier : BarrierToMreqConnectorAudit)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt y := by
  exact noCrossingAt_of_NoCrossingBeyondYstarAudit
    (no_crossing_beyond_ystarAudit hbarrier) hy hp

/--
Audit-facing local inequality extraction from the assembled global no-crossing
certificate under the remaining barrier connector.
-/
theorem McNat_lt_mreq_of_barrierConnectorAudit
    (hbarrier : BarrierToMreqConnectorAudit)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    McNat y < mreq y := by
  exact McNat_lt_mreq_of_NoCrossingBeyondYstarAudit
    (no_crossing_beyond_ystarAudit hbarrier) hy hp

end CaseB
end Lehmer