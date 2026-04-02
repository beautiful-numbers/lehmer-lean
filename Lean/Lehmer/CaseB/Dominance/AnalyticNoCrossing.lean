-- FILE: Lean/Lehmer/CaseB/Dominance/AnalyticNoCrossing.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.CaseB.Dominance.MajorantMc : def thm
- Lehmer.CaseB.Dominance.AnalyticMhatBarrier : thm
- Lehmer.Pivot.MreqAnalyticBridge : thm
-/

import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.MajorantMc
import Lehmer.CaseB.Dominance.AnalyticMhatBarrier
import Lehmer.Pivot.MreqAnalyticBridge

namespace Lehmer
namespace CaseB

open Lehmer.Pivot

/--
Bridge from the closed majorant `Mc` to the continuous paper majorant `Mhat`.

This theorem should be a thin structural bridge: `Mc` is the Case B majorant
written in terms of the local auxiliary quantity `yB y`, while `Mhat` is the
paper majorant evaluated directly at `y`. The intended proof is to use the
relation between `yB y` and `y`, together with monotonicity of the majorant
expression on the large range.
-/
theorem mc_le_mhat :
    ∀ y : ℕ, 3 ≤ y → Mc y ≤ Mhat (y : ℝ) := by
  intro y hy
  /-
  Intended route:
  1. prove / import a comparison `yB y ≤ y`,
  2. prove monotonicity of
       x ↦ ((20 : ℝ) / 3) * (x / log x) + 3 * (log x)^4 + 2
     on the relevant range,
  3. conclude by unfolding `Mc` and `Mhat`.
  -/
  admit

/--
Function-style export of the Appendix A strict large-range comparison.
-/
theorem mhat_lt_barrier :
    ∀ t : ℝ, TB ≤ t → Mhat t < analyticBarrier t := by
  intro t ht
  exact CaseB.mhat_lt_barrier ht

/--
Discrete ceiling bridge from `Mc` to `analyticBarrier`.

The intended proof is not to redo Appendix A here, but to consume an already
available large-range discretization gap strong enough to survive passage to
ceilings.
-/
theorem mcNat_lt_barrierCeil :
    ∀ y : ℕ, Y0 ≤ y →
      Mc y < analyticBarrier (y : ℝ) →
      McNat y < Nat.ceil (analyticBarrier (y : ℝ)) := by
  intro y hy hgap
  rw [McNat_def]
  /-
  Intended route:
  use a stronger upstream large-range gap / discretization lemma.
  A purely formal `ceil` argument from `Mc y < analyticBarrier (y : ℝ)` is
  not enough in general without additional margin.
  -/
  admit

/--
Pivot-side bridge placeholder interface.

At the current stage, `MreqAnalyticBridge.lean` no longer exports a theorem of
the exact shape required by `CaseBAnalyticBounds`; it exports the minimality
step plus a genuine sub-barrier `UBm` obligation. Therefore this file must not
pretend that the final connector is already available as a theorem.

The final `barrierCeil_le_mreq` connector should be reinstated here only once
the pivot-side analytic block is genuinely closed with the exact signature
required by `CaseBAnalyticBounds`.
-/
def HasBarrierCeilLeMreqConnector : Prop :=
  ∀ y : ℕ, Y0 ≤ y →
    Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y

end CaseB
end Lehmer