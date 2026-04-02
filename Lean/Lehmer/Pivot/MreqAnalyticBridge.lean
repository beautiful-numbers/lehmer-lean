-- FILE: Lean/Lehmer/Pivot/MreqAnalyticBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pivot.MreqAnalytic : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.Mreq
import Lehmer.Pivot.MreqAnalytic

namespace Lehmer
namespace Pivot

/--
Positivity of the discretized analytic barrier in the certified large range.

This is the small arithmetic lemma needed in the `mreq = 0` branch of the
minimality argument.
-/
theorem ceil_barrier_pos_of_ge_Y0
    {y : ℕ}
    (hy : Y0 ≤ y) :
    0 < Nat.ceil (barrier (y : ℝ)) := by
  have hy1 : 1 < (y : ℝ) := by
    have hY0 : (1 : ℕ) < Y0 := by
      simp [Y0]
    exact_mod_cast (lt_of_lt_of_le hY0 hy)
  have hlog : 0 < Real.log (y : ℝ) := by
    exact Real.log_pos hy1
  have hC1 : 0 < C1 := by
    have : (0 : ℝ) < (1 : ℝ) / 1000 := by norm_num
    simpa [C1_def] using this
  have hy0 : 0 < (y : ℝ) := by positivity
  have hbar : 0 < barrier (y : ℝ) := by
    dsimp [barrier]
    positivity
  exact Nat.ceil_pos.mpr hbar

/--
Minimality bridge:
if some threshold witness exists, and every index below the discretized
analytic barrier stays at or below `2`, then that barrier is bounded by `mreq y`.
-/
theorem barrierCeil_le_mreq_of_UBm_le_two_below
    {y : ℕ}
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    Nat.ceil (barrier (y : ℝ)) ≤ mreq y := by
  by_contra hlt
  have hmreq : mreq y < Nat.ceil (barrier (y : ℝ)) :=
    Nat.lt_of_not_ge hlt
  have hle : UBm y (mreq y) ≤ 2 :=
    hbelow (mreq y) hmreq
  have hgt : (2 : ℚ) < UBm y (mreq y) :=
    UBm_gt_two_at_mreq_of_exists h_exists
  exact (not_lt_of_ge hle) hgt

/--
Analytic bridge from the large-range barrier to the pivot demand threshold.

This theorem is intentionally parameterized by the genuine analytic inputs
needed to conclude the bridge:

1. existence of a threshold witness for `mreq y`,
2. control of `UBm y m` below the discretized barrier.

The present file proves only the minimality step; these inputs must come from
the real analytic layer.
-/
theorem analyticBarrierCeil_le_mreq
    {y : ℕ}
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    Nat.ceil (barrier (y : ℝ)) ≤ mreq y := by
  exact barrierCeil_le_mreq_of_UBm_le_two_below h_exists hbelow

/--
Convenient non-curried form.
-/
theorem analyticBarrierCeil_le_mreq_of_ge_Y0
    (y : ℕ)
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    Nat.ceil (barrier (y : ℝ)) ≤ mreq y := by
  exact analyticBarrierCeil_le_mreq h_exists hbelow

end Pivot
end Lehmer