-- FILE: Lean/Lehmer/Pivot/MreqAnalyticBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pivot.MreqAnalytic : def thm

FILE ROLE
This file is the internal Lean bridge from the minimality definition of `mreq`
to a discretized lower bound shape.

More precisely, the output proved here is of the internal bridge-shape form
  Nat.ceil (barrier (y : ℝ)) ≤ mreq y,
under two genuine analytic inputs:
- existence of a threshold witness for `mreq y`,
- control of `UBm y m` below the discretized barrier.

Paper-facing note:
- This is NOT yet the public paper-facing statement of Lemma 3.4.
- The paper-facing output expected higher up is of the form
    C1 * y^2 / log y < mreq(y),
  not the discretized bridge-shape proved here.
- Accordingly, this file proves only the minimality bridge step; it does not
  by itself internalize the full large-range analytic proof from the paper.
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
minimality argument. It is an internal arithmetic helper for the discretized
bridge-shape and is not itself a paper-facing pivot theorem.
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
    rw [C1_def]
    positivity
  have hbar : 0 < barrier (y : ℝ) := by
    dsimp [barrier]
    positivity
  have hceil_real : (0 : ℝ) < (Nat.ceil (barrier (y : ℝ)) : ℝ) := by
    exact lt_of_lt_of_le hbar (Nat.le_ceil _)
  exact_mod_cast hceil_real

/--
Minimality bridge in discretized form.

If:
1. some threshold witness exists for `mreq y`, and
2. every index below the discretized barrier stays at or below `2`,

then the discretized barrier is bounded by `mreq y`.

This is an internal Lean bridge-shape theorem:
  `Nat.ceil (barrier (y : ℝ)) ≤ mreq y`.

It is not yet the public paper-facing analytic lower bound on `mreq(y)`.
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
Discretized pivot bridge from analytic input to `mreq`.

This theorem is intentionally parameterized by the genuine inputs needed to
conclude the bridge:

1. existence of a threshold witness for `mreq y`,
2. control of `UBm y m` below the discretized barrier.

Output:
  `Nat.ceil (barrier (y : ℝ)) ≤ mreq y`.

This remains an internal Lean interface. The corresponding paper-facing output
expected higher up is a non-discretized lower bound on `mreq(y)`, not this
`Nat.ceil` bridge-shape.
-/
theorem analyticBarrierCeil_le_mreq
    {y : ℕ}
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    Nat.ceil (barrier (y : ℝ)) ≤ mreq y := by
  exact barrierCeil_le_mreq_of_UBm_le_two_below h_exists hbelow

/--
Convenient non-curried form of the same discretized pivot bridge.

This theorem should still be read only as an internal bridge-shape lemma, not
as the final public analytic pivot theorem from the paper.
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