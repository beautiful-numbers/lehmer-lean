-- FILE: Lean/Lehmer/Pivot/MreqAnalyticLowerBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.MreqLargeRangePropagation : thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.MreqLargeRangePropagation

namespace Lehmer
namespace Pivot

/--
Paper-facing large-range lower bound for `mreq`.

Source in the paper:
- Appendix A.4 states that with the fixed constants `C1 = 10^-3` and
  `Y0 = 30000`, one has
    `mreq(y) > C1 * y^2 / log y`
  for every prime `y ≥ Y0`,
  after reduction to the endpoint inequality recorded at `y = Y0`.

This file is the public paper-facing facade for that final large-range output.
-/
theorem mreq_gt_C1_mul_y_sq_div_log_of_ge_Y0
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    C1 * (y : ℝ)^2 / Real.log y < (mreq y : ℝ) := by
  exact endpoint_certificate_implies_mreq_large_range hy0 hy

/--
Alias in barrier vocabulary.
-/
theorem mreq_gt_barrier_of_ge_Y0
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    barrier (y : ℝ) < (mreq y : ℝ) := by
  simpa [barrier] using mreq_gt_C1_mul_y_sq_div_log_of_ge_Y0 hy0 hy

end Pivot
end Lehmer