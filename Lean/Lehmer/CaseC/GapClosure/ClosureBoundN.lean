-- FILE: Lean/Lehmer/CaseC/GapClosure/ClosureBoundN.lean
import Lehmer.Prelude
import Lehmer.CaseC.GapClosure.DeltaStar
import Lehmer.CaseC.GapClosure.KmaxGap

namespace Lehmer
namespace CaseC
namespace GapClosure

/--
The abstract Case C closure bound
`N(y, W) = ⌈KmaxGap(y, W) / DeltaStar(y, W)⌉ + 1`.

For MVP-3 we keep this as a natural-number placeholder built from the
rational ratio appearing in the paper.
-/
def closureBoundN (y W : ℕ) : ℕ :=
  Nat.ceil (kmaxGap y W / deltaStar y W) + 1

/--
Paper-style alias for the closure bound.
-/
abbrev N (y W : ℕ) : ℕ :=
  closureBoundN y W

@[simp] theorem closureBoundN_def (y W : ℕ) :
    closureBoundN y W = Nat.ceil (kmaxGap y W / deltaStar y W) + 1 := rfl

@[simp] theorem N_def (y W : ℕ) :
    N y W = closureBoundN y W := rfl

/--
The closure bound is always positive.
-/
theorem closureBoundN_pos (y W : ℕ) :
    0 < closureBoundN y W := by
  simp [closureBoundN]

/--
Hence the closure bound is nonzero.
-/
theorem closureBoundN_ne_zero (y W : ℕ) :
    closureBoundN y W ≠ 0 := by
  exact Nat.ne_of_gt (closureBoundN_pos y W)

/--
The defining ratio is well-formed in the positive-gap regime.
-/
theorem closureBoundN_ratio_wellformed (y W : ℕ) :
    deltaStar y W ≠ 0 := by
  exact kmaxGap_div_deltaStar_wellformed_placeholder y W

/--
Stable MVP-3 placeholder: any relevant Case C witness is bounded by `N(y, W)`.
This is the abstract bridge from gap estimates to finite closure.
-/
theorem closureBoundN_controls_witness_placeholder
    (y W : ℕ) :
    ∀ n : ℕ, n ≤ closureBoundN y W := by
  intro n
  sorry

/--
Equivalent paper-style formulation using the alias `N`.
-/
theorem N_controls_witness_placeholder
    (y W : ℕ) :
    ∀ n : ℕ, n ≤ N y W := by
  simpa [N] using closureBoundN_controls_witness_placeholder y W

end GapClosure
end CaseC
end Lehmer