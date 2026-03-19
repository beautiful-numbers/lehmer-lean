-- FILE: Lean/Lehmer/CaseC/GapClosure/ClosureBoundN.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
- Lehmer.CaseC.GapClosure.KmaxGap : def thm
-/

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
The defining ratio is well-formed under an explicit positive-gap hypothesis.
-/
theorem closureBoundN_ratio_wellformed_of_pos (y W : ℕ)
    (hpos : 0 < deltaStar y W) :
    deltaStar y W ≠ 0 := by
  exact kmaxGap_div_deltaStar_wellformed_of_pos y W hpos

/--
Interface form: once a witness bound by `N(y, W)` has been established,
it can be reused under the canonical file-local name.
-/
theorem closureBoundN_controls_witness_of_assumption
    (y W : ℕ)
    (hbound : ∀ n : ℕ, n ≤ closureBoundN y W) :
    ∀ n : ℕ, n ≤ closureBoundN y W := by
  exact hbound

/--
Equivalent paper-style formulation using the alias `N`.
-/
theorem N_controls_witness_of_assumption
    (y W : ℕ)
    (hbound : ∀ n : ℕ, n ≤ closureBoundN y W) :
    ∀ n : ℕ, n ≤ N y W := by
  simpa [N] using hbound

end GapClosure
end CaseC
end Lehmer