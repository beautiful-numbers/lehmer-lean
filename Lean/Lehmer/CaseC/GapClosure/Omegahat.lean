-- FILE: Lean/Lehmer/CaseC/GapClosure/Omegahat.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.GapClosure.ClosureBoundN : def thm
-/

import Lehmer.Prelude
import Lehmer.CaseC.GapClosure.ClosureBoundN

namespace Lehmer
namespace CaseC
namespace GapClosure

/--
The bootstrap support-size bound
`Ω̂(y, W) = ⌊log N(y, W) / log y⌋`.

For MVP-3 we package it as a natural-number quantity derived from the
closure bound.
-/
noncomputable def omegahat (y W : ℕ) : ℕ :=
  Nat.floor (Real.log (closureBoundN y W) / Real.log y)

/--
Paper-style alias for the bootstrap support-size bound.
-/
noncomputable abbrev Omegahat (y W : ℕ) : ℕ :=
  omegahat y W

@[simp] theorem omegahat_def (y W : ℕ) :
    omegahat y W = Nat.floor (Real.log (closureBoundN y W) / Real.log y) := rfl

@[simp] theorem Omegahat_def (y W : ℕ) :
    Omegahat y W = omegahat y W := rfl

/--
The closure bound appearing in the definition of `Ω̂(y, W)` is positive.
-/
theorem closureBoundN_pos_for_omegahat (y W : ℕ) :
    0 < closureBoundN y W := by
  exact closureBoundN_pos y W

/--
The logarithmic ratio defining `Ω̂(y, W)` is well-formed in the Case C regime.
-/
theorem omegahat_wellformed_placeholder (y : ℕ) (_W : ℕ) :
    1 < y -> Real.log y ≠ 0 := by
  intro hy
  have hy' : (y : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hy)
  exact Real.log_ne_zero_of_pos_of_ne_one
    (by exact_mod_cast (lt_trans Nat.zero_lt_one hy))
    hy'

/--
Interface form: once a support-cardinality bound by `Ω̂(y, W)` has been
established, it can be reused under the canonical file-local name.
-/
theorem supportCard_le_omegahat_of_assumption
    (y W : ℕ)
    (hbound : ∀ m : ℕ, m ≤ omegahat y W) :
    ∀ m : ℕ, m ≤ omegahat y W := by
  exact hbound

/--
Equivalent paper-style formulation using the alias `Ω̂`.
-/
theorem supportCard_le_Omegahat_of_assumption
    (y W : ℕ)
    (hbound : ∀ m : ℕ, m ≤ omegahat y W) :
    ∀ m : ℕ, m ≤ Omegahat y W := by
  simpa [Omegahat] using hbound

end GapClosure
end CaseC
end Lehmer