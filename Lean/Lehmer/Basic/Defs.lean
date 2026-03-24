-- FILE: Lean/Lehmer/Pivot/Defs.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs

namespace Lehmer
namespace Pivot

open Lehmer.Basic

/--
`YRough y n` means that every prime divisor of `n` is at least `y`.

This is the basic roughness predicate used by the pivot layer.
-/
def YRough (y n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → y ≤ p

/--
The pivot value attached to `n`, defined as its least prime factor.

For the Lehmer problem, this is the natural pivot parameter used in the paper.
-/
def pivotVal (n : ℕ) : ℕ :=
  n.minFac

@[simp] theorem pivotVal_def (n : ℕ) :
    pivotVal n = n.minFac := rfl

@[simp] theorem yRough_def (y n : ℕ) :
    YRough y n = ∀ p : ℕ, Nat.Prime p → p ∣ n → y ≤ p := rfl

end Pivot
end Lehmer