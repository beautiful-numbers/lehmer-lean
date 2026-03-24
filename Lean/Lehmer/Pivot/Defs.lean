-- FILE: Lean/Lehmer/Pivot/Defs.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.PrimeSupport : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.PrimeSupport

namespace Lehmer
namespace Pivot

open Lehmer.Basic

/--
Canonical pivot value attached to an integer `n`.

Mathematically, this is intended to model the pivot
`y = P⁻(n)`, i.e. the least prime divisor of `n`.
At the current stage we realize it by `Nat.minFac`.
-/
def pivotVal (n : ℕ) : ℕ :=
  n.minFac

@[simp] theorem pivotVal_def (n : ℕ) :
    pivotVal n = n.minFac := rfl

/--
`YRough y n` means that every prime divisor of `n` is at least `y`.

This is the canonical roughness predicate used by the pivot layer.
-/
def YRough (y n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → y ≤ p

@[simp] theorem YRough_def (y n : ℕ) :
    YRough y n = (∀ p : ℕ, Nat.Prime p → p ∣ n → y ≤ p) := rfl

/--
Monotonicity of roughness in the pivot parameter:
if `n` is `y`-rough, then it is also `z`-rough for every `z ≤ y`.
-/
theorem YRough.mono_left {z y n : ℕ}
    (hzy : z ≤ y) (hy : YRough y n) :
    YRough z n := by
  intro p hp hpd
  exact le_trans hzy (hy p hp hpd)

/--
A number is trivially `0`-rough.
-/
theorem yrough_zero_left (n : ℕ) :
    YRough 0 n := by
  intro p hp hpd
  exact Nat.zero_le p

/--
A number is trivially `1`-rough.
-/
theorem yrough_one_left (n : ℕ) :
    YRough 1 n := by
  intro p hp hpd
  exact le_trans (by decide : 1 ≤ 2) hp.two_le

/--
A number is trivially `2`-rough with respect to its prime divisors.
-/
theorem yrough_two_left (n : ℕ) :
    YRough 2 n := by
  intro p hp hpd
  exact hp.two_le

end Pivot
end Lehmer