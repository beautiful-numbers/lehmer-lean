-- FILE: Lean/Lehmer/Pivot/SupportInterface.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.PrimeSupport : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.PrimeSupport

namespace Lehmer
namespace Pivot

open Lehmer.Basic

/--
Canonical support-size function used by the pivot layer.

It is the pivot-side incarnation of the arithmetic quantity `ω(n)`,
defined as the cardinality of the prime support of `n`.
-/
def omega (n : ℕ) : ℕ :=
  supportCard (primeSupport n)

@[simp] theorem omega_def (n : ℕ) :
    omega n = supportCard (primeSupport n) := rfl

@[simp] theorem omega_eq_card_primeSupport (n : ℕ) :
    omega n = (primeSupport n).card := rfl

/--
The prime support of `0` is empty, hence `omega 0 = 0`.
-/
@[simp] theorem omega_zero : omega 0 = 0 := by
  unfold omega supportCard primeSupport
  simp

/--
The prime support of `1` is empty, hence `omega 1 = 0`.
-/
@[simp] theorem omega_one : omega 1 = 0 := by
  unfold omega supportCard primeSupport
  simp

/--
`omega` is always nonnegative.
-/
theorem omega_nonneg (n : ℕ) : 0 ≤ omega n := by
  exact Nat.zero_le _

/--
If a prime belongs to the prime support of `n`, then `omega n` is positive.
-/
theorem omega_pos_of_mem_primeSupport {n p : ℕ}
    (hp : p ∈ primeSupport n) :
    0 < omega n := by
  rw [omega_eq_card_primeSupport]
  exact Finset.card_pos.mpr ⟨p, hp⟩

/--
If `n` has a prime divisor, then `omega n` is positive.
-/
theorem omega_pos_of_prime_dvd {n p : ℕ}
    (hn : n ≠ 0) (hp : Nat.Prime p) (hpd : p ∣ n) :
    0 < omega n := by
  apply omega_pos_of_mem_primeSupport
  exact mem_primeSupport_of_prime_dvd hn hp hpd

end Pivot
end Lehmer