-- FILE: Lean/Lehmer/Pivot/AppendixA/IntervalUpperBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.PrimeCountToUpperBound : thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.PrimeCountToUpperBound

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A interval upper bound

This file records the paper-facing specialization of the counting-to-enumeration
bridge to the Appendix A endpoint `xA y`.

Core content:
* from the prime count on `[y, xA y]`, recover that the first `m` primes
  greater than or equal to `y` all lie in `[y, xA y]`.

Scope:
* no analytic proof of the counting bound yet;
* no product comparison yet;
* no `mreq` yet.
-/

/--
Appendix A upper bound for the `m`-th prime `≥ y`, in the paper-facing
prime-counting form.
-/
theorem py_le_xA_of_primePi_bound
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hm : 1 ≤ m)
    (hcount : m ≤ primePi (xA y) - primePi y + 1) :
    py y m ≤ xA y := by
  exact py_le_xA_of_primePi_sub_primePi_add_one
    (y := y) (m := m) hy hyx hm hcount

/--
Appendix A package:
if the interval `[y, xA y]` contains at least `m` primes, then every one of the
first `m` primes `≥ y` lies in `[y, xA y]`.
-/
theorem all_py_mem_Icc_y_xA_of_primePi_bound
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ primePi (xA y) - primePi y + 1) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m → y ≤ py y i ∧ py y i ≤ xA y := by
  intro i hi him
  exact ⟨py_ge_of_one_le hi, py_le_xA_of_primePi_bound hy hyx hi (le_trans him hcount)⟩

/--
Zero-based reformulation used by the finite-product layer.
-/
theorem all_py0_le_xA_of_primePi_bound
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ primePi (xA y) - primePi y + 1) :
    ∀ k : ℕ, k < m → py0 y k ≤ xA y := by
  intro k hk
  simpa [py0] using
    py_le_xA_of_primePi_bound
      (y := y) (m := k + 1) hy hyx (Nat.succ_le_succ (Nat.zero_le k))
      (le_trans (Nat.succ_le_of_lt hk) hcount)

/--
Set-theoretic reformulation used downstream:
the finite block `firstPrimesFrom y m` lies in the interval `[y, xA y]`.
-/
theorem firstPrimesFrom_subset_Icc_y_xA_of_primePi_bound
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hcount : m ≤ primePi (xA y) - primePi y + 1) :
    ∀ p ∈ firstPrimesFrom y m, y ≤ p ∧ p ≤ xA y := by
  intro p hp
  rcases (Pivot.mem_firstPrimesFrom_iff).mp hp with ⟨k, hk, rfl⟩
  exact ⟨py0_ge y k, all_py0_le_xA_of_primePi_bound hy hyx hcount k hk⟩

end AppendixA
end Pivot
end Lehmer