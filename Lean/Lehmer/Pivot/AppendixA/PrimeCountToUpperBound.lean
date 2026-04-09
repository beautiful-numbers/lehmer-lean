-- FILE: Lean/Lehmer/Pivot/AppendixA/PrimeCountToUpperBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.UBmOrder : def thm
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.UBmOrder
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.PrimeCountDefs

open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A prime-count to upper-bound bridge

This file contains the finite counting-to-enumeration bridge used in Appendix A:

if there are at least `m` primes in `[y, x]`, then the first `m` primes
greater than or equal to `y` all lie in `[y, x]`.

Scope:
* no analytic estimates;
* no `mreq`;
* purely finite counting / enumeration.
-/

/--
If a prime lies strictly between `py0 y k` and `py0 y (k+1)`, then it lies
above the least prime `≥ py0 y k + 1`, which is impossible.
-/
private theorem py0_succ_le_of_prime_gt
    {y k p : ℕ}
    (hp : Nat.Prime p)
    (hgt : py0 y k < p) :
    py0 y (k + 1) ≤ p := by
  simpa [py0_succ] using
    nextPrimeGe_le_of_prime_ge hp (Nat.succ_le_of_lt hgt)

/--
A prime strictly below `py0 y (k+1)` is at most `py0 y k`.
-/
private theorem prime_lt_py0_succ_imp_le_py0
    {y k p : ℕ}
    (hp : Nat.Prime p)
    (hlt : p < py0 y (k + 1)) :
    p ≤ py0 y k := by
  by_contra hnot
  have hgt : py0 y k < p := lt_of_not_ge hnot
  have hle : py0 y (k + 1) ≤ p := py0_succ_le_of_prime_gt hp hgt
  exact (not_lt_of_ge hle) hlt

/--
If there are at least `k+1` primes in `[y, x]`, then the `k`-th prime
greater than or equal to `y` lies at most at `x`.
-/
theorem py0_le_of_succ_le_primeCountInIcc
    {y x k : ℕ}
    (hcount : k + 1 ≤ primeCountInIcc y x) :
    py0 y k ≤ x := by
  by_contra hnot
  have hlt : x < py0 y k := lt_of_not_ge hnot
  have hsubset : primesInIcc y x ⊆ firstPrimesFrom y k := by
    intro p hp
    have hp_prime : Nat.Prime p := prime_of_mem_primesInIcc hp
    have hp_left : y ≤ p := (bounds_of_mem_primesInIcc hp).1
    have hp_right : p ≤ x := (bounds_of_mem_primesInIcc hp).2
    cases k with
    | zero =>
        exfalso
        have hfirst : py0 y 0 ≤ p := by
          simpa [py0] using nextPrimeGe_le_of_prime_ge hp_prime hp_left
        exact (not_lt_of_ge hfirst) (lt_of_le_of_lt hp_right hlt)
    | succ k' =>
        have hp_lt_last : p < py0 y (k' + 1) := lt_of_le_of_lt hp_right hlt
        have hp_le_prev : p ≤ py0 y k' :=
          prime_lt_py0_succ_imp_le_py0 hp_prime hp_lt_last
        have hp_mem : p ∈ firstPrimesFrom y (k' + 1) :=
          prime_ge_le_py0_mem_firstPrimesFrom hp_prime hp_left hp_le_prev
        simpa using hp_mem
  have hcard :
      primeCountInIcc y x ≤ (firstPrimesFrom y k).card := by
    simpa [primeCountInIcc_def] using Finset.card_le_card hsubset
  rw [card_firstPrimesFrom] at hcard
  omega

/--
Paper-facing counting-to-enumeration bridge:

if there are at least `m` primes in `[y, x]`, then the `m`-th prime
greater than or equal to `y` lies at most at `x`.
-/
theorem py_le_of_primeCountInIcc
    {y x m : ℕ}
    (hm : 1 ≤ m)
    (hcount : m ≤ primeCountInIcc y x) :
    py y m ≤ x := by
  rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
  simpa [py0] using
    py0_le_of_succ_le_primeCountInIcc (y := y) (x := x) (k := k) hcount

/--
Paper-facing pointwise package:

if there are at least `m` primes in `[y, x]`, then every `i`-th prime with
`1 ≤ i ≤ m` lies at most at `x`.
-/
theorem all_py_le_of_primeCountInIcc
    {y x m : ℕ}
    (hcount : m ≤ primeCountInIcc y x) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m → py y i ≤ x := by
  intro i hi him
  exact py_le_of_primeCountInIcc hi (le_trans him hcount)

/--
Equivalent form with the interval cardinal written explicitly.
-/
theorem py_le_of_card_primesInIcc
    {y x m : ℕ}
    (hm : 1 ≤ m)
    (hcount : m ≤ (primesInIcc y x).card) :
    py y m ≤ x := by
  exact py_le_of_primeCountInIcc hm (by simpa [primeCountInIcc_def] using hcount)

/--
Equivalent pointwise package with the interval cardinal written explicitly.
-/
theorem all_py_le_of_card_primesInIcc
    {y x m : ℕ}
    (hcount : m ≤ (primesInIcc y x).card) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m → py y i ≤ x := by
  intro i hi him
  exact py_le_of_card_primesInIcc hi (le_trans him hcount)

/--
Prime-endpoint Appendix A form:

if `y` is prime and there are at least
`π(x) - π(y) + 1` primes in `[y, x]`, then the `m`-th prime `≥ y`
lies at most at `x`.
-/
theorem py_le_of_primePi_sub_primePi_add_one
    {y x m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ x)
    (hm : 1 ≤ m)
    (hcount : m ≤ primePi x - primePi y + 1) :
    py y m ≤ x := by
  have hcard : m ≤ primeCountInIcc y x := by
    rw [primeCountInIcc_eq_primePi_sub_primePi_add_one hy hyx]
    exact hcount
  exact py_le_of_primeCountInIcc hm hcard

/--
Appendix A specialization to the right endpoint `xA y`, assuming the corresponding
prime-count bound is available in that form.
-/
theorem py_le_xA_of_primePi_sub_primePi_add_one
    {y m : ℕ}
    (hy : Nat.Prime y)
    (hyx : y ≤ xA y)
    (hm : 1 ≤ m)
    (hcount : m ≤ primePi (xA y) - primePi y + 1) :
    py y m ≤ xA y := by
  exact py_le_of_primePi_sub_primePi_add_one hy hyx hm hcount

end AppendixA
end Pivot
end Lehmer