-- FILE: Lean/Lehmer/Pivot/AppendixA/IntervalMembership.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.UBmRangeProduct : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.UBmRangeProduct

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A interval membership lemmas

This file contains only structural membership/inclusion lemmas combining:
* the discrete Appendix A interval objects;
* the finite-prime packaging used by `UBm`.

Important scope:
* no prime-counting input;
* no nth-prime upper bound yet;
* no analytic estimate yet.
-/

/--
Every point of the form `y + t` with `t < barrierLen y` lies in the discrete
Appendix A interval.
-/
theorem add_index_mem_interval
    {y t : ℕ}
    (ht : t < barrierLen y) :
    InInterval y (y + t) := by
  exact add_lt_barrierLen_mem_interval ht

/--
The left endpoint belongs to the interval whenever the barrier length is
positive.
-/
theorem y_mem_interval
    {y : ℕ}
    (hpos : 0 < barrierLen y) :
    InInterval y y := by
  exact left_mem_interval hpos

/--
The right endpoint belongs to the interval.
-/
theorem xA_mem_interval
    (y : ℕ) :
    InInterval y (xA y) := by
  exact right_mem_interval y

/--
A member of `firstPrimesFrom y m` is prime and at least `y`.
-/
theorem mem_firstPrimesFrom_prime_and_ge
    {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    Nat.Prime p ∧ y ≤ p := by
  exact mem_firstPrimesFrom_prime_ge hp

/--
A member of `firstPrimesFrom y m` is at least the left endpoint of the
Appendix A interval.
-/
theorem mem_firstPrimesFrom_left_bound
    {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    y ≤ p := by
  exact (mem_firstPrimesFrom_prime_and_ge hp).2

/--
The indexed prime `nthPrimeFrom y k` is a member of `firstPrimesFrom y m`
whenever `k < m`.
-/
theorem nthPrimeFrom_mem_firstPrimesFrom'
    {y m k : ℕ}
    (hk : k < m) :
    nthPrimeFrom y k ∈ firstPrimesFrom y m := by
  exact nthPrimeFrom_mem_firstPrimesFrom hk

/--
The indexed prime `nthPrimeFrom y k` is prime.
-/
theorem nthPrimeFrom_prime'
    (y k : ℕ) :
    Nat.Prime (nthPrimeFrom y k) := by
  exact Pivot.nthPrimeFrom_prime y k

/--
The indexed prime `nthPrimeFrom y k` lies above `y`.
-/
theorem nthPrimeFrom_ge'
    (y k : ℕ) :
    y ≤ nthPrimeFrom y k := by
  exact Pivot.nthPrimeFrom_ge y k

/--
Prime-membership packaging for indexed primes.
-/
theorem nthPrimeFrom_prime_ge
    (y k : ℕ) :
    Nat.Prime (nthPrimeFrom y k) ∧ y ≤ nthPrimeFrom y k := by
  exact ⟨nthPrimeFrom_prime' y k, nthPrimeFrom_ge' y k⟩

/--
If `p ∈ firstPrimesFrom y m`, then `p` satisfies the left half of interval
membership.
-/
theorem mem_firstPrimesFrom_left_interval_condition
    {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    y ≤ p := by
  exact mem_firstPrimesFrom_left_bound hp

/--
Reformulation of membership in `firstPrimesFrom y m` through indexed primes.
-/
theorem mem_firstPrimesFrom_exists_index
    {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    ∃ k < m, nthPrimeFrom y k = p := by
  exact (mem_firstPrimesFrom_iff).mp hp

/--
Conversely, any indexed prime with index `< m` belongs to `firstPrimesFrom y m`.
-/
theorem exists_index_mem_firstPrimesFrom
    {y m p : ℕ}
    (hp : ∃ k < m, nthPrimeFrom y k = p) :
    p ∈ firstPrimesFrom y m := by
  exact (mem_firstPrimesFrom_iff).mpr hp

/--
Every element of `firstPrimesFrom y m` is represented by some index `< m`,
together with primality and the lower bound `y ≤ p`.
-/
theorem mem_firstPrimesFrom_exists_index_prime_ge
    {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    ∃ k < m, nthPrimeFrom y k = p ∧ Nat.Prime p ∧ y ≤ p := by
  rcases mem_firstPrimesFrom_exists_index hp with ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl, nthPrimeFrom_prime' y k, nthPrimeFrom_ge' y k⟩

/--
Set-theoretic inclusion criterion from `firstPrimesFrom y m` into the Appendix A
interval predicate, reduced to the missing right-endpoint bound.
-/
theorem firstPrimesFrom_subset_interval_of_upper_bound
    {y m : ℕ}
    (hub :
      ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ xA y) :
    ∀ p ∈ firstPrimesFrom y m, InInterval y p := by
  intro p hp
  rcases mem_firstPrimesFrom_exists_index hp with ⟨k, hk, rfl⟩
  exact ⟨nthPrimeFrom_ge' y k, hub k hk⟩

/--
Indexed version of the previous inclusion criterion.
-/
theorem nthPrimeFrom_mem_interval_of_upper_bound
    {y m k : ℕ}
    (hub :
      ∀ j : ℕ, j < m → nthPrimeFrom y j ≤ xA y)
    (hk : k < m) :
    InInterval y (nthPrimeFrom y k) := by
  exact ⟨nthPrimeFrom_ge' y k, hub k hk⟩

end AppendixA
end Pivot
end Lehmer