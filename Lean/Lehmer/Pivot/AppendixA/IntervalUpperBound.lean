-- FILE: Lean/Lehmer/Pivot/AppendixA/IntervalUpperBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.IntervalMembership : def thm
- Lehmer.Pivot.AppendixA.PrimeCountToUpperBound : thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.IntervalMembership
import Lehmer.Pivot.AppendixA.PrimeCountToUpperBound

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A interval upper bound

This file packages the upper-bound statement needed to place the first `m`
primes `≥ y` inside the discrete Appendix A interval `[y, xA y]`.

Important scope:
* no analytic proof of the counting bound yet;
* no `mreq` yet;
* this file only turns a prime-count lower bound on `[y, xA y]` into the
  interval-membership consequences needed downstream.
-/

/--
Upper-bound interface asserting that the first `m` primes `≥ y` all lie below
the Appendix A right endpoint `xA y`.
-/
def HasIntervalUpperBound (y m : ℕ) : Prop :=
  ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ xA y

@[simp] theorem HasIntervalUpperBound_def
    (y m : ℕ) :
    HasIntervalUpperBound y m =
      (∀ k : ℕ, k < m → nthPrimeFrom y k ≤ xA y) := by
  rfl

/--
A prime-count lower bound on `[y, xA y]` yields the interval upper bound for
the first `m` primes `≥ y`.
-/
theorem HasIntervalUpperBound_of_card_primesInIcc_ge
    {y m : ℕ}
    (hcard : m ≤ (primesInIcc y (xA y)).card) :
    HasIntervalUpperBound y m := by
  exact all_nthPrimeFrom_le_xA_of_card_primesInIcc_ge hcard

/--
Indexed interval membership derived from the upper-bound interface.
-/
theorem nthPrimeFrom_mem_interval_of_HasIntervalUpperBound
    {y m k : ℕ}
    (hup : HasIntervalUpperBound y m)
    (hk : k < m) :
    InInterval y (nthPrimeFrom y k) := by
  exact nthPrimeFrom_mem_interval_of_upper_bound hup hk

/--
Set-membership form derived from the upper-bound interface:
every member of `firstPrimesFrom y m` lies in the Appendix A interval.
-/
theorem mem_firstPrimesFrom_interval_of_HasIntervalUpperBound
    {y m p : ℕ}
    (hup : HasIntervalUpperBound y m)
    (hp : p ∈ firstPrimesFrom y m) :
    InInterval y p := by
  exact firstPrimesFrom_subset_interval_of_upper_bound hup p hp

/--
Subset-style reformulation:
`firstPrimesFrom y m` is contained in the discrete Appendix A interval under the
upper-bound interface.
-/
theorem firstPrimesFrom_subset_interval_of_HasIntervalUpperBound
    {y m : ℕ}
    (hup : HasIntervalUpperBound y m) :
    ∀ p ∈ firstPrimesFrom y m, InInterval y p := by
  exact firstPrimesFrom_subset_interval_of_upper_bound hup

/--
Prime-membership packaging inside the interval under the upper-bound interface.
-/
theorem mem_firstPrimesFrom_prime_interval_of_HasIntervalUpperBound
    {y m p : ℕ}
    (hup : HasIntervalUpperBound y m)
    (hp : p ∈ firstPrimesFrom y m) :
    Nat.Prime p ∧ InInterval y p := by
  refine ⟨mem_firstPrimesFrom_prime' hp, ?_⟩
  exact mem_firstPrimesFrom_interval_of_HasIntervalUpperBound hup hp

/--
Existential index packaging inside the interval under the upper-bound
interface.
-/
theorem mem_firstPrimesFrom_exists_index_interval_of_HasIntervalUpperBound
    {y m p : ℕ}
    (hup : HasIntervalUpperBound y m)
    (hp : p ∈ firstPrimesFrom y m) :
    ∃ k < m, nthPrimeFrom y k = p ∧ InInterval y p := by
  rcases mem_firstPrimesFrom_exists_index hp with ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl, nthPrimeFrom_mem_interval_of_HasIntervalUpperBound hup hk⟩

/--
Right-endpoint inequality extracted from the upper-bound interface.
-/
theorem nthPrimeFrom_le_xA_of_HasIntervalUpperBound
    {y m k : ℕ}
    (hup : HasIntervalUpperBound y m)
    (hk : k < m) :
    nthPrimeFrom y k ≤ xA y := by
  exact hup k hk

end AppendixA
end Pivot
end Lehmer