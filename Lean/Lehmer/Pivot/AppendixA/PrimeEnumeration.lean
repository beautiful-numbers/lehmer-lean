-- FILE: Lean/Lehmer/Pivot/AppendixA/PrimeEnumeration.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixA.UBmRangeProduct : def thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.AppendixA.UBmRangeProduct
import Lehmer.Pivot.AppendixA.PrimeCountDefs

open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A finite prime-enumeration lemmas

This file contains only genuine finite enumeration facts connecting:
* `nthPrimeFrom` / `firstPrimesFrom`,
* `primesInIcc`,
* `primePi`.

Important scope:
* no analytic estimates;
* no `mreq`;
* no interval upper bound theorem yet.
-/

/--
Every indexed prime `nthPrimeFrom y k` belongs to `firstPrimesFrom y m` when
`k < m`.
-/
theorem nthPrimeFrom_mem_firstPrimesFrom_of_lt
    {y m k : ℕ}
    (hk : k < m) :
    nthPrimeFrom y k ∈ firstPrimesFrom y m := by
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩

/--
Every indexed prime `nthPrimeFrom y k` lies in `primesUpTo x` once it is known
to be at most `x`.
-/
theorem nthPrimeFrom_mem_primesUpTo_of_le
    {y k x : ℕ}
    (hkx : nthPrimeFrom y k ≤ x) :
    nthPrimeFrom y k ∈ primesUpTo x := by
  exact mem_primesUpTo_iff.mpr ⟨hkx, nthPrimeFrom_prime y k⟩

/--
Every indexed prime `nthPrimeFrom y k` lies in `primesInIcc y x` once it is
known to be at most `x`.
-/
theorem nthPrimeFrom_mem_primesInIcc_of_le
    {y k x : ℕ}
    (hkx : nthPrimeFrom y k ≤ x) :
    nthPrimeFrom y k ∈ primesInIcc y x := by
  exact mem_primesInIcc_iff.mpr ⟨nthPrimeFrom_ge y k, hkx, nthPrimeFrom_prime y k⟩

/--
If all first `m` indexed primes are at most `x`, then every member of
`firstPrimesFrom y m` lies in `primesInIcc y x`.
-/
theorem firstPrimesFrom_subset_primesInIcc_of_upper_bound
    {y m x : ℕ}
    (hub : ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ x) :
    ∀ p ∈ firstPrimesFrom y m, p ∈ primesInIcc y x := by
  intro p hp
  rcases (mem_firstPrimesFrom_iff).mp hp with ⟨k, hk, rfl⟩
  exact nthPrimeFrom_mem_primesInIcc_of_le (hub k hk)

/--
Set inclusion form of the previous lemma.
-/
theorem firstPrimesFrom_subset_primesInIcc
    {y m x : ℕ}
    (hub : ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ x) :
    firstPrimesFrom y m ⊆ primesInIcc y x := by
  intro p hp
  exact firstPrimesFrom_subset_primesInIcc_of_upper_bound hub p hp

/--
If all first `m` indexed primes are at most `x`, then the cardinality of
`firstPrimesFrom y m` is bounded by the number of primes in `[y,x]`.
-/
theorem card_firstPrimesFrom_le_card_primesInIcc_of_upper_bound
    {y m x : ℕ}
    (hub : ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ x) :
    (firstPrimesFrom y m).card ≤ (primesInIcc y x).card := by
  exact Finset.card_le_card (firstPrimesFrom_subset_primesInIcc hub)

/--
Numerical form of the previous cardinality comparison.
-/
theorem m_le_card_primesInIcc_of_upper_bound
    {y m x : ℕ}
    (hub : ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ x) :
    m ≤ (primesInIcc y x).card := by
  simpa [card_firstPrimesFrom] using
    card_firstPrimesFrom_le_card_primesInIcc_of_upper_bound hub

/--
Every member of `primesInIcc y x` is a prime at most `x`.
-/
theorem mem_primesInIcc_to_primesUpTo
    {y x p : ℕ}
    (hp : p ∈ primesInIcc y x) :
    p ∈ primesUpTo x := by
  exact mem_primesUpTo_of_mem_primesInIcc hp

/--
The number of primes in `[y,x]` is bounded by `primePi x`.
-/
theorem card_primesInIcc_le_primePi
    (y x : ℕ) :
    (primesInIcc y x).card ≤ primePi x := by
  exact Finset.card_le_card (by
    intro p hp
    exact mem_primesInIcc_to_primesUpTo hp)

/--
If all first `m` indexed primes are at most `x`, then `m ≤ primePi x`.
-/
theorem m_le_primePi_of_upper_bound
    {y m x : ℕ}
    (hub : ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ x) :
    m ≤ primePi x := by
  exact le_trans
    (m_le_card_primesInIcc_of_upper_bound hub)
    (card_primesInIcc_le_primePi y x)

end AppendixA
end Pivot
end Lehmer