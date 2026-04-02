-- FILE: Lean/Lehmer/Pivot/AppendixA/PrimeCountToUpperBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
- Lehmer.Pivot.AppendixA.PrimeEnumeration : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.PrimeCountDefs
import Lehmer.Pivot.AppendixA.PrimeEnumeration

open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A prime-count to upper-bound bridge

This file proves the converse finite bridge needed downstream:

if there are at least `m` primes in the interval `[y, x]`, then the first `m`
primes `≥ y` all lie at most at `x`.

Important scope:
* no analytic estimates;
* no `mreq`;
* purely finite counting / enumeration.
-/

/--
If `nthPrimeFrom y (m - 1)` lies strictly above `x`, then there are at most
`m - 1` primes in `[y, x]`.
-/
theorem card_primesInIcc_le_pred_of_nthPrimeFrom_pred_gt
    {y m x : ℕ}
    (hm : 0 < m)
    (hgt : x < nthPrimeFrom y (m - 1)) :
    (primesInIcc y x).card ≤ m - 1 := by
  have hsubset : primesInIcc y x ⊆ firstPrimesFrom y (m - 1) := by
    intro p hp
    rcases exists_nthPrimeFrom_eq_of_mem_primesInIcc hp with ⟨k, rfl⟩
    have hklt : k < m - 1 := by
      by_contra hklt
      have hkm1 : m - 1 ≤ k := Nat.le_of_not_lt hklt
      rcases lt_or_eq_of_le hkm1 with hlt | rfl
      · have hstrict :
            nthPrimeFrom y (m - 1) < nthPrimeFrom y k :=
          (nthPrimeFrom_strictMono y) hlt
        have hkx : nthPrimeFrom y k ≤ x :=
          (bounds_of_mem_primesInIcc hp).2
        exact (not_lt_of_ge hkx) (lt_of_lt_of_le hgt hstrict)
      · have hkx : nthPrimeFrom y (m - 1) ≤ x :=
          (bounds_of_mem_primesInIcc hp).2
        exact (not_lt_of_ge hkx) hgt
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hklt, rfl⟩
  have hcard :
      (primesInIcc y x).card ≤ (firstPrimesFrom y (m - 1)).card :=
    Finset.card_le_card hsubset
  simpa [card_firstPrimesFrom] using hcard

/--
If there are at least `m` primes in `[y, x]`, then the `(m-1)`-th prime
`≥ y` lies at most at `x`.
-/
theorem nthPrimeFrom_pred_le_of_card_primesInIcc_ge
    {y m x : ℕ}
    (hm : 0 < m)
    (hcard : m ≤ (primesInIcc y x).card) :
    nthPrimeFrom y (m - 1) ≤ x := by
  by_contra hnot
  have hgt : x < nthPrimeFrom y (m - 1) := lt_of_not_ge hnot
  have hle :
      (primesInIcc y x).card ≤ m - 1 :=
    card_primesInIcc_le_pred_of_nthPrimeFrom_pred_gt hm hgt
  omega

/--
If there are at least `m` primes in `[y, x]`, then every indexed prime
`nthPrimeFrom y k` with `k < m` lies at most at `x`.
-/
theorem nthPrimeFrom_le_of_card_primesInIcc_ge
    {y m x k : ℕ}
    (hk : k < m)
    (hcard : m ≤ (primesInIcc y x).card) :
    nthPrimeFrom y k ≤ x := by
  have hk1 : 0 < k + 1 := Nat.succ_pos k
  have hk1m : k + 1 ≤ m := Nat.succ_le_of_lt hk
  have hcard' : k + 1 ≤ (primesInIcc y x).card := le_trans hk1m hcard
  simpa using nthPrimeFrom_pred_le_of_card_primesInIcc_ge hk1 hcard'

/--
Specialization to the Appendix A right endpoint `xA y`.
-/
theorem nthPrimeFrom_le_xA_of_card_primesInIcc_ge
    {y m k : ℕ}
    (hk : k < m)
    (hcard : m ≤ (primesInIcc y (xA y)).card) :
    nthPrimeFrom y k ≤ xA y := by
  exact nthPrimeFrom_le_of_card_primesInIcc_ge hk hcard

/--
Pointwise upper-bound package extracted from a prime-count lower bound on the
interval `[y, xA y]`.
-/
theorem all_nthPrimeFrom_le_xA_of_card_primesInIcc_ge
    {y m : ℕ}
    (hcard : m ≤ (primesInIcc y (xA y)).card) :
    ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ xA y := by
  intro k hk
  exact nthPrimeFrom_le_xA_of_card_primesInIcc_ge hk hcard

end AppendixA
end Pivot
end Lehmer