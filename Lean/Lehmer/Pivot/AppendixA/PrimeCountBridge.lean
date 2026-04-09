-- FILE: Lean/Lehmer/Pivot/AppendixA/PrimeCountBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
- Lehmer.Pivot.AppendixA.PrimeEnumeration : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.AppendixA.PrimeCountDefs
import Lehmer.Pivot.AppendixA.PrimeEnumeration

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A prime-count bridge

This file records the genuine finite counting consequences already available
from the enumeration layer.

Important scope:
* no analytic estimates;
* no `mreq`;
* no converse counting-to-upper-bound theorem yet.

What is proved here is the bridge in the direction that is already justified:
an upper bound on the indexed primes `nthPrimeFrom y k` implies a counting
lower bound on the interval `[y, x]`.
-/

/--
If all first `m` indexed primes above `y` are at most `x`, then there are at
least `m` primes in the interval `[y, x]`.
-/
theorem m_le_card_primesInIcc_of_nthPrimeFrom_le
    {y m x : ℕ}
    (hub : ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ x) :
    m ≤ (primesInIcc y x).card := by
  exact m_le_card_primesInIcc_of_upper_bound hub

/--
If all first `m` indexed primes above `y` are at most `x`, then there are at
least `m` primes at most `x`.
-/
theorem m_le_primePi_of_nthPrimeFrom_le
    {y m x : ℕ}
    (hub : ∀ k : ℕ, k < m → nthPrimeFrom y k ≤ x) :
    m ≤ primePi x := by
  exact m_le_primePi_of_upper_bound hub

/--
Specialized pointwise form: if `nthPrimeFrom y (m - 1) ≤ x` and `m > 0`, then
there are at least `m` primes in `[y, x]`.
-/
theorem m_le_card_primesInIcc_of_last_nthPrimeFrom_le
    {y m x : ℕ}
    (hm : 0 < m)
    (hlast : nthPrimeFrom y (m - 1) ≤ x) :
    m ≤ (primesInIcc y x).card := by
  apply m_le_card_primesInIcc_of_nthPrimeFrom_le
  intro k hk
  have hkm1 : k ≤ m - 1 := by
    omega
  have hmono := nthPrimeFrom_strictMono y
  have hle : nthPrimeFrom y k ≤ nthPrimeFrom y (m - 1) := by
    exact le_of_lt_or_eq ((lt_or_eq_of_le hkm1)).elim
      (fun hlt => le_of_lt (hmono hlt))
      (fun heq => by simpa [heq])
  exact le_trans hle hlast

/--
Specialized pointwise form: if `nthPrimeFrom y (m - 1) ≤ x` and `m > 0`, then
there are at least `m` primes at most `x`.
-/
theorem m_le_primePi_of_last_nthPrimeFrom_le
    {y m x : ℕ}
    (hm : 0 < m)
    (hlast : nthPrimeFrom y (m - 1) ≤ x) :
    m ≤ primePi x := by
  exact le_trans
    (m_le_card_primesInIcc_of_last_nthPrimeFrom_le hm hlast)
    (card_primesInIcc_le_primePi y x)

end AppendixA
end Pivot
end Lehmer