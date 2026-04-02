-- FILE: Lean/Lehmer/Pivot/AppendixA/NthPrimeEnumeration.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.AppendixA.PrimeCountDefs

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A enumeration of `nthPrimeFrom`

This file proves the genuine enumeration fact needed downstream:
every prime `p ≥ y` appears somewhere in the sequence `nthPrimeFrom y`.

Important scope:
* no analytic estimates;
* no `mreq`;
* no interval/product bounds yet.
-/

/--
Every prime `p ≥ y` occurs in the sequence `nthPrimeFrom y`.
-/
theorem exists_nthPrimeFrom_eq_of_prime_ge
    (y p : ℕ)
    (hp : Nat.Prime p)
    (hyp : y ≤ p) :
    ∃ k : ℕ, nthPrimeFrom y k = p := by
  revert y
  refine Nat.strong_induction_on p ?_
  intro p ih y hp hyp
  let q := nextPrimeGe y
  have hqprime : Nat.Prime q := nextPrimeGe_prime y
  have hyq : y ≤ q := nextPrimeGe_ge y
  have hqp : q ≤ p := nextPrimeGe_le_of_prime_ge hp hyp
  by_cases hEq : q = p
  · exact ⟨0, by simpa [q, hEq] using nthPrimeFrom_zero y⟩
  · have hlt : q < p := lt_of_le_of_ne hqp (Ne.symm hEq)
    have hq1p : q + 1 ≤ p := Nat.succ_le_of_lt hlt
    have hk :
        ∃ k : ℕ, nthPrimeFrom (q + 1) k = p := by
      exact ih (q + 1) hlt hp hq1p
    rcases hk with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    simpa [nthPrimeFrom_succ, q] using hk

/--
Every prime in `[y,x]` occurs in the sequence `nthPrimeFrom y`.
-/
theorem exists_nthPrimeFrom_eq_of_mem_primesInIcc
    {y x p : ℕ}
    (hp : p ∈ primesInIcc y x) :
    ∃ k : ℕ, nthPrimeFrom y k = p := by
  rcases mem_primesInIcc_iff.mp hp with ⟨hyp, _hpx, hprime⟩
  exact exists_nthPrimeFrom_eq_of_prime_ge y p hprime hyp

/--
Every prime `≤ x` and `≥ y` occurs in the sequence `nthPrimeFrom y`.
-/
theorem exists_nthPrimeFrom_eq_of_mem_primesUpTo
    {y x p : ℕ}
    (hp : p ∈ primesUpTo x)
    (hyp : y ≤ p) :
    ∃ k : ℕ, nthPrimeFrom y k = p := by
  rcases mem_primesUpTo_iff.mp hp with ⟨_hpx, hprime⟩
  exact exists_nthPrimeFrom_eq_of_prime_ge y p hprime hyp

end AppendixA
end Pivot
end Lehmer