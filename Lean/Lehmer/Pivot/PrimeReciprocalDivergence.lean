-- FILE: Lean/Lehmer/Pivot/PrimeReciprocalDivergence.lean
/-
IMPORT CLASSIFICATION
- Archive.Wiedijk100Theorems.SumOfPrimeReciprocalsDiverges : thm
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm

FILE ROLE
This file provides the source divergence statement used downstream in `UBmGrowth`.

Design choice:
- We do not reprove divergence locally.
- We import the existing mathlib theorem stating that the partial sums of
  reciprocals of primes tend to `+∞`.
- We expose only the paper/UBm-friendly finite-set corollary.
-/

import Lehmer.Prelude
import Lehmer.Pivot.AppendixA.PrimeCountDefs
import Archive.Wiedijk100Theorems.SumOfPrimeReciprocalsDiverges

open scoped BigOperators
open Finset
open Filter

namespace Lehmer
namespace Pivot

noncomputable section

/--
Unboundedness of the reciprocal-prime partial sums over primes `≤ X`.

This is the external source theorem used downstream for the intrinsic growth of
`UBm`.
-/
theorem prime_harmonic_unbounded :
    ∀ B : ℝ, ∃ X : ℕ,
      B ≤ ∑ p in AppendixA.primesUpTo X, (1 : ℝ) / p := by
  intro B
  rcases (tendsto_atTop.1 Theorems100.Real.tendsto_sum_one_div_prime_atTop) B with
    ⟨X, hX⟩
  refine ⟨X, ?_⟩
  simpa [AppendixA.primesUpTo, Finset.sum_filter] using hX

end

end Pivot
end Lehmer