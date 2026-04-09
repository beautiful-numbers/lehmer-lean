-- FILE: Lean/Lehmer/Pivot/PrimeReciprocalTailBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.UBmOrder : def thm
- Lehmer.Pivot.PrimeReciprocalDivergence : thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
- Lehmer.Pivot.AppendixA.PrimeCountToUpperBound : thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.UBm
import Lehmer.Pivot.UBmOrder
import Lehmer.Pivot.PrimeReciprocalDivergence
import Lehmer.Pivot.AppendixA.PrimeCountDefs
import Lehmer.Pivot.AppendixA.PrimeCountToUpperBound

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot

noncomputable section

/--
The reciprocal-prime summand is nonnegative on prime sets.
-/
private theorem reciprocal_prime_nonneg {p : ℕ} :
    0 ≤ (1 : ℝ) / (p : ℝ) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · have hp_nonneg : 0 ≤ (p : ℝ) := by exact_mod_cast Nat.zero_le p
    exact one_div_nonneg.mpr hp_nonneg

/--
Monotonicity of reciprocal-prime sums over `primesUpTo`.
-/
private theorem sum_primesUpTo_mono {X X' : ℕ} (hXX' : X ≤ X') :
    (∑ p in AppendixA.primesUpTo X, (1 : ℝ) / (p : ℝ)) ≤
      ∑ p in AppendixA.primesUpTo X', (1 : ℝ) / (p : ℝ) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rcases AppendixA.mem_primesUpTo_iff.mp hp with ⟨hpX, hpprime⟩
    exact AppendixA.mem_primesUpTo_iff.mpr ⟨le_trans hpX hXX', hpprime⟩
  · intro p hpX' hpnot
    exact reciprocal_prime_nonneg

/--
For a fixed interval `[y, X]`, the first `primeCountInIcc y X` primes `≥ y`
are exactly the primes in that interval.
-/
theorem firstPrimesFrom_eq_primesInIcc_of_primeCount
    (y X : ℕ) :
    firstPrimesFrom y (AppendixA.primeCountInIcc y X) = AppendixA.primesInIcc y X := by
  classical
  have hsubset :
      firstPrimesFrom y (AppendixA.primeCountInIcc y X) ⊆ AppendixA.primesInIcc y X := by
    intro p hp
    rcases (Pivot.mem_firstPrimesFrom_iff).mp hp with ⟨k, hk, rfl⟩
    have hpx : py0 y k ≤ X :=
      AppendixA.all_py0_le_of_primeCountInIcc
        (y := y) (x := X) (m := AppendixA.primeCountInIcc y X) le_rfl k hk
    exact AppendixA.mem_primesInIcc_iff.mpr ⟨py0_ge y k, hpx, py0_prime y k⟩
  have hcard :
      (AppendixA.primesInIcc y X).card ≤
        (firstPrimesFrom y (AppendixA.primeCountInIcc y X)).card := by
    rw [card_firstPrimesFrom, AppendixA.primeCountInIcc_def]
  exact Finset.eq_of_subset_of_card_le hsubset hcard

/--
The reciprocal sum over the primes in `[y, X]` is the same as the reciprocal
sum along the initial `py0`-block of corresponding length.
-/
theorem sum_primesInIcc_eq_sum_range_py0
    (y X : ℕ) :
    (∑ p in AppendixA.primesInIcc y X, (1 : ℝ) / (p : ℝ)) =
      ∑ k in Finset.range (AppendixA.primeCountInIcc y X), (1 : ℝ) / (py0 y k : ℝ) := by
  classical
  rw [← firstPrimesFrom_eq_primesInIcc_of_primeCount y X]
  unfold firstPrimesFrom
  rw [Finset.sum_image]
  · rfl
  · exact (py0_strictMono y).injective.injOn _

/--
For fixed `y`, the reciprocal-prime partial sums along `py0 y k`
are unbounded above.
-/
theorem prime_harmonic_unbounded_from_y
    (y : ℕ) :
    ∀ B : ℝ, ∃ m : ℕ,
      B ≤ ∑ k in Finset.range m, (1 : ℝ) / (py0 y k : ℝ) := by
  intro B
  let C : ℝ := ∑ p in AppendixA.primesUpTo (y - 1), (1 : ℝ) / (p : ℝ)
  rcases prime_harmonic_unbounded (B + C) with ⟨X, hX⟩
  let X' : ℕ := max X (y - 1)
  have hmono :
      B + C ≤ ∑ p in AppendixA.primesUpTo X', (1 : ℝ) / (p : ℝ) := by
    exact le_trans hX (sum_primesUpTo_mono (Nat.le_max_left _ _))
  have hyX' : y ≤ X' + 1 := by
    dsimp [X']
    omega
  have hsplit :
      ∑ p in AppendixA.primesUpTo X', (1 : ℝ) / (p : ℝ) =
        (∑ p in AppendixA.primesUpTo (y - 1), (1 : ℝ) / (p : ℝ)) +
        (∑ p in AppendixA.primesInIcc y X', (1 : ℝ) / (p : ℝ)) := by
    classical
    rw [AppendixA.primesUpTo_disjUnion_primesInIcc y X' hyX']
    rw [Finset.sum_disjUnion]
    · rfl
    · intro p hp1 hp2
      rcases AppendixA.mem_primesUpTo_iff.mp hp1 with ⟨h1, _⟩
      rcases AppendixA.mem_primesInIcc_iff.mp hp2 with ⟨h2, _, _⟩
      exact Nat.not_lt_of_ge h2 (Nat.lt_of_le_pred h1)
  have hinter :
      B ≤ ∑ p in AppendixA.primesInIcc y X', (1 : ℝ) / (p : ℝ) := by
    dsimp [C] at hmono
    rw [hsplit] at hmono
    linarith
  refine ⟨AppendixA.primeCountInIcc y X', ?_⟩
  rw [← sum_primesInIcc_eq_sum_range_py0 y X']
  exact hinter

end

end Pivot