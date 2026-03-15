-- FILE: Lean/Lehmer/Basic/PrimeSupport.lean
import Mathlib
import Lehmer.Basic.Defs
import Lehmer.Basic.SupportProd

namespace Lehmer
namespace Basic

/--
Membership in `primeSupport n` is equivalent to being a prime divisor of `n`.
-/
theorem mem_primeSupport_iff {n p : ℕ} :
    p ∈ primeSupport n ↔ Nat.Prime p ∧ p ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp [primeSupport]
  · constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpdiv, hpprime⟩
      exact ⟨hpprime, (Nat.mem_divisors.mp hpdiv).1⟩
    · intro hp
      rcases hp with ⟨hpprime, hpdvd⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, hpprime⟩
      exact Nat.mem_divisors.mpr ⟨hpdvd, hn⟩

/-- If `p ∈ primeSupport n`, then `p` is prime. -/
theorem prime_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) :
    Nat.Prime p := by
  exact (mem_primeSupport_iff.mp hp).1

/-- If `p ∈ primeSupport n`, then `p ∣ n`. -/
theorem dvd_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) :
    p ∣ n := by
  exact (mem_primeSupport_iff.mp hp).2

/-- If `p` is prime and divides `n`, then `p ∈ primeSupport n`. -/
theorem mem_primeSupport_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p) (hpd : p ∣ n) :
    p ∈ primeSupport n := by
  exact mem_primeSupport_iff.mpr ⟨hp, hpd⟩

/-- Every element of `primeSupport n` is nonzero. -/
theorem ne_zero_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) :
    p ≠ 0 := by
  exact (prime_of_mem_primeSupport hp).ne_zero

/-- Every element of `primeSupport n` is at least `2`. -/
theorem two_le_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) :
    2 ≤ p := by
  exact (prime_of_mem_primeSupport hp).two_le

/-- The prime support of `0` is empty. -/
@[simp] theorem primeSupport_zero :
    primeSupport 0 = ∅ := by
  ext p
  simp [primeSupport]

/-- The prime support of `1` is empty. -/
@[simp] theorem primeSupport_one :
    primeSupport 1 = ∅ := by
  ext p
  simp [primeSupport]

/-- If `n` is prime, then its prime support is the singleton `{n}`. -/
theorem primeSupport_of_prime {n : ℕ} (hn : Nat.Prime n) :
    primeSupport n = {n} := by
  ext p
  simp [mem_primeSupport_iff, hn, Nat.prime.dvd_iff_eq hn]

/--
Every prime divisor of `n` belongs to `primeSupport n`.
This is just the forward API version of `mem_primeSupport_iff`.
-/
theorem subset_primeSupport_of_prime_dvd {n : ℕ} :
    {p ∈ Nat.divisors n | Nat.Prime p}.Finite := by
  exact Set.toFinite _

/--
If `n` is squarefree, then the product of its prime support is `n`.

This is the key support/product bridge used later in the paper.
-/
theorem supportProd_primeSupport_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    supportProd (primeSupport n) = n := by
  simpa [primeSupport, supportProd] using Nat.prod_primeFactors_of_squarefree hsq

/--
If `n` is squarefree, then `n` factors as the product of its prime support.
-/
theorem exists_eq_supportProd_primeSupport {n : ℕ}
    (hsq : Squarefree n) :
    n = supportProd (primeSupport n) := by
  simpa using (supportProd_primeSupport_of_squarefree hsq).symm

end Basic
end Lehmer