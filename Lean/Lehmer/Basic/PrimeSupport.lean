-- FILE: Lean/Lehmer/Basic/PrimeSupport.lean
/-
IMPORT CLASSIFICATION
- Mathlib : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.SupportProd : thm
-/

import Mathlib
import Lehmer.Basic.Defs
import Lehmer.Basic.SupportProd

namespace Lehmer
namespace Basic

/--
Membership in `primeSupport n` is equivalent to being a prime divisor of `n`,
provided `n ≠ 0`.
-/
theorem mem_primeSupport_iff {n p : ℕ} (hn : n ≠ 0) :
    p ∈ primeSupport n ↔ Nat.Prime p ∧ p ∣ n := by
  constructor
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
  by_cases hn : n = 0
  · simp [primeSupport, hn] at hp
  · exact (mem_primeSupport_iff hn).mp hp |>.1

/-- If `p ∈ primeSupport n`, then `p ∣ n`. -/
theorem dvd_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) :
    p ∣ n := by
  by_cases hn : n = 0
  · simp [primeSupport, hn] at hp
  · exact (mem_primeSupport_iff hn).mp hp |>.2

/-- If `p` is prime and divides `n`, then `p ∈ primeSupport n`, provided `n ≠ 0`. -/
theorem mem_primeSupport_of_prime_dvd {n p : ℕ}
    (hn : n ≠ 0) (hp : Nat.Prime p) (hpd : p ∣ n) :
    p ∈ primeSupport n := by
  exact (mem_primeSupport_iff hn).mpr ⟨hp, hpd⟩

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
  constructor
  · intro hp
    have hpprime : Nat.Prime p := prime_of_mem_primeSupport hp
    have hpd : p ∣ 1 := dvd_of_mem_primeSupport hp
    have hp1 : p = 1 := Nat.dvd_one.mp hpd
    exact False.elim (hpprime.ne_one hp1)
  · intro hp
    simp at hp

/-- If `n` is prime, then its prime support is the singleton `{n}`. -/
theorem primeSupport_of_prime {n : ℕ} (hn : Nat.Prime n) :
    primeSupport n = {n} := by
  ext p
  constructor
  · intro hp
    have hpprime : Nat.Prime p := prime_of_mem_primeSupport hp
    have hpd : p ∣ n := dvd_of_mem_primeSupport hp
    have hcases : p = 1 ∨ p = n := (Nat.dvd_prime hn).mp hpd
    rcases hcases with hp1 | hpn
    · exact False.elim (hpprime.ne_one hp1)
    · simpa [Finset.mem_singleton] using hpn
  · intro hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact mem_primeSupport_of_prime_dvd hn.ne_zero hn dvd_rfl

/--
The set underlying `primeSupport n` is finite.
-/
theorem subset_primeSupport_of_prime_dvd {n : ℕ} :
    Set.Finite {p : ℕ | p ∈ primeSupport n} := by
  exact Set.toFinite _

/--
If `n` is squarefree, then the prime support coincides with `n.primeFactors`.
-/
theorem primeSupport_eq_primeFactors_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    primeSupport n = n.primeFactors := by
  ext p
  have hn : n ≠ 0 := by
    intro hn0
    subst hn0
    simp at hsq
  rw [mem_primeSupport_iff hn, Nat.mem_primeFactors]
  constructor
  · intro hp
    exact ⟨hp.1, hp.2, hn⟩
  · intro hp
    exact ⟨hp.1, hp.2.1⟩

/--
If `n` is squarefree, then the product of its prime support is `n`.

This is the key support/product bridge used later in the paper.
-/
theorem supportProd_primeSupport_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    supportProd (primeSupport n) = n := by
  rw [primeSupport_eq_primeFactors_of_squarefree hsq, supportProd]
  simpa using Nat.prod_primeFactors_of_squarefree hsq

/--
If `n` is squarefree, then `n` factors as the product of its prime support.
-/
theorem exists_eq_supportProd_primeSupport {n : ℕ}
    (hsq : Squarefree n) :
    n = supportProd (primeSupport n) := by
  simpa using (supportProd_primeSupport_of_squarefree hsq).symm

end Basic
end Lehmer