import Mathlib
import Lehmer.Basic.Defs

namespace Lehmer
namespace Basic

@[simp] theorem supportLcm_empty :
    supportLcm (∅ : Finset ℕ) = 1 := by
  simp [supportLcm]

@[simp] theorem supportLcm_singleton (p : ℕ) :
    supportLcm ({p} : Finset ℕ) = p - 1 := by
  simp [supportLcm]

@[simp] theorem supportLcm_insert {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) :
    supportLcm (insert p S) = Nat.lcm (p - 1) (supportLcm S) := by
  simp [supportLcm, hp]

/-- For every `p ∈ S`, the shifted prime `p - 1` divides `supportLcm S`. -/
theorem sub_dvd_supportLcm {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    p - 1 ∣ supportLcm S := by
  exact Finset.dvd_lcm hp

/-- A support lcm is positive. -/
theorem supportLcm_pos (S : Finset ℕ) :
    0 < supportLcm S := by
  exact Nat.succ_pos _

/-- A support lcm is nonzero. -/
theorem supportLcm_ne_zero (S : Finset ℕ) :
    supportLcm S ≠ 0 := by
  exact Nat.ne_of_gt (supportLcm_pos S)

/-- Monotonicity of divisibility along support inclusion. -/
theorem supportLcm_dvd_of_subset {S T : Finset ℕ} (hST : S ⊆ T) :
    supportLcm S ∣ supportLcm T := by
  refine Finset.lcm_dvd ?_
  intro p hp
  exact dvd_trans (sub_dvd_supportLcm hp) (sub_dvd_supportLcm (hST hp))

/-- If every shifted support element divides `m`, then `supportLcm S ∣ m`. -/
theorem supportLcm_dvd_of_forall_dvd {S : Finset ℕ} {m : ℕ}
    (hS : ∀ p ∈ S, p - 1 ∣ m) :
    supportLcm S ∣ m := by
  refine Finset.lcm_dvd ?_
  intro p hp
  exact hS p hp

/-- If all support elements are at least `2`, then every shifted support element is nonzero. -/
theorem sub_ne_zero_of_two_le {S : Finset ℕ}
    (hS : ∀ p ∈ S, 2 ≤ p) :
    ∀ p ∈ S, p - 1 ≠ 0 := by
  intro p hp
  have hp2 : 2 ≤ p := hS p hp
  omega

/-- If all elements of `S` are prime, then every shifted support element is positive. -/
theorem sub_pos_of_prime_mem {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    ∀ p ∈ S, 0 < p - 1 := by
  intro p hp
  have hp2 : 2 ≤ p := (hS p hp).two_le
  omega

/-- If all elements of `S` are prime, then `supportLcm S` is the lcm of positive integers. -/
theorem supportLcm_pos_of_all_prime {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    0 < supportLcm S := by
  exact supportLcm_pos S

/-- A useful API lemma: every member of the support contributes a divisor to the support lcm. -/
theorem dvd_supportLcm_of_mem {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    p - 1 ∣ supportLcm S := by
  exact sub_dvd_supportLcm hp

end Basic
end Lehmer