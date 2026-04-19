-- FILE: Lean/Lehmer/Support/IncrementRatio.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.PrimeSupport : thm
- Lehmer.Basic.SupportLcm : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.PrimeSupport
import Lehmer.Basic.SupportLcm

namespace Lehmer
namespace Support

open Lehmer.Basic

/-!
# Increment ratio on supports

This file introduces the low-level support increment ratio attached to the
modular resource `supportLcm`. It provides only the local plumbing needed for
the subsequent increment-identity layer.
-/

/--
Support-level increment ratio obtained by removing `p` from the support `S`.

This is the quotient of the ambient modular resource by the modular resource of
the erased support.
-/
def incrementRatio (S : Finset ℕ) (p : ℕ) : ℕ :=
  supportLcm S / supportLcm (S.erase p)

@[simp] theorem incrementRatio_def (S : Finset ℕ) (p : ℕ) :
    incrementRatio S p = supportLcm S / supportLcm (S.erase p) := rfl

/-- The erased support is a subset of the original support. -/
theorem erase_subset (S : Finset ℕ) (p : ℕ) :
    S.erase p ⊆ S := by
  intro q hq
  exact Finset.mem_of_mem_erase hq

/--
The modular resource of the erased support divides the ambient modular
resource.
-/
theorem supportLcm_erase_dvd (S : Finset ℕ) (p : ℕ) :
    supportLcm (S.erase p) ∣ supportLcm S := by
  exact supportLcm_dvd_of_subset (erase_subset S p)

/--
Exact quotient identity for the increment ratio.
-/
theorem incrementRatio_mul_supportLcm_erase (S : Finset ℕ) (p : ℕ) :
    incrementRatio S p * supportLcm (S.erase p) = supportLcm S := by
  unfold incrementRatio
  exact Nat.div_mul_cancel (supportLcm_erase_dvd S p)

/--
Rewriting form of the quotient identity.
-/
theorem supportLcm_eq_incrementRatio_mul_supportLcm_erase (S : Finset ℕ) (p : ℕ) :
    supportLcm S = incrementRatio S p * supportLcm (S.erase p) := by
  symm
  exact incrementRatio_mul_supportLcm_erase S p

/--
The increment ratio divides the ambient modular resource.
-/
theorem incrementRatio_dvd_supportLcm (S : Finset ℕ) (p : ℕ) :
    incrementRatio S p ∣ supportLcm S := by
  refine ⟨supportLcm (S.erase p), ?_⟩
  exact supportLcm_eq_incrementRatio_mul_supportLcm_erase S p

/--
If all members of the support are prime, then the erased support also has
positive modular resource.
-/
theorem supportLcm_erase_pos_of_all_prime {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    0 < supportLcm (S.erase p) := by
  apply supportLcm_pos_of_all_prime
  intro q hq
  exact hS q (Finset.mem_of_mem_erase hq)

/--
If all members of the support are prime, then the erased support has nonzero
modular resource.
-/
theorem supportLcm_erase_ne_zero_of_all_prime {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    supportLcm (S.erase p) ≠ 0 := by
  exact Nat.ne_of_gt (supportLcm_erase_pos_of_all_prime hS)

/--
If all members of the support are prime, then the increment ratio is positive.
-/
theorem incrementRatio_pos_of_all_prime {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    0 < incrementRatio S p := by
  have hLpos : 0 < supportLcm S := supportLcm_pos_of_all_prime hS
  have hEq : incrementRatio S p * supportLcm (S.erase p) = supportLcm S :=
    incrementRatio_mul_supportLcm_erase S p
  have hne : incrementRatio S p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hEq
    exact (Nat.ne_of_gt hLpos) hEq.symm
  exact Nat.pos_iff_ne_zero.mpr hne

/--
If all members of the support are prime, then the increment ratio is nonzero.
-/
theorem incrementRatio_ne_zero_of_all_prime {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    incrementRatio S p ≠ 0 := by
  exact Nat.ne_of_gt (incrementRatio_pos_of_all_prime hS)

/--
If all members of the support are prime, then the increment ratio is at least
`1`.
-/
theorem one_le_incrementRatio_of_all_prime {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    1 ≤ incrementRatio S p := by
  exact Nat.succ_le_of_lt (incrementRatio_pos_of_all_prime hS)

/--
Active-case denominator nonvanishing: under membership and primality of the
support, the erased support still has nonzero modular resource.
-/
theorem supportLcm_erase_ne_zero_of_mem_of_all_prime {S : Finset ℕ} {p : ℕ}
    (_hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    supportLcm (S.erase p) ≠ 0 := by
  exact supportLcm_erase_ne_zero_of_all_prime hS

/--
If `p ∉ S`, then removing `p` does not change the support and the increment
ratio is `1`, under the standard prime-support positivity hypothesis.
-/
theorem incrementRatio_eq_one_of_not_mem_of_all_prime
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∉ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    incrementRatio S p = 1 := by
  have hpos : 0 < supportLcm S := supportLcm_pos_of_all_prime hS
  have hErase : S.erase p = S := by
    ext q
    by_cases hqp : q = p
    · subst hqp
      simp [hp]
    · simp [hp]
  unfold incrementRatio
  rw [hErase]
  exact Nat.div_self hpos

end Support
end Lehmer