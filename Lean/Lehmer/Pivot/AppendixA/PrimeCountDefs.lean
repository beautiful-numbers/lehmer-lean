-- FILE: Lean/Lehmer/Pivot/AppendixA/PrimeCountDefs.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
-/

import Lehmer.Prelude

open Finset

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A prime-counting definitions

This file introduces only the finite prime-counting objects needed by the
Appendix A bridge layer.

Important scope:
* purely definitional / finite-set level;
* no analytic estimates;
* no `UBm` yet;
* no `mreq` yet.
-/

/--
Finite set of primes in the closed interval `[a, b]`.
-/
def primesInIcc (a b : ℕ) : Finset ℕ :=
  (Finset.Icc a b).filter Nat.Prime

/--
Finite set of primes at most `x`.
-/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/--
Prime-counting function on naturals:
the number of primes `≤ x`.
-/
def primePi (x : ℕ) : ℕ :=
  (primesUpTo x).card

@[simp] theorem primesInIcc_def (a b : ℕ) :
    primesInIcc a b = (Finset.Icc a b).filter Nat.Prime := rfl

@[simp] theorem primesUpTo_def (x : ℕ) :
    primesUpTo x = (Finset.range (x + 1)).filter Nat.Prime := rfl

@[simp] theorem primePi_def (x : ℕ) :
    primePi x = (primesUpTo x).card := rfl

/--
Membership in `primesInIcc a b`.
-/
theorem mem_primesInIcc_iff
    {a b p : ℕ} :
    p ∈ primesInIcc a b ↔ a ≤ p ∧ p ≤ b ∧ Nat.Prime p := by
  simp [primesInIcc, and_left_comm, and_assoc]

/--
Membership in `primesUpTo x`.
-/
theorem mem_primesUpTo_iff
    {x p : ℕ} :
    p ∈ primesUpTo x ↔ p ≤ x ∧ Nat.Prime p := by
  simp [primesUpTo, Nat.lt_succ_iff]

/--
Every member of `primesInIcc a b` is prime.
-/
theorem prime_of_mem_primesInIcc
    {a b p : ℕ}
    (hp : p ∈ primesInIcc a b) :
    Nat.Prime p := by
  exact (mem_primesInIcc_iff.mp hp).2.2

/--
Every member of `primesInIcc a b` lies in `[a,b]`.
-/
theorem bounds_of_mem_primesInIcc
    {a b p : ℕ}
    (hp : p ∈ primesInIcc a b) :
    a ≤ p ∧ p ≤ b := by
  exact ⟨(mem_primesInIcc_iff.mp hp).1, (mem_primesInIcc_iff.mp hp).2.1⟩

/--
Every member of `primesUpTo x` is prime.
-/
theorem prime_of_mem_primesUpTo
    {x p : ℕ}
    (hp : p ∈ primesUpTo x) :
    Nat.Prime p := by
  exact (mem_primesUpTo_iff.mp hp).2

/--
Every member of `primesUpTo x` is at most `x`.
-/
theorem le_of_mem_primesUpTo
    {x p : ℕ}
    (hp : p ∈ primesUpTo x) :
    p ≤ x := by
  exact (mem_primesUpTo_iff.mp hp).1

/--
Primes in `[a,b]` are exactly primes `≤ b` and `≥ a`.
-/
theorem mem_primesInIcc_iff_mem_primesUpTo
    {a b p : ℕ} :
    p ∈ primesInIcc a b ↔ p ∈ primesUpTo b ∧ a ≤ p := by
  constructor
  · intro hp
    rcases mem_primesInIcc_iff.mp hp with ⟨h1, h2, hp'⟩
    exact ⟨mem_primesUpTo_iff.mpr ⟨h2, hp'⟩, h1⟩
  · rintro ⟨hp, ha⟩
    rcases mem_primesUpTo_iff.mp hp with ⟨hb, hp'⟩
    exact mem_primesInIcc_iff.mpr ⟨ha, hb, hp'⟩

/--
The prime-counting function counts `primesUpTo`.
-/
theorem primePi_eq_card_primesUpTo
    (x : ℕ) :
    primePi x = (primesUpTo x).card := rfl

/--
If `a ≤ b`, then every prime in `[a,b]` is also in `primesUpTo b`.
-/
theorem mem_primesUpTo_of_mem_primesInIcc
    {a b p : ℕ}
    (hp : p ∈ primesInIcc a b) :
    p ∈ primesUpTo b := by
  rcases mem_primesInIcc_iff.mp hp with ⟨_ha, hb, hp'⟩
  exact mem_primesUpTo_iff.mpr ⟨hb, hp'⟩

end AppendixA
end Pivot
end Lehmer