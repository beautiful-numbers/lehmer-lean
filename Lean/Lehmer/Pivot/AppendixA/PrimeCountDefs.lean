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

This file contains the minimal finite prime-counting layer used in Appendix A.

Scope:
* finite prime sets and counting only;
* no `UBm`;
* no interval upper-bound API;
* no analytic estimates.
-/

/-- Finite set of primes in the closed interval `[a, b]`. -/
def primesInIcc (a b : ℕ) : Finset ℕ :=
  (Finset.Icc a b).filter Nat.Prime

/-- Finite set of primes at most `x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- Prime-counting function on naturals: the number of primes `≤ x`. -/
def primePi (x : ℕ) : ℕ :=
  (primesUpTo x).card

/-- Number of primes in the closed interval `[a,b]`. -/
def primeCountInIcc (a b : ℕ) : ℕ :=
  (primesInIcc a b).card

@[simp] theorem primesInIcc_def (a b : ℕ) :
    primesInIcc a b = (Finset.Icc a b).filter Nat.Prime := rfl

@[simp] theorem primesUpTo_def (x : ℕ) :
    primesUpTo x = (Finset.range (x + 1)).filter Nat.Prime := rfl

@[simp] theorem primePi_def (x : ℕ) :
    primePi x = (primesUpTo x).card := rfl

@[simp] theorem primeCountInIcc_def (a b : ℕ) :
    primeCountInIcc a b = (primesInIcc a b).card := rfl

/-- Membership in `primesInIcc a b`. -/
theorem mem_primesInIcc_iff
    {a b p : ℕ} :
    p ∈ primesInIcc a b ↔ a ≤ p ∧ p ≤ b ∧ Nat.Prime p := by
  simp [primesInIcc, and_left_comm, and_assoc]

/-- Membership in `primesUpTo x`. -/
theorem mem_primesUpTo_iff
    {x p : ℕ} :
    p ∈ primesUpTo x ↔ p ≤ x ∧ Nat.Prime p := by
  simp [primesUpTo, Nat.lt_succ_iff]

/-- Every member of `primesInIcc a b` is prime. -/
theorem prime_of_mem_primesInIcc
    {a b p : ℕ}
    (hp : p ∈ primesInIcc a b) :
    Nat.Prime p := by
  exact (mem_primesInIcc_iff.mp hp).2.2

/-- Every member of `primesInIcc a b` lies in `[a,b]`. -/
theorem bounds_of_mem_primesInIcc
    {a b p : ℕ}
    (hp : p ∈ primesInIcc a b) :
    a ≤ p ∧ p ≤ b := by
  exact ⟨(mem_primesInIcc_iff.mp hp).1, (mem_primesInIcc_iff.mp hp).2.1⟩

/-- Every member of `primesUpTo x` is prime. -/
theorem prime_of_mem_primesUpTo
    {x p : ℕ}
    (hp : p ∈ primesUpTo x) :
    Nat.Prime p := by
  exact (mem_primesUpTo_iff.mp hp).2

/-- Every member of `primesUpTo x` is at most `x`. -/
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
    rcases mem_primesInIcc_iff.mp hp with ⟨ha, hb, hp'⟩
    exact ⟨mem_primesUpTo_iff.mpr ⟨hb, hp'⟩, ha⟩
  · rintro ⟨hp, ha⟩
    rcases mem_primesUpTo_iff.mp hp with ⟨hb, hp'⟩
    exact mem_primesInIcc_iff.mpr ⟨ha, hb, hp'⟩

/-- Every prime in `[a,b]` is also in `primesUpTo b`. -/
theorem mem_primesUpTo_of_mem_primesInIcc
    {a b p : ℕ}
    (hp : p ∈ primesInIcc a b) :
    p ∈ primesUpTo b := by
  rcases mem_primesInIcc_iff.mp hp with ⟨_, hb, hp'⟩
  exact mem_primesUpTo_iff.mpr ⟨hb, hp'⟩

/--
Set-theoretic decomposition:
primes up to `b` split into primes up to `a-1` and primes in `[a,b]`.
-/
theorem primesUpTo_disjUnion_primesInIcc
    (a b : ℕ)
    (hab : a ≤ b + 1) :
    primesUpTo b =
      (primesUpTo (a - 1)).disjUnion (primesInIcc a b)
        (by
          intro p hp1 hp2
          rcases mem_primesUpTo_iff.mp hp1 with ⟨h1, _⟩
          rcases mem_primesInIcc_iff.mp hp2 with ⟨h2, _, _⟩
          exact Nat.not_lt_of_ge h2 (Nat.lt_of_le_pred h1)) := by
  classical
  ext p
  constructor
  · intro hp
    by_cases hlt : p < a
    · apply Finset.mem_disjUnion.mpr
      left
      rcases mem_primesUpTo_iff.mp hp with ⟨_, hpprime⟩
      exact mem_primesUpTo_iff.mpr ⟨Nat.le_pred_of_lt hlt, hpprime⟩
    · apply Finset.mem_disjUnion.mpr
      right
      rcases mem_primesUpTo_iff.mp hp with ⟨hpb, hpprime⟩
      have ha : a ≤ p := Nat.le_of_not_lt hlt
      exact mem_primesInIcc_iff.mpr ⟨ha, hpb, hpprime⟩
  · intro hp
    rcases Finset.mem_disjUnion.mp hp with hp | hp
    · rcases mem_primesUpTo_iff.mp hp with ⟨hpa, hpprime⟩
      have hle : p ≤ b := by
        omega
      exact mem_primesUpTo_iff.mpr ⟨hle, hpprime⟩
    · exact mem_primesUpTo_of_mem_primesInIcc hp

/--
Cardinality formula:
the number of primes in `[a,b]` is `π(b) - π(a-1)`.
-/
theorem primeCountInIcc_eq_primePi_sub_pred
    (a b : ℕ)
    (hab : a ≤ b + 1) :
    primeCountInIcc a b = primePi b - primePi (a - 1) := by
  classical
  have hdisj := primesUpTo_disjUnion_primesInIcc a b hab
  rw [primeCountInIcc_def, primePi_def, primePi_def]
  rw [hdisj, Finset.card_disjUnion]
  omega

/--
Equivalent set-cardinality form:
`(primesInIcc a b).card = primePi b - primePi (a - 1)`.
-/
theorem card_primesInIcc_eq_primePi_sub_pred
    (a b : ℕ)
    (hab : a ≤ b + 1) :
    (primesInIcc a b).card = primePi b - primePi (a - 1) := by
  exact primeCountInIcc_eq_primePi_sub_pred a b hab

/--
Prime-endpoint form used in Appendix A:
if `a` is prime and `a ≤ b`, then the number of primes in `[a,b]` is
`π(b) - π(a) + 1`.
-/
theorem primeCountInIcc_eq_primePi_sub_primePi_add_one
    {a b : ℕ}
    (ha : Nat.Prime a)
    (hab : a ≤ b) :
    primeCountInIcc a b = primePi b - primePi a + 1 := by
  have hab' : a ≤ b + 1 := le_trans hab (Nat.le_succ _)
  rw [primeCountInIcc_eq_primePi_sub_pred a b hab']
  have hsplit : primePi a = primePi (a - 1) + 1 := by
    classical
    have hmem : a ∈ primesUpTo a := by
      exact mem_primesUpTo_iff.mpr ⟨le_rfl, ha⟩
    have hdecomp : primesUpTo a = insert a (primesUpTo (a - 1)) := by
      ext p
      constructor
      · intro hp
        by_cases hpa : p = a
        · simp [hpa]
        · rcases mem_primesUpTo_iff.mp hp with ⟨hple, hpprime⟩
          have hlt : p < a := lt_of_le_of_ne hple hpa
          simp [hpa, mem_primesUpTo_iff.mpr ⟨Nat.le_pred_of_lt hlt, hpprime⟩]
      · intro hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hmem
        · rcases mem_primesUpTo_iff.mp hp with ⟨hple, hpprime⟩
          have hle : p ≤ a := by omega
          exact mem_primesUpTo_iff.mpr ⟨hle, hpprime⟩
    rw [primePi_def, hdecomp, Finset.card_insert, primePi_def]
    · omega
    · intro hcontra
      rcases mem_primesUpTo_iff.mp hcontra with ⟨hle, _⟩
      exact Nat.not_lt_of_ge hle (ha.one_lt)
  omega

/--
Equivalent set-cardinality form with prime left endpoint:
if `a` is prime and `a ≤ b`, then
`(primesInIcc a b).card = primePi b - primePi a + 1`.
-/
theorem card_primesInIcc_eq_primePi_sub_primePi_add_one
    {a b : ℕ}
    (ha : Nat.Prime a)
    (hab : a ≤ b) :
    (primesInIcc a b).card = primePi b - primePi a + 1 := by
  exact primeCountInIcc_eq_primePi_sub_primePi_add_one ha hab

end AppendixA
end Pivot
end Lehmer