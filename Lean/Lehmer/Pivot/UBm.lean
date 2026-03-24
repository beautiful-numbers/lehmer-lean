-- FILE: Lean/Lehmer/Pivot/UBm.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.PrimeSupport : thm
- Lehmer.Pivot.Defs : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.PrimeSupport
import Lehmer.Pivot.Defs

namespace Lehmer
namespace Pivot

open scoped BigOperators
open Lehmer.Basic

/--
`PrimeGe y p` means that `p` is prime and lies above the pivot threshold `y`.
-/
def PrimeGe (y p : ℕ) : Prop :=
  Nat.Prime p ∧ y ≤ p

/--
The basic decreasing factor appearing in the pivot product.
-/
def pivotFactor (p : ℕ) : ℚ :=
  (p : ℚ) / ((p - 1 : ℕ) : ℚ)

@[simp] theorem pivotFactor_def (p : ℕ) :
    pivotFactor p = (p : ℚ) / ((p - 1 : ℕ) : ℚ) := rfl

/--
`nextPrimeGe y` is the least prime at least `y`.
-/
noncomputable def nextPrimeGe (y : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes y)

theorem nextPrimeGe_spec (y : ℕ) :
    y ≤ nextPrimeGe y ∧ Nat.Prime (nextPrimeGe y) := by
  simpa [nextPrimeGe] using Nat.find_spec (Nat.exists_infinite_primes y)

theorem nextPrimeGe_ge (y : ℕ) :
    y ≤ nextPrimeGe y := by
  exact (nextPrimeGe_spec y).1

theorem nextPrimeGe_prime (y : ℕ) :
    Nat.Prime (nextPrimeGe y) := by
  exact (nextPrimeGe_spec y).2

theorem nextPrimeGe_le_of_prime_ge {y p : ℕ}
    (hp : Nat.Prime p) (hypy : y ≤ p) :
    nextPrimeGe y ≤ p := by
  exact Nat.find_min' (Nat.exists_infinite_primes y) ⟨hypy, hp⟩

/--
The `i`-th prime in the increasing sequence of primes starting at threshold `y`.
This is an internal convenience object. The envelope `UBm` itself is defined
recursively in the same spirit as the paper.
-/
noncomputable def nthPrimeFrom (y : ℕ) : ℕ → ℕ
  | 0 => nextPrimeGe y
  | k + 1 => nthPrimeFrom (nextPrimeGe y + 1) k

@[simp] theorem nthPrimeFrom_zero (y : ℕ) :
    nthPrimeFrom y 0 = nextPrimeGe y := rfl

@[simp] theorem nthPrimeFrom_succ (y k : ℕ) :
    nthPrimeFrom y (k + 1) = nthPrimeFrom (nextPrimeGe y + 1) k := rfl

theorem nthPrimeFrom_prime (y : ℕ) (k : ℕ) :
    Nat.Prime (nthPrimeFrom y k) := by
  induction k generalizing y with
  | zero =>
      simpa using nextPrimeGe_prime y
  | succ k ih =>
      simpa [nthPrimeFrom_succ] using ih (nextPrimeGe y + 1)

theorem nthPrimeFrom_ge (y : ℕ) (k : ℕ) :
    y ≤ nthPrimeFrom y k := by
  induction k generalizing y with
  | zero =>
      simpa using nextPrimeGe_ge y
  | succ k ih =>
      calc
        y ≤ nextPrimeGe y := nextPrimeGe_ge y
        _ ≤ nextPrimeGe y + 1 := Nat.le_succ _
        _ ≤ nthPrimeFrom (nextPrimeGe y + 1) k := ih (nextPrimeGe y + 1)
        _ = nthPrimeFrom y (k + 1) := by simp [nthPrimeFrom_succ]

theorem nthPrimeFrom_strictMono (y : ℕ) :
    StrictMono (nthPrimeFrom y) := by
  intro a b hab
  induction hab generalizing y with
  | refl =>
      exact False.elim (Nat.lt_irrefl _)
  | @step b hab ih =>
      calc
        nthPrimeFrom y a < nthPrimeFrom (nextPrimeGe y + 1) a := by
          have hprime : Nat.Prime (nthPrimeFrom y a) := nthPrimeFrom_prime y a
          have hlt : nthPrimeFrom y a < nextPrimeGe y + 1 := by
            have hle : nextPrimeGe y ≤ nthPrimeFrom y a := by
              exact nextPrimeGe_le_of_prime_ge hprime (nthPrimeFrom_ge y a)
            exact lt_of_le_of_lt hle (Nat.lt_succ_self _)
          exact lt_of_lt_of_le hlt (nthPrimeFrom_ge (nextPrimeGe y + 1) a)
        _ < nthPrimeFrom (nextPrimeGe y + 1) b := ih (nextPrimeGe y + 1)
        _ = nthPrimeFrom y (b + 1) := by simp [nthPrimeFrom_succ]

/--
The finite set of the first `m` primes above `y`.
-/
noncomputable def firstPrimesFrom (y m : ℕ) : Finset ℕ :=
  (Finset.range m).image (nthPrimeFrom y)

theorem card_firstPrimesFrom (y m : ℕ) :
    (firstPrimesFrom y m).card = m := by
  classical
  unfold firstPrimesFrom
  rw [Finset.card_image_of_injective]
  · simp
  · exact (nthPrimeFrom_strictMono y).injective

theorem mem_firstPrimesFrom_prime {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    Nat.Prime p := by
  classical
  unfold firstPrimesFrom at hp
  rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
  exact nthPrimeFrom_prime y i

theorem mem_firstPrimesFrom_ge {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    y ≤ p := by
  classical
  unfold firstPrimesFrom at hp
  rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
  exact nthPrimeFrom_ge y i

/--
The canonical pivot envelope.
This is the recursive form matching the paper:
`UB0(y)=1`, and one adds the smallest available prime factor at each step.
-/
def UBm (y m : ℕ) : ℚ :=
  Nat.rec 1 (fun m _ => pivotFactor (nextPrimeGe y) * UBm (nextPrimeGe y + 1) m) m
termination_by m

@[simp] theorem UBm_zero (y : ℕ) :
    UBm y 0 = 1 := rfl

@[simp] theorem UBm_succ (y m : ℕ) :
    UBm y (m + 1) = pivotFactor (nextPrimeGe y) * UBm (nextPrimeGe y + 1) m := by
  rfl

/--
Positivity of a single pivot factor at a prime.
-/
theorem pivotFactor_pos_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 < pivotFactor p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp2
  have hnum : (0 : ℚ) < (p : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hp2)
  have hden : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by
    rw [Nat.cast_sub hp1]
    exact sub_pos.mpr (by exact_mod_cast hp2)
  exact div_pos hnum hden

theorem pivotFactor_nonneg_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ pivotFactor p := by
  exact le_of_lt (pivotFactor_pos_of_prime hp)

/--
Positivity of the canonical envelope.
-/
theorem UBm_pos (y m : ℕ) :
    0 < UBm y m := by
  induction m generalizing y with
  | zero =>
      simp [UBm_zero]
  | succ m ih =>
      rw [UBm_succ]
      exact mul_pos (pivotFactor_pos_of_prime (nextPrimeGe_prime y))
        (ih (nextPrimeGe y + 1))

theorem UBm_nonneg (y m : ℕ) :
    0 ≤ UBm y m := by
  exact le_of_lt (UBm_pos y m)

/--
The factor `p ↦ p/(p-1)` is antitone on integers `≥ 2`.
-/
theorem factor_antitone_on_two_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    pivotFactor b ≤ pivotFactor a := by
  have ha1 : 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha
  have hb : 2 ≤ b := le_trans ha hab
  have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
  have hdena : (0 : ℚ) < (((a - 1 : ℕ) : ℚ)) := by
    rw [Nat.cast_sub ha1]
    exact sub_pos.mpr (by exact_mod_cast ha)
  have hdenb : (0 : ℚ) < (((b - 1 : ℕ) : ℚ)) := by
    rw [Nat.cast_sub hb1]
    exact sub_pos.mpr (by exact_mod_cast hb)
  have hcross :
      (b : ℚ) * (((a - 1 : ℕ) : ℚ)) ≤
        (a : ℚ) * (((b - 1 : ℕ) : ℚ)) := by
    rw [Nat.cast_sub ha1, Nat.cast_sub hb1]
    ring_nf
    exact_mod_cast hab
  exact (div_le_div_iff hdenb hdena).2 hcross

/--
Antitonicity of the envelope in the pivot threshold:
if `y₁ ≤ y₂`, then `UBm y₂ m ≤ UBm y₁ m`.
-/
theorem UBm_antitone_in_y {y₁ y₂ m : ℕ} (hy : y₁ ≤ y₂) :
    UBm y₂ m ≤ UBm y₁ m := by
  induction m generalizing y₁ y₂ with
  | zero =>
      simp
  | succ m ih =>
      rw [UBm_succ, UBm_succ]
      have hprime1 : Nat.Prime (nextPrimeGe y₁) := nextPrimeGe_prime y₁
      have hprime2 : Nat.Prime (nextPrimeGe y₂) := nextPrimeGe_prime y₂
      have hnext : nextPrimeGe y₁ ≤ nextPrimeGe y₂ := by
        exact nextPrimeGe_le_of_prime_ge hprime2 (le_trans hy (nextPrimeGe_ge y₂))
      have hhead :
          pivotFactor (nextPrimeGe y₂) ≤ pivotFactor (nextPrimeGe y₁) := by
        exact factor_antitone_on_two_le hprime1.two_le hnext
      have htail :
          UBm (nextPrimeGe y₂ + 1) m ≤ UBm (nextPrimeGe y₁ + 1) m := by
        exact ih (Nat.succ_le_succ hnext)
      exact mul_le_mul hhead htail
        (UBm_nonneg _ _) (pivotFactor_nonneg_of_prime hprime1)

/--
Product positivity for a finite prime support.
-/
theorem prod_pivotFactor_pos_of_all_prime {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    0 < S.prod pivotFactor := by
  classical
  refine Finset.prod_pos ?_
  intro p hp
  exact pivotFactor_pos_of_prime (hprime p hp)

/--
Core extremal comparison:
among finite sets of primes all `≥ y`, the product of `pivotFactor`
is maximized by the canonical envelope with the same cardinality.
-/
theorem worst_case_monotone_envelope {y : ℕ} :
    ∀ S : Finset ℕ,
      (∀ p ∈ S, Nat.Prime p) →
      (∀ p ∈ S, y ≤ p) →
      S.prod pivotFactor ≤ UBm y S.card := by
  classical
  refine Finset.induction_on ?S ?h0 ?hstep
  · intro _ _
    simp [UBm_zero]
  · intro a S ha ih hprime hge
    have ha_prime : Nat.Prime a := hprime a (by simp)
    have hy_a : y ≤ a := hge a (by simp)
    have hS_prime : ∀ p ∈ S, Nat.Prime p := by
      intro p hp
      exact hprime p (by simp [hp])
    have hS_ge : ∀ p ∈ S, y ≤ p := by
      intro p hp
      exact hge p (by simp [hp])
    have hSa : ∀ p ∈ S, a + 1 ≤ p := by
      intro p hp
      have hneq : p ≠ a := by
        intro hpeq
        subst hpeq
        exact ha hp
      have hmin : a ≤ p := by
        have hp' : p ∈ insert a S := by simp [hp]
        exact Finset.min'_le (insert a S) p hp'
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hmin hneq)
    have hnext_le_a : nextPrimeGe y ≤ a := by
      exact nextPrimeGe_le_of_prime_ge ha_prime hy_a
    have hhead :
        pivotFactor a ≤ pivotFactor (nextPrimeGe y) := by
      exact factor_antitone_on_two_le (nextPrimeGe_prime y).two_le hnext_le_a
    have htail :
        S.prod pivotFactor ≤ UBm (a + 1) S.card := by
      exact ih hS_prime hSa
    have htail' :
        UBm (a + 1) S.card ≤ UBm (nextPrimeGe y + 1) S.card := by
      exact UBm_antitone_in_y (Nat.succ_le_succ hnext_le_a)
    have hprod_nonneg : 0 ≤ S.prod pivotFactor := by
      exact le_of_lt (prod_pivotFactor_pos_of_all_prime hS_prime)
    calc
      (insert a S).prod pivotFactor
          = pivotFactor a * S.prod pivotFactor := by
              rw [Finset.prod_insert ha]
      _ ≤ pivotFactor (nextPrimeGe y) * UBm (nextPrimeGe y + 1) S.card := by
          exact mul_le_mul hhead (le_trans htail htail')
            hprod_nonneg (pivotFactor_nonneg_of_prime (nextPrimeGe_prime y))
      _ = UBm y (S.card + 1) := by
          rw [UBm_succ]
      _ = UBm y (Finset.card (insert a S)) := by
          simp [Finset.card_insert_of_not_mem ha]

/--
Application of the extremal envelope to a `y`-rough prime support.
-/
theorem prod_primeSupport_le_UBm_of_yrough {y n : ℕ} (hy : YRough y n) :
    (primeSupport n).prod pivotFactor ≤ UBm y (primeSupport n).card := by
  apply worst_case_monotone_envelope
  · intro p hp
    exact prime_of_mem_primeSupport hp
  · intro p hp
    exact hy p (prime_of_mem_primeSupport hp) (dvd_of_mem_primeSupport hp)

end Pivot
end Lehmer