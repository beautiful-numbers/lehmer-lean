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

def PrimeGe (y p : ℕ) : Prop :=
  Nat.Prime p ∧ y ≤ p

def pivotFactor (p : ℕ) : ℚ :=
  (p : ℚ) / ((p - 1 : ℕ) : ℚ)

@[simp] theorem pivotFactor_def (p : ℕ) :
    pivotFactor p = (p : ℚ) / ((p - 1 : ℕ) : ℚ) := rfl

noncomputable def nextPrimeGe (y : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes y)

theorem nextPrimeGe_spec (y : ℕ) :
    y ≤ nextPrimeGe y ∧ Nat.Prime (nextPrimeGe y) := by
  have h := Nat.find_spec (Nat.exists_infinite_primes y)
  exact h

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

noncomputable def nthPrimeFrom (y : ℕ) : ℕ → ℕ
  | 0 => nextPrimeGe y
  | k + 1 => nextPrimeGe (nthPrimeFrom y k + 1)

@[simp] theorem nthPrimeFrom_zero (y : ℕ) :
    nthPrimeFrom y 0 = nextPrimeGe y := rfl

@[simp] theorem nthPrimeFrom_succ (y k : ℕ) :
    nthPrimeFrom y (k + 1) = nextPrimeGe (nthPrimeFrom y k + 1) := rfl

theorem nthPrimeFrom_prime (y : ℕ) (k : ℕ) :
    Nat.Prime (nthPrimeFrom y k) := by
  induction k with
  | zero =>
      exact nextPrimeGe_prime y
  | succ k ih =>
      exact nextPrimeGe_prime (nthPrimeFrom y k + 1)

theorem nthPrimeFrom_ge (y : ℕ) (k : ℕ) :
    y ≤ nthPrimeFrom y k := by
  induction k with
  | zero =>
      exact nextPrimeGe_ge y
  | succ k ih =>
      have hstep : nthPrimeFrom y k + 1 ≤ nthPrimeFrom y (k + 1) := by
        exact nextPrimeGe_ge (nthPrimeFrom y k + 1)
      exact le_trans ih (le_trans (Nat.le_succ _) hstep)

theorem nthPrimeFrom_lt_succ (y : ℕ) (k : ℕ) :
    nthPrimeFrom y k < nthPrimeFrom y (k + 1) := by
  have hstep : nthPrimeFrom y k + 1 ≤ nthPrimeFrom y (k + 1) := by
    exact nextPrimeGe_ge (nthPrimeFrom y k + 1)
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hstep

theorem nthPrimeFrom_strictMono (y : ℕ) :
    StrictMono (nthPrimeFrom y) := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  exact nthPrimeFrom_lt_succ y k

noncomputable def firstPrimesFrom (y m : ℕ) : Finset ℕ :=
  (Finset.range m).image (nthPrimeFrom y)

theorem card_firstPrimesFrom (y m : ℕ) :
    (firstPrimesFrom y m).card = m := by
  classical
  unfold firstPrimesFrom
  rw[Finset.card_image_of_injective]
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

noncomputable def UBm (y : ℕ) : ℕ → ℚ
  | 0 => 1
  | m + 1 => pivotFactor (nextPrimeGe y) * UBm (nextPrimeGe y + 1) m

@[simp] theorem UBm_zero (y : ℕ) :
    UBm y 0 = 1 := rfl

@[simp] theorem UBm_succ (y m : ℕ) :
    UBm y (m + 1) = pivotFactor (nextPrimeGe y) * UBm (nextPrimeGe y + 1) m := rfl

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

theorem pivotFactor_eq_one_add_inv {p : ℕ} (hp : 2 ≤ p) :
    pivotFactor p = 1 + 1 / (((p - 1 : ℕ) : ℚ)) := by
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp
  have hden : (((p - 1 : ℕ) : ℚ)) ≠ 0 := by
    have hpnz : (p - 1 : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hp)
    intro hq
    have : (p - 1 : ℕ) = 0 := by exact_mod_cast hq
    exact hpnz this
  rw [pivotFactor_def]
  have hrepr : (p : ℚ) = (((p - 1 : ℕ) : ℚ)) + 1 := by
    rw[Nat.cast_sub hp1]
    try ring
  rw [hrepr]
  field_simp[hden]
  try ring

theorem UBm_pos (y m : ℕ) :
    0 < UBm y m := by
  induction m generalizing y with
  | zero => simp[UBm_zero]
  | succ m ih =>
      rw [UBm_succ]
      exact mul_pos (pivotFactor_pos_of_prime (nextPrimeGe_prime y)) (ih (nextPrimeGe y + 1))

theorem UBm_nonneg (y m : ℕ) :
    0 ≤ UBm y m := by
  exact le_of_lt (UBm_pos y m)

theorem factor_antitone_on_two_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    pivotFactor b ≤ pivotFactor a := by
  have hb : 2 ≤ b := le_trans ha hab
  have hqa : (0 : ℚ) < (((a - 1 : ℕ) : ℚ)) := by
    have ha1 : 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha
    rw[Nat.cast_sub ha1]
    exact sub_pos.mpr (by exact_mod_cast ha)
  have hqb : (0 : ℚ) < (((b - 1 : ℕ) : ℚ)) := by
    have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
    rw[Nat.cast_sub hb1]
    exact sub_pos.mpr (by exact_mod_cast hb)
  have hsub : (((a - 1 : ℕ) : ℚ)) ≤ (((b - 1 : ℕ) : ℚ)) := by
    have ha1 : 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha
    have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
    rw[Nat.cast_sub ha1, Nat.cast_sub hb1]
    have habQ : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
    linarith
  have hone : 1 / (((b - 1 : ℕ) : ℚ)) ≤ 1 / (((a - 1 : ℕ) : ℚ)) := by
    have h_mul_pos : 0 < (((a - 1 : ℕ) : ℚ)) * (((b - 1 : ℕ) : ℚ)) := mul_pos hqa hqb
    have h_diff : 0 ≤ (((b - 1 : ℕ) : ℚ)) - (((a - 1 : ℕ) : ℚ)) := sub_nonneg.mpr hsub
    have h_div : 0 ≤ ((((b - 1 : ℕ) : ℚ)) - (((a - 1 : ℕ) : ℚ))) / ((((a - 1 : ℕ) : ℚ)) * (((b - 1 : ℕ) : ℚ))) := div_nonneg h_diff (le_of_lt h_mul_pos)
    have h_eq : ((((b - 1 : ℕ) : ℚ)) - (((a - 1 : ℕ) : ℚ))) / ((((a - 1 : ℕ) : ℚ)) * (((b - 1 : ℕ) : ℚ))) = 1 / (((a - 1 : ℕ) : ℚ)) - 1 / (((b - 1 : ℕ) : ℚ)) := by
      have hane : (((a - 1 : ℕ) : ℚ)) ≠ 0 := ne_of_gt hqa
      have hbne : (((b - 1 : ℕ) : ℚ)) ≠ 0 := ne_of_gt hqb
      field_simp [hane, hbne]
      try ring
    have h_diff2 : 0 ≤ 1 / (((a - 1 : ℕ) : ℚ)) - 1 / (((b - 1 : ℕ) : ℚ)) := by
      rw[← h_eq]
      exact h_div
    exact sub_nonneg.mp h_diff2
  rw[pivotFactor_eq_one_add_inv hb, pivotFactor_eq_one_add_inv ha]
  linarith[hone]

theorem UBm_antitone_in_y {y₁ y₂ m : ℕ} (hy : y₁ ≤ y₂) :
    UBm y₂ m ≤ UBm y₁ m := by
  induction m generalizing y₁ y₂ with
  | zero => simp
  | succ m ih =>
      rw[UBm_succ, UBm_succ]
      have hprime1 : Nat.Prime (nextPrimeGe y₁) := nextPrimeGe_prime y₁
      have hprime2 : Nat.Prime (nextPrimeGe y₂) := nextPrimeGe_prime y₂
      have hnext : nextPrimeGe y₁ ≤ nextPrimeGe y₂ := by
        exact nextPrimeGe_le_of_prime_ge hprime2 (le_trans hy (nextPrimeGe_ge y₂))
      have hhead : pivotFactor (nextPrimeGe y₂) ≤ pivotFactor (nextPrimeGe y₁) := by
        exact factor_antitone_on_two_le hprime1.two_le hnext
      have htail : UBm (nextPrimeGe y₂ + 1) m ≤ UBm (nextPrimeGe y₁ + 1) m := by
        exact ih (Nat.succ_le_succ hnext)
      exact mul_le_mul hhead htail (UBm_nonneg _ _) (pivotFactor_nonneg_of_prime hprime1)

theorem prod_pivotFactor_pos_of_all_prime {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    0 < S.prod pivotFactor := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha_prime : Nat.Prime a := hprime a (by simp)
      have hs_prime : ∀ p ∈ s, Nat.Prime p := by
        intro p hp
        exact hprime p (by simp [hp])
      rw[Finset.prod_insert ha]
      exact mul_pos (pivotFactor_pos_of_prime ha_prime) (ih hs_prime)

theorem worst_case_monotone_envelope :
    ∀ S : Finset ℕ, ∀ y : ℕ,
      (∀ p ∈ S, Nat.Prime p) →
      (∀ p ∈ S, y ≤ p) →
      S.prod pivotFactor ≤ UBm y S.card := by
  intro S
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih y hprime hge
  by_cases hS : S.Nonempty
  · let a : ℕ := S.min' hS
    let T : Finset ℕ := S.erase a
    have ha_mem : a ∈ S := Finset.min'_mem S hS
    have ha_prime : Nat.Prime a := hprime a ha_mem
    have hy_a : y ≤ a := hge a ha_mem
    have hT_ss : T ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      constructor
      · intro x hx
        exact Finset.mem_of_mem_erase hx
      · intro hEq
        have : a ∈ T := by simpa [hEq] using ha_mem
        exact (Finset.mem_erase.mp this).1 rfl
    have hT_prime : ∀ p ∈ T, Nat.Prime p := by
      intro p hp
      exact hprime p (Finset.mem_of_mem_erase hp)
    have hT_ge : ∀ p ∈ T, a + 1 ≤ p := by
      intro p hp
      have hpS : p ∈ S := Finset.mem_of_mem_erase hp
      have hmin : a ≤ p := Finset.min'_le S p hpS
      have hne : a ≠ p := Ne.symm ((Finset.mem_erase.mp hp).1)
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hmin hne)
    have htail : T.prod pivotFactor ≤ UBm (a + 1) T.card := by
      exact ih T hT_ss (a + 1) hT_prime hT_ge
    have hnext_le_a : nextPrimeGe y ≤ a := by
      exact nextPrimeGe_le_of_prime_ge ha_prime hy_a
    have hhead : pivotFactor a ≤ pivotFactor (nextPrimeGe y) := by
      exact factor_antitone_on_two_le (nextPrimeGe_prime y).two_le hnext_le_a
    have hprod_nonneg : 0 ≤ T.prod pivotFactor := by
      exact le_of_lt (prod_pivotFactor_pos_of_all_prime hT_prime)
    calc
      S.prod pivotFactor
          = pivotFactor a * T.prod pivotFactor := by
              dsimp[T, a]
              have h_ins : insert a (S.erase a) = S := Finset.insert_erase ha_mem
              have h_not_mem : a ∉ S.erase a := by simp
              calc
                S.prod pivotFactor = (insert a (S.erase a)).prod pivotFactor := by rw[h_ins]
                _ = pivotFactor a * (S.erase a).prod pivotFactor := Finset.prod_insert h_not_mem
      _ ≤ pivotFactor (nextPrimeGe y) * UBm (a + 1) T.card := by
          exact mul_le_mul hhead htail hprod_nonneg (pivotFactor_nonneg_of_prime (nextPrimeGe_prime y))
      _ ≤ pivotFactor (nextPrimeGe y) * UBm (nextPrimeGe y + 1) T.card := by
          have htail' : UBm (a + 1) T.card ≤ UBm (nextPrimeGe y + 1) T.card := by
            exact UBm_antitone_in_y (Nat.succ_le_succ hnext_le_a)
          exact mul_le_mul_of_nonneg_left htail' (pivotFactor_nonneg_of_prime (nextPrimeGe_prime y))
      _ = UBm y (T.card + 1) := by
          rw [UBm_succ]
      _ = UBm y S.card := by
          have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha_mem
          rw [hcard]
  · have hSE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst hSE
    simp[UBm_zero]

theorem prod_primeSupport_le_UBm_of_yrough {y n : ℕ} (hy : YRough y n) :
    (primeSupport n).prod pivotFactor ≤ UBm y (primeSupport n).card := by
  apply worst_case_monotone_envelope (primeSupport n) y
  · intro p hp
    exact prime_of_mem_primeSupport hp
  · intro p hp
    exact hy p (prime_of_mem_primeSupport hp) (dvd_of_mem_primeSupport hp)

end Pivot
end Lehmer