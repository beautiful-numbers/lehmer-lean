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

/-- Prime and at least `y`. -/
def PrimeGe (y p : ℕ) : Prop :=
  Nat.Prime p ∧ y ≤ p

/-- The factor `p / (p - 1)` appearing in the pivot products. -/
def pivotFactor (p : ℕ) : ℚ :=
  (p : ℚ) / ((p - 1 : ℕ) : ℚ)

@[simp] theorem pivotFactor_def (p : ℕ) :
    pivotFactor p = (p : ℚ) / ((p - 1 : ℕ) : ℚ) := rfl

/-- Least prime at least `y`. -/
noncomputable def nextPrimeGe (y : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes y)

theorem nextPrimeGe_spec (y : ℕ) :
    y ≤ nextPrimeGe y ∧ Nat.Prime (nextPrimeGe y) := by
  exact Nat.find_spec (Nat.exists_infinite_primes y)

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
Paper-facing prime sequence.

`py y i` is intended to represent `p_{y,i}` for `i ≥ 1`.
We keep the dummy value `py y 0 = 0` only to stay in `ℕ → ℕ`.
-/
noncomputable def py (y : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => nextPrimeGe y
  | i + 2 => nextPrimeGe (py y (i + 1) + 1)

@[simp] theorem py_zero (y : ℕ) :
    py y 0 = 0 := rfl

@[simp] theorem py_one (y : ℕ) :
    py y 1 = nextPrimeGe y := rfl

@[simp] theorem py_succ_succ (y i : ℕ) :
    py y (i + 2) = nextPrimeGe (py y (i + 1) + 1) := rfl

/-- Internal shifted sequence indexed from `0`. -/
noncomputable def py0 (y : ℕ) (k : ℕ) : ℕ :=
  py y (k + 1)

@[simp] theorem py0_def (y k : ℕ) :
    py0 y k = py y (k + 1) := rfl

@[simp] theorem py0_zero (y : ℕ) :
    py0 y 0 = nextPrimeGe y := rfl

@[simp] theorem py0_succ (y k : ℕ) :
    py0 y (k + 1) = nextPrimeGe (py0 y k + 1) := rfl

theorem py_prime_of_one_le {y i : ℕ} (hi : 1 ≤ i) :
    Nat.Prime (py y i) := by
  have h_ex : ∃ k, i = k + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hi)
  rcases h_ex with ⟨k, rfl⟩
  cases k with
  | zero =>
      exact nextPrimeGe_prime y
  | succ k =>
      have h : py y (k + 1 + 1) = nextPrimeGe (py y (k + 1) + 1) := rfl
      rw [h]
      exact nextPrimeGe_prime _

theorem py_ge_of_one_le {y i : ℕ} (hi : 1 ≤ i) :
    y ≤ py y i := by
  have h_ex : ∃ k, i = k + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hi)
  rcases h_ex with ⟨k, rfl⟩
  clear hi
  induction k with
  | zero =>
      exact nextPrimeGe_ge y
  | succ k ih =>
      have h1 : py y (k + 1) + 1 ≤ nextPrimeGe (py y (k + 1) + 1) := nextPrimeGe_ge _
      have h2 : py y (k + 1 + 1) = nextPrimeGe (py y (k + 1) + 1) := rfl
      rw [h2]
      exact le_trans ih (le_trans (Nat.le_succ _) h1)

theorem py_lt_succ_of_one_le {y i : ℕ} (hi : 1 ≤ i) :
    py y i < py y (i + 1) := by
  have h_ex : ∃ k, i = k + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hi)
  rcases h_ex with ⟨k, rfl⟩
  have h1 : py y (k + 1) + 1 ≤ nextPrimeGe (py y (k + 1) + 1) := nextPrimeGe_ge _
  have h2 : py y (k + 1 + 1) = nextPrimeGe (py y (k + 1) + 1) := rfl
  rw [h2]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) h1

theorem py0_prime (y k : ℕ) :
    Nat.Prime (py0 y k) := by
  exact py_prime_of_one_le (Nat.succ_le_succ (Nat.zero_le k))

theorem py0_ge (y k : ℕ) :
    y ≤ py0 y k := by
  exact py_ge_of_one_le (Nat.succ_le_succ (Nat.zero_le k))

theorem py0_lt_succ (y k : ℕ) :
    py0 y k < py0 y (k + 1) := by
  have h_eq : py0 y (k + 1) = nextPrimeGe (py0 y k + 1) := rfl
  rw [h_eq]
  have h1 : py0 y k + 1 ≤ nextPrimeGe (py0 y k + 1) := nextPrimeGe_ge _
  exact lt_of_lt_of_le (Nat.lt_succ_self _) h1

theorem py0_strictMono (y : ℕ) :
    StrictMono (py0 y) := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  exact py0_lt_succ y k

/-- The first `m` primes at least `y`. -/
noncomputable def firstPrimesFrom (y m : ℕ) : Finset ℕ :=
  (Finset.range m).image (py0 y)

theorem card_firstPrimesFrom (y m : ℕ) :
    (firstPrimesFrom y m).card = m := by
  unfold firstPrimesFrom
  rw [Finset.card_image_of_injective _ (StrictMono.injective (py0_strictMono y))]
  exact Finset.card_range m

theorem mem_firstPrimesFrom_iff
    {y m p : ℕ} :
    p ∈ firstPrimesFrom y m ↔ ∃ k < m, py0 y k = p := by
  classical
  constructor
  · intro hp
    unfold firstPrimesFrom at hp
    rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    unfold firstPrimesFrom
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩

theorem mem_firstPrimesFrom_prime {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    Nat.Prime p := by
  rcases (mem_firstPrimesFrom_iff).mp hp with ⟨k, hk, rfl⟩
  exact py0_prime y k

theorem mem_firstPrimesFrom_ge {y m p : ℕ}
    (hp : p ∈ firstPrimesFrom y m) :
    y ≤ p := by
  rcases (mem_firstPrimesFrom_iff).mp hp with ⟨k, hk, rfl⟩
  exact py0_ge y k

/-- The paper product `UB(S) = ∏_{p ∈ S} p/(p-1)`. -/
def UB (S : Finset ℕ) : ℚ :=
  S.prod pivotFactor

@[simp] theorem UB_empty :
    UB ∅ = 1 := rfl

@[simp] theorem UB_insert {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) :
    UB (insert p S) = pivotFactor p * UB S := by
  unfold UB
  rw [Finset.prod_insert hp]

@[simp] theorem UB_def (S : Finset ℕ) :
    UB S = S.prod pivotFactor := rfl

/--
Paper-facing worst-case envelope:
`UBm y m = ∏_{i=1}^m p_{y,i}/(p_{y,i}-1)`, with `UBm y 0 = 1`.
-/
noncomputable def UBm (y m : ℕ) : ℚ :=
  ∏ k ∈ Finset.range m, pivotFactor (py0 y k)

@[simp] theorem UBm_zero (y : ℕ) :
    UBm y 0 = 1 := rfl

@[simp] theorem UBm_succ (y m : ℕ) :
    UBm y (m + 1) = UBm y m * pivotFactor (py0 y m) := by
  unfold UBm
  rw [Finset.prod_range_succ]

theorem UBm_eq_prod_range (y m : ℕ) :
    UBm y m = ∏ k ∈ Finset.range m, pivotFactor (py0 y k) := rfl

theorem UBm_eq_UB_firstPrimesFrom (y m : ℕ) :
    UBm y m = UB (firstPrimesFrom y m) := by
  classical
  unfold UBm UB firstPrimesFrom
  rw [Finset.prod_image]
  intro a _ b _ hab
  exact StrictMono.injective (py0_strictMono y) hab

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
  have hp1 : 1 ≤ p := le_trans (by decide) hp
  have hden : (((p - 1 : ℕ) : ℚ)) ≠ 0 := by
    have hpnz : (p - 1 : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by decide) hp)
    exact_mod_cast hpnz
  rw [pivotFactor_def]
  have hrepr : (p : ℚ) = (((p - 1 : ℕ) : ℚ)) + 1 := by
    rw [Nat.cast_sub hp1]
    ring
  rw [hrepr, add_div, div_self hden]

theorem UBm_pos (y m : ℕ) :
    0 < UBm y m := by
  unfold UBm
  exact Finset.prod_pos (fun p _ => pivotFactor_pos_of_prime (py0_prime y p))

theorem UBm_nonneg (y m : ℕ) :
    0 ≤ UBm y m := by
  exact le_of_lt (UBm_pos y m)

theorem one_le_pivotFactor_of_prime {p : ℕ} (hp : Nat.Prime p) :
    1 ≤ pivotFactor p := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [pivotFactor_eq_one_add_inv hp2]
  have hden_pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by
    have hp1 : 1 ≤ p := le_trans (by decide) hp2
    rw [Nat.cast_sub hp1]
    exact sub_pos.mpr (by exact_mod_cast hp2)
  have hinv_nonneg : (0 : ℚ) ≤ 1 / (((p - 1 : ℕ) : ℚ)) := by
    exact div_nonneg (by norm_num) (le_of_lt hden_pos)
  linarith

theorem UBm_le_succ (y m : ℕ) :
    UBm y m ≤ UBm y (m + 1) := by
  rw [UBm_succ]
  have hfac : 1 ≤ pivotFactor (py0 y m) := one_le_pivotFactor_of_prime (py0_prime y m)
  have hnonneg : 0 ≤ UBm y m := UBm_nonneg y m
  have : UBm y m * 1 ≤ UBm y m * pivotFactor (py0 y m) := by
    exact mul_le_mul_of_nonneg_left hfac hnonneg
  simpa using this

theorem UBm_monotone (y : ℕ) :
    Monotone (UBm y) := by
  refine monotone_nat_of_le_succ ?_
  intro m
  exact UBm_le_succ y m

theorem UBm_le_of_le {y m n : ℕ} (hmn : m ≤ n) :
    UBm y m ≤ UBm y n := by
  exact UBm_monotone y hmn

theorem py0_monotone_in_y {y₁ y₂ k : ℕ} (hy : y₁ ≤ y₂) :
    py0 y₁ k ≤ py0 y₂ k := by
  induction k generalizing y₁ y₂ with
  | zero =>
      simpa [py0] using nextPrimeGe_le_of_prime_ge (nextPrimeGe_prime y₂) (le_trans hy (nextPrimeGe_ge y₂))
  | succ k ih =>
      have hstep : py0 y₁ k + 1 ≤ py0 y₂ k + 1 := Nat.succ_le_succ (ih hy)
      simpa [py0_succ] using
        nextPrimeGe_le_of_prime_ge (nextPrimeGe_prime (py0 y₂ k + 1))
          (le_trans hstep (nextPrimeGe_ge (py0 y₂ k + 1)))

theorem factor_antitone_on_two_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    pivotFactor b ≤ pivotFactor a := by
  have hb : 2 ≤ b := le_trans ha hab
  have hqa : (0 : ℚ) < (((a - 1 : ℕ) : ℚ)) := by
    have ha1 : 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha
    rw [Nat.cast_sub ha1]
    exact sub_pos.mpr (by exact_mod_cast ha)
  have hqb : (0 : ℚ) < (((b - 1 : ℕ) : ℚ)) := by
    have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
    rw [Nat.cast_sub hb1]
    exact sub_pos.mpr (by exact_mod_cast hb)
  have hsub : (((a - 1 : ℕ) : ℚ)) ≤ (((b - 1 : ℕ) : ℚ)) := by
    have ha1 : 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha
    have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
    rw [Nat.cast_sub ha1, Nat.cast_sub hb1]
    have habQ : (a : ℚ) ≤ (b : ℚ) := by
      exact_mod_cast hab
    linarith
  have hone : 1 / (((b - 1 : ℕ) : ℚ)) ≤ 1 / (((a - 1 : ℕ) : ℚ)) := by
    have h_mul_pos : 0 < (((a - 1 : ℕ) : ℚ)) * (((b - 1 : ℕ) : ℚ)) := mul_pos hqa hqb
    have h_diff : 0 ≤ (((b - 1 : ℕ) : ℚ)) - (((a - 1 : ℕ) : ℚ)) := sub_nonneg.mpr hsub
    have h_div :
        0 ≤ ((((b - 1 : ℕ) : ℚ)) - (((a - 1 : ℕ) : ℚ))) /
              ((((a - 1 : ℕ) : ℚ)) * (((b - 1 : ℕ) : ℚ))) := by
      exact div_nonneg h_diff (le_of_lt h_mul_pos)
    have h_eq :
        ((((b - 1 : ℕ) : ℚ)) - (((a - 1 : ℕ) : ℚ))) /
            ((((a - 1 : ℕ) : ℚ)) * (((b - 1 : ℕ) : ℚ))) =
          1 / (((a - 1 : ℕ) : ℚ)) - 1 / (((b - 1 : ℕ) : ℚ)) := by
      have hane : (((a - 1 : ℕ) : ℚ)) ≠ 0 := ne_of_gt hqa
      have hbne : (((b - 1 : ℕ) : ℚ)) ≠ 0 := ne_of_gt hqb
      field_simp [hane, hbne]
    have h_diff2 : 0 ≤ 1 / (((a - 1 : ℕ) : ℚ)) - 1 / (((b - 1 : ℕ) : ℚ)) := by
      rw [← h_eq]
      exact h_div
    exact sub_nonneg.mp h_diff2
  rw [pivotFactor_eq_one_add_inv hb, pivotFactor_eq_one_add_inv ha]
  linarith

theorem UBm_antitone_in_y {y₁ y₂ m : ℕ} (hy : y₁ ≤ y₂) :
    UBm y₂ m ≤ UBm y₁ m := by
  unfold UBm
  exact Finset.prod_le_prod
    (fun k _ => pivotFactor_nonneg_of_prime (py0_prime y₂ k))
    (fun k _ => factor_antitone_on_two_le (py0_prime y₁ k).two_le (py0_monotone_in_y hy))

theorem prod_pivotFactor_pos_of_all_prime {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    0 < S.prod pivotFactor := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have ha_prime : Nat.Prime a := hprime a (by simp)
      have hs_prime : ∀ p ∈ s, Nat.Prime p := by
        intro p hp
        exact hprime p (by simp [hp])
      rw [Finset.prod_insert ha]
      exact mul_pos (pivotFactor_pos_of_prime ha_prime) (ih hs_prime)

theorem py0_shift (y k : ℕ) :
    py0 y (k + 1) = py0 (py0 y 0 + 1) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change nextPrimeGe (py0 y (k + 1) + 1) = nextPrimeGe (py0 (py0 y 0 + 1) k + 1)
      rw [ih]

theorem UBm_succ_first (y m : ℕ) :
    UBm y (m + 1) = pivotFactor (py0 y 0) * UBm (py0 y 0 + 1) m := by
  unfold UBm
  rw [Finset.prod_range_succ', mul_comm]
  apply congrArg (fun x => pivotFactor (py0 y 0) * x)
  apply Finset.prod_congr rfl
  intro k _
  rw [py0_shift]

private theorem worst_case_monotone_envelope_prod :
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
    have h_not_in_T : a ∉ T := by
      intro h
      exact (Finset.mem_erase.mp h).1 rfl
    have hT_ss : T ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.erase_subset a S, ?_⟩
      intro hEq
      have h_in_T : a ∈ T := by
        rw [hEq]
        exact ha_mem
      exact h_not_in_T h_in_T
    have hT_prime : ∀ p ∈ T, Nat.Prime p := fun p hp => hprime p (Finset.mem_erase.mp hp).2
    have hT_ge : ∀ p ∈ T, a + 1 ≤ p := by
      intro p hp
      have hpS : p ∈ S := (Finset.mem_erase.mp hp).2
      have hmin : a ≤ p := Finset.min'_le S p hpS
      have hne : a ≠ p := Ne.symm (Finset.mem_erase.mp hp).1
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hmin hne)
    have htail : T.prod pivotFactor ≤ UBm (a + 1) T.card := ih T hT_ss (a + 1) hT_prime hT_ge
    have hhead : pivotFactor a ≤ pivotFactor (py0 y 0) := by
      have hnext_le_a : py0 y 0 ≤ a := nextPrimeGe_le_of_prime_ge ha_prime hy_a
      exact factor_antitone_on_two_le (nextPrimeGe_prime y).two_le hnext_le_a
    have hprod_nonneg : 0 ≤ T.prod pivotFactor := le_of_lt (prod_pivotFactor_pos_of_all_prime hT_prime)
    have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha_mem
    calc
      S.prod pivotFactor = pivotFactor a * T.prod pivotFactor := by
        have : insert a T = S := Finset.insert_erase ha_mem
        nth_rw 1 [← this]
        exact Finset.prod_insert h_not_in_T
      _ ≤ pivotFactor (py0 y 0) * UBm (a + 1) T.card := by
        exact mul_le_mul hhead htail hprod_nonneg (pivotFactor_nonneg_of_prime (py0_prime y 0))
      _ ≤ pivotFactor (py0 y 0) * UBm (py0 y 0 + 1) T.card := by
        have hnext_le_a : py0 y 0 ≤ a := nextPrimeGe_le_of_prime_ge ha_prime hy_a
        have htail' : UBm (a + 1) T.card ≤ UBm (py0 y 0 + 1) T.card :=
          UBm_antitone_in_y (Nat.succ_le_succ hnext_le_a)
        exact mul_le_mul_of_nonneg_left htail' (pivotFactor_nonneg_of_prime (py0_prime y 0))
      _ = UBm y (T.card + 1) := (UBm_succ_first y T.card).symm
      _ = UBm y S.card := by rw [hcard]
  · have hSE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst hSE
    simp

/--
Worst-case monotone envelope:
among finite sets of `m` primes all at least `y`, `UB(S)` is bounded by `UBm y m`.
-/
theorem worst_case_monotone_envelope :
    ∀ S : Finset ℕ, ∀ y : ℕ,
      (∀ p ∈ S, Nat.Prime p) →
      (∀ p ∈ S, y ≤ p) →
      UB S ≤ UBm y S.card := by
  intro S y hprime hge
  simpa [UB] using worst_case_monotone_envelope_prod S y hprime hge

/--
Support-level worst-case envelope for a `y`-rough integer.
-/
theorem UB_primeSupport_le_UBm_of_yrough {y n : ℕ} (hy : YRough y n) :
    UB (primeSupport n) ≤ UBm y (primeSupport n).card := by
  apply worst_case_monotone_envelope
  · intro p hp
    exact prime_of_mem_primeSupport hp
  · intro p hp
    exact hy p (prime_of_mem_primeSupport hp) (dvd_of_mem_primeSupport hp)

/--
Legacy rational-product form used downstream.
-/
theorem prod_primeSupport_le_UBm_of_yrough {y n : ℕ} (hy : YRough y n) :
    (primeSupport n).prod pivotFactor ≤ UBm y (primeSupport n).card := by
  have h_eq : UB (primeSupport n) = (primeSupport n).prod pivotFactor := rfl
  rw [← h_eq]
  exact UB_primeSupport_le_UBm_of_yrough hy

end Pivot
end Lehmer