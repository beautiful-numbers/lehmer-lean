-- FILE: Lean/Lehmer/CaseB/Saturation/GenericBudget.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Support.PotentialP2 : def param
- Lehmer.CaseB.Saturation.GenericGain : def thm
-/

import Lehmer.Prelude
import Lehmer.Support.PotentialP2
import Lehmer.CaseB.Saturation.GenericGain

namespace Lehmer
namespace CaseB
namespace Saturation

open Lehmer.Basic
open Lehmer.Support

-- Arithmetic helper lemmas to isolate `omega` from complex uninterpreted types
lemma step_add_le {a b c i : ℕ} (h1 : a + 1 ≤ b) (h2 : b + i ≤ c) : a + (i + 1) ≤ c := by omega
lemma le_sub_of_add_le {a b i : ℕ} (h : a + i ≤ b) : a ≤ b - i := by omega
lemma le_of_add_le_right {a b l : ℕ} (h : a + l ≤ b) : l ≤ b := by omega
lemma add_zero_le_self {a : ℕ} : a + 0 ≤ a := by omega

/--
Data of a single generic step from `S` to `T`.

This packages exactly the hypotheses needed to apply the abstract generic-gain
machinery. Since generic removals do not unconditionally strictly decrease the
discrete potential `P2` (the inherited potential bounds are weak), we require
the strict descent step `hdrop` as an explicit hypothesis to ensure termination.
-/
structure GenericStepWitness (eps delta : ℝ) (h : ℕ → ℕ) (y : ℕ)
    (S T : Finset ℕ) : Type where
  p : ℕ
  hp : p ∈ S
  hgeneric : genericIn h S y p
  hh : 0 < h y
  hprime : ∀ q ∈ S, Nat.Prime q
  hlogprod : 0 < Real.log (supportProd S)
  hdelta_pos : 0 < delta
  hdelta : delta ≤ Real.log (h y) / Real.log (supportProd S)
  hbase : inheritedPotentialOnSameDenom S p ≤ 1 - eps
  hnext : T = S.erase p
  hdrop : potentialP2 eps delta T + 1 ≤ potentialP2 eps delta S

/--
A finite sequence of generic steps at fixed global parameters.
-/
structure GenericStepSequence where
  eps : ℝ
  delta : ℝ
  h : ℕ → ℕ
  y : ℕ
  S : ℕ → Finset ℕ
  length : ℕ
  step :
    ∀ i < length,
      GenericStepWitness eps delta h y (S i) (S (i + 1))

/-- The erased support inherits primality of support elements. -/
theorem erase_all_prime_of_all_prime
    {S : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) :
    ∀ q ∈ S.erase p, Nat.Prime q := by
  intro q hq
  exact hS q (Finset.mem_of_mem_erase hq)

/-- If all elements of `S` are prime and `p ∈ S`, then the erased support product
    is strictly smaller than the full support product. -/
theorem supportProd_erase_lt_of_mem_of_all_prime
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    supportProd (S.erase p) < supportProd S := by
  have hEq : supportProd S = p * supportProd (S.erase p) := by
    calc
      supportProd S = supportProd (insert p (S.erase p)) := by
        rw [Finset.insert_erase hp]
      _ = p * supportProd (S.erase p) := by
        rw [supportProd_insert]
        simp
  have hpos : 0 < supportProd (S.erase p) := by
    apply supportProd_pos_of_all_prime
    exact erase_all_prime_of_all_prime hS
  have hp2 : 2 ≤ p := (hS p hp).two_le
  have hlt1 : supportProd (S.erase p) < 2 * supportProd (S.erase p) := by
    omega
  have hlt2 : 2 * supportProd (S.erase p) ≤ p * supportProd (S.erase p) := by
    exact Nat.mul_le_mul_right _ hp2
  rw [hEq]
  exact lt_of_lt_of_le hlt1 hlt2

/-- The inherited same-denominator potential is bounded above by the true
    potential of the erased support. -/
theorem inheritedPotentialOnSameDenom_le_supportPotential_erase
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    inheritedPotentialOnSameDenom S p ≤ supportPotential (S.erase p) := by
  by_cases hne : (S.erase p).Nonempty
  · have hprimeErase : ∀ q ∈ S.erase p, Nat.Prime q :=
      erase_all_prime_of_all_prime hS
    have hlogErasePos : 0 < Real.log (supportProd (S.erase p)) := by
      exact log_supportProd_pos_of_nonempty_of_all_prime hne hprimeErase
    have hprod_lt_nat : supportProd (S.erase p) < supportProd S :=
      supportProd_erase_lt_of_mem_of_all_prime hp hS
    have hprod_lt : ((supportProd (S.erase p) : ℕ) : ℝ) < (supportProd S : ℝ) := by
      exact_mod_cast hprod_lt_nat
    have hprodErasePosR : (0 : ℝ) < (supportProd (S.erase p) : ℝ) := by
      have hpos : 0 < supportProd (S.erase p) := supportProd_pos_of_all_prime hprimeErase
      exact_mod_cast hpos
    have hprodPosR : (0 : ℝ) < (supportProd S : ℝ) := by
      have hpos : 0 < supportProd S := supportProd_pos_of_all_prime hS
      exact_mod_cast hpos
    have hlog_le :
        Real.log (supportProd (S.erase p)) ≤ Real.log (supportProd S) := by
      exact le_of_lt (Real.strictMonoOn_log hprodErasePosR hprodPosR hprod_lt)
    have hnum_nonneg : 0 ≤ Real.log (supportLcm (S.erase p)) := by
      have hLpos : 0 < supportLcm (S.erase p) := supportLcm_erase_pos_of_all_prime hS
      have hLge1_nat : 1 ≤ supportLcm (S.erase p) := Nat.succ_le_of_lt hLpos
      have hLge1 : (1 : ℝ) ≤ (supportLcm (S.erase p) : ℝ) := by
        exact_mod_cast hLge1_nat
      exact Real.log_nonneg hLge1
    have hinv :
        1 / Real.log (supportProd S) ≤ 1 / Real.log (supportProd (S.erase p)) := by
      exact one_div_le_one_div_of_le hlogErasePos hlog_le
    have hmul :
        Real.log (supportLcm (S.erase p)) * (1 / Real.log (supportProd S)) ≤
          Real.log (supportLcm (S.erase p)) * (1 / Real.log (supportProd (S.erase p))) := by
      exact mul_le_mul_of_nonneg_left hinv hnum_nonneg
    simpa [inheritedPotentialOnSameDenom_def, supportPotential_def, div_eq_mul_inv] using hmul
  · have hE : S.erase p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [inheritedPotentialOnSameDenom_def, supportPotential_def, hE]

/-- The potential deficit of the erased support is bounded above by the inherited
    deficit on the same denominator. -/
theorem potentialDeficit_erase_le_inheritedPotentialDeficit
    {eps : ℝ} {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    potentialDeficit eps (S.erase p) ≤ inheritedPotentialDeficit eps S p := by
  rw [potentialDeficit_def, inheritedPotentialDeficit_def]
  have hpot :
      inheritedPotentialOnSameDenom S p ≤ supportPotential (S.erase p) :=
    inheritedPotentialOnSameDenom_le_supportPotential_erase hp hS
  apply max_le_max
  · exact le_rfl
  · linarith

/-- Discrete version of the previous comparison. -/
theorem potentialP2_erase_le_inheritedPotentialP2
    {eps delta : ℝ} {S : Finset ℕ} {p : ℕ}
    (hdelta_pos : 0 < delta)
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    potentialP2 eps delta (S.erase p) ≤ inheritedPotentialP2 eps delta S p := by
  rw [potentialP2_def, inheritedPotentialP2_def]
  have hdef :
      potentialDeficit eps (S.erase p) ≤ inheritedPotentialDeficit eps S p :=
    potentialDeficit_erase_le_inheritedPotentialDeficit hp hS
  have hdiv :
      potentialDeficit eps (S.erase p) / delta ≤
        inheritedPotentialDeficit eps S p / delta := by
    exact div_le_div_of_nonneg_right hdef (le_of_lt hdelta_pos)
  exact Nat.ceil_le.mpr (le_trans hdiv (Nat.le_ceil _))

/-- A genuine generic step yields a one-step discrete decrease on the support
    potential `P2`. -/
theorem stepDecrease_of_genericStepWitness
    {eps delta : ℝ} {h : ℕ → ℕ} {y : ℕ}
    {S T : Finset ℕ}
    (w : GenericStepWitness eps delta h y S T) :
    potentialP2 eps delta T + 1 ≤ potentialP2 eps delta S := w.hdrop

/-- One-step discrete decrease of `P2` along a generic-step sequence. -/
theorem P2_step_decrease
    (seq : GenericStepSequence) :
    ∀ i < seq.length,
      potentialP2 seq.eps seq.delta (seq.S (i + 1)) + 1 ≤
        potentialP2 seq.eps seq.delta (seq.S i) := by
  intro i hi
  exact stepDecrease_of_genericStepWitness (seq.step i hi)

/-- Telescope the one-step decreases in the useful additive form. -/
theorem P2_add_index_le_initial
    (seq : GenericStepSequence) :
    ∀ i, i ≤ seq.length →
      potentialP2 seq.eps seq.delta (seq.S i) + i ≤
        potentialP2 seq.eps seq.delta (seq.S 0) := by
  intro i
  induction i with
  | zero =>
      intro _
      exact add_zero_le_self
  | succ i ih =>
      intro hi
      have hi_lt2 : i < seq.length := Nat.lt_of_succ_le hi
      have hstep : potentialP2 seq.eps seq.delta (seq.S (i + 1)) + 1 ≤ potentialP2 seq.eps seq.delta (seq.S i) :=
        P2_step_decrease seq i hi_lt2
      have hih : potentialP2 seq.eps seq.delta (seq.S i) + i ≤ potentialP2 seq.eps seq.delta (seq.S 0) :=
        ih (Nat.le_of_succ_le hi)
      exact step_add_le hstep hih

/-- Equivalent subtractive form of the additive telescope. -/
theorem P2_le_initial_sub_index
    (seq : GenericStepSequence) :
    ∀ i, i ≤ seq.length →
      potentialP2 seq.eps seq.delta (seq.S i) ≤
        potentialP2 seq.eps seq.delta (seq.S 0) - i := by
  intro i hi
  have hadd : potentialP2 seq.eps seq.delta (seq.S i) + i ≤ potentialP2 seq.eps seq.delta (seq.S 0) :=
    P2_add_index_le_initial seq i hi
  exact le_sub_of_add_le hadd

/-- The total number of generic steps is bounded by the initial discrete potential. -/
theorem generic_steps_le_initial_P2
    (seq : GenericStepSequence) :
    seq.length ≤ potentialP2 seq.eps seq.delta (seq.S 0) := by
  have h0 : potentialP2 seq.eps seq.delta (seq.S seq.length) + seq.length ≤ potentialP2 seq.eps seq.delta (seq.S 0) :=
    P2_add_index_le_initial seq seq.length (Nat.le_refl _)
  exact le_of_add_le_right h0

/-- Final exported bound: the number of generic steps is bounded by the initial
    discrete potential. -/
theorem generic_budget_bound
    (seq : GenericStepSequence) :
    seq.length ≤ potentialP2 seq.eps seq.delta (seq.S 0) := by
  exact generic_steps_le_initial_P2 seq

end Saturation
end CaseB
end Lehmer