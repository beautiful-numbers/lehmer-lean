-- FILE: Lean/Lehmer/Basic/Totient.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.PrimeSupport : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.PrimeSupport

namespace Lehmer
namespace Basic

/-- `φ(n)` viewed in `ℚ`. -/
def totientQ (n : ℕ) : ℚ :=
  (Nat.totient n : ℚ)

@[simp] theorem totientQ_def (n : ℕ) :
    totientQ n = (Nat.totient n : ℚ) := rfl

@[simp] theorem totientIndex_def (n : ℕ) :
    totientIndex n = (n : ℚ) / totientQ n := rfl

@[simp] theorem lehmerQuotient_def (n : ℕ) :
    lehmerQuotient n = ((n - 1 : ℕ) : ℚ) / totientQ n := rfl

/-- Positivity of `φ(n)` in `ℚ` for positive `n`. -/
theorem totientQ_pos_of_pos {n : ℕ} (hn : 0 < n) :
    (0 : ℚ) < totientQ n := by
  have hφ : 0 < Nat.totient n := (Nat.totient_pos).2 hn
  exact_mod_cast hφ

/-- Non-vanishing of `φ(n)` in `ℚ` for positive `n`. -/
theorem totientQ_ne_zero_of_pos {n : ℕ} (hn : 0 < n) :
    totientQ n ≠ 0 := by
  exact ne_of_gt (totientQ_pos_of_pos hn)

/--
Squarefree totient product formula:
`φ(n) = ∏_{p ∈ Supp(n)} (p - 1)`.
-/
theorem totient_eq_prod_sub_one_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    Nat.totient n = (primeSupport n).prod (fun p => p - 1) := by
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    simp at hsq

  rw [primeSupport_eq_primeFactors_of_squarefree hsq]
  rw [Nat.totient_eq_prod_factorization]
  · rfl
  · exact hsq
  · exact hn0

/--
Rational-cast version of the squarefree totient product formula.
-/
theorem totientQ_eq_prod_sub_one_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    totientQ n = ((primeSupport n).prod (fun p => p - 1) : ℚ) := by
  rw [totientQ_def, totient_eq_prod_sub_one_of_squarefree hsq]

/--
For squarefree `n`, the numerator itself is the product of its prime support.
-/
theorem nat_eq_prod_primeSupport_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    n = (primeSupport n).prod (fun p => p) := by
  rw [primeSupport_eq_primeFactors_of_squarefree hsq]
  exact (Nat.prod_primeFactors_of_squarefree hsq).symm

/--
Rational-cast version of the squarefree support product for `n`.
-/
theorem rat_cast_eq_prod_primeSupport_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    (n : ℚ) = (primeSupport n).prod (fun p => (p : ℚ)) := by
  rw [nat_eq_prod_primeSupport_of_squarefree hsq]
  norm_num

/--
If every factor in a finite product is nonzero, then the product is nonzero.
-/
theorem prod_ne_zero_of_forall_ne_zero {s : Finset ℕ} {f : ℕ → ℚ}
    (h : ∀ x ∈ s, f x ≠ 0) :
    s.prod f ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro x hx
  exact h x hx

/--
Finite-product division identity:
`(∏ f) / (∏ g) = ∏ (f/g)` provided all `g`-factors are nonzero.
-/
theorem prod_div_prod_eq_prod_div {s : Finset ℕ} {f g : ℕ → ℚ}
    (h : ∀ x ∈ s, g x ≠ 0) :
    (s.prod f) / (s.prod g) = s.prod (fun x => f x / g x) := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    have ha0 : g a ≠ 0 := h a (by simp)
    have hs0 : ∀ x ∈ s, g x ≠ 0 := by
      intro x hx
      exact h x (by simp [hx])
    have hsg : s.prod g ≠ 0 := prod_ne_zero_of_forall_ne_zero hs0
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have hmul :
        (f a * s.prod f) / (g a * s.prod g) =
          (f a / g a) * (s.prod f / s.prod g) := by
      field_simp [ha0, hsg]
      ring
    rw [hmul, ih hs0]
    ring

/--
Support-level product formula for the totient index:
`I(n) = ∏_{p ∈ Supp(n)} p / (p - 1)` for squarefree `n`.
-/
theorem totientIndex_eq_prod_primeSupport_of_squarefree {n : ℕ}
    (hsq : Squarefree n) :
    totientIndex n =
      (primeSupport n).prod (fun p => ((p : ℚ) / ((p - 1 : ℕ) : ℚ))) := by
  rw [totientIndex_def]
  rw [rat_cast_eq_prod_primeSupport_of_squarefree hsq]
  rw [totientQ_eq_prod_sub_one_of_squarefree hsq]

  have hden :
      ∀ p ∈ primeSupport n, (((p - 1 : ℕ) : ℚ)) ≠ 0 := by
    intro p hp
    have hp2 : 2 ≤ p := two_le_of_mem_primeSupport hp
    have hp1 : 1 < p := lt_of_lt_of_le (by decide : 1 < 2) hp2
    have hpnz : (p - 1 : ℕ) ≠ 0 := by
      exact Nat.sub_ne_zero_of_lt hp1
    exact_mod_cast hpnz

  simpa using
    (prod_div_prod_eq_prod_div
      (s := primeSupport n)
      (f := fun p => (p : ℚ))
      (g := fun p => (((p - 1 : ℕ) : ℚ)))
      hden)

/--
Basic rigidity identity:
`I(n) - K(n) = 1 / φ(n)` in `ℚ`.
-/
theorem totientIndex_sub_lehmerQuotient (n : ℕ) :
    totientIndex n - lehmerQuotient n = 1 / totientQ n := by
  by_cases hn : n = 0
  · subst hn
    simp [totientIndex, lehmerQuotient, totientQ]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hφ0 : totientQ n ≠ 0 := totientQ_ne_zero_of_pos hnpos
    have hsub : (((n - 1 : ℕ) : ℚ)) = (n : ℚ) - 1 := by
      have hn1 : 1 ≤ n := Nat.succ_le_of_lt hnpos
      norm_num [Nat.cast_sub hn1]
    rw [totientIndex_def, lehmerQuotient_def, hsub]
    field_simp [hφ0]
    ring

/--
Additive form of the rigidity identity.
-/
theorem totientIndex_eq_lehmerQuotient_add_inv (n : ℕ) :
    totientIndex n = lehmerQuotient n + 1 / totientQ n := by
  linarith [totientIndex_sub_lehmerQuotient n]

/--
If `φ(n) ∣ n - 1`, then `K(n)` is an integer-valued rational.
-/
theorem lehmerQuotient_exists_nat_of_totient_dvd (n : ℕ)
    (h : Nat.totient n ∣ (n - 1)) :
    ∃ k : ℕ, lehmerQuotient n = k := by
  rcases h with ⟨k, hk⟩
  by_cases hφ : Nat.totient n = 0
  · refine ⟨0, ?_⟩
    simp [lehmerQuotient, totientQ, hφ]
  · refine ⟨k, ?_⟩
    have hφQ : totientQ n ≠ 0 := by
      rw [totientQ_def]
      exact_mod_cast hφ
    apply (div_eq_iff hφQ).2
    rw [lehmerQuotient_def, totientQ_def]
    exact_mod_cast hk

/--
For a Lehmer composite, `K(n)` is an integer-valued rational.
-/
theorem lehmerQuotient_exists_nat_of_LehmerComposite {n : ℕ}
    (h : LehmerComposite n) :
    ∃ k : ℕ, lehmerQuotient n = k := by
  exact lehmerQuotient_exists_nat_of_totient_dvd n h.2.2

end Basic
end Lehmer