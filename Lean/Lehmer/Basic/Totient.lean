-- FILE: Lean/Lehmer/Basic/Totient.lean
import Mathlib
import Lehmer.Basic.Defs

namespace Lehmer
namespace Basic

/-- `φ(n)` as a rational number. -/
def totientQ (n : ℕ) : ℚ :=
  (Nat.totient n : ℚ)

@[simp] theorem totientQ_def (n : ℕ) : totientQ n = (Nat.totient n : ℚ) := rfl

@[simp] theorem totientIndex_def (n : ℕ) :
    totientIndex n = (n : ℚ) / (Nat.totient n : ℚ) := rfl

@[simp] theorem lehmerQuotient_def (n : ℕ) :
    lehmerQuotient n = ((n - 1 : ℕ) : ℚ) / (Nat.totient n : ℚ) := rfl

/-- Rewriting `I(n)` through `φ(n)` in the auxiliary notation `totientQ`. -/
@[simp] theorem totientIndex_eq (n : ℕ) :
    totientIndex n = (n : ℚ) / totientQ n := rfl

/-- Rewriting `K(n)` through `φ(n)` in the auxiliary notation `totientQ`. -/
@[simp] theorem lehmerQuotient_eq (n : ℕ) :
    lehmerQuotient n = ((n - 1 : ℕ) : ℚ) / totientQ n := rfl

/-- The basic rigidity identity `I(n) - K(n) = 1 / φ(n)` in `ℚ`. -/
theorem totientIndex_sub_lehmerQuotient (n : ℕ) :
    totientIndex n - lehmerQuotient n = 1 / totientQ n := by
  by_cases hφ : Nat.totient n = 0
  · simp [totientIndex, lehmerQuotient, totientQ, hφ]
  · have hφQ : (Nat.totient n : ℚ) ≠ 0 := by
      exact_mod_cast hφ
    have hn : n ≠ 0 := by
      intro hn0
      subst hn0
      simp at hφ
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hsub : (((n - 1 : ℕ) : ℚ)) = (n : ℚ) - 1 := by
      norm_num [Nat.cast_sub hn1]
    rw [totientIndex, lehmerQuotient, totientQ]
    rw [hsub]
    field_simp [hφQ]
    ring

/-- Equivalent additive form of the rigidity identity. -/
theorem totientIndex_eq_lehmerQuotient_add_inv (n : ℕ) :
    totientIndex n = lehmerQuotient n + 1 / totientQ n := by
  linarith [totientIndex_sub_lehmerQuotient n]

/-- If `φ(n) ∣ n-1`, then `K(n)` is an integer-valued rational. -/
theorem lehmerQuotient_exists_int_of_totient_dvd (n : ℕ)
    (h : Nat.totient n ∣ (n - 1)) :
    ∃ k : ℕ, lehmerQuotient n = k := by
  rcases h with ⟨k, hk⟩
  by_cases hφ : Nat.totient n = 0
  · refine ⟨0, ?_⟩
    simp [lehmerQuotient, hφ]
  · refine ⟨k, ?_⟩
    have hφQ : (Nat.totient n : ℚ) ≠ 0 := by
      exact_mod_cast hφ
    have hkQ : (((n - 1 : ℕ) : ℚ)) = (Nat.totient n : ℚ) * (k : ℚ) := by
      exact_mod_cast hk
    apply (div_eq_iff hφQ).2
    simpa [lehmerQuotient, mul_comm, mul_left_comm, mul_assoc] using hkQ

/-- For a Lehmer composite, `K(n)` is an integer-valued rational. -/
theorem lehmerQuotient_exists_int_of_LehmerComposite (n : ℕ)
    (h : LehmerComposite n) :
    ∃ k : ℕ, lehmerQuotient n = k := by
  exact lehmerQuotient_exists_int_of_totient_dvd n h.2.2

end Basic
end Lehmer