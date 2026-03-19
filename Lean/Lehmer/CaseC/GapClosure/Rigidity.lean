-- FILE: Lean/Lehmer/CaseC/GapClosure/Rigidity.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.Totient : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.Totient

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def rigidityGap (n : ℕ) : ℚ :=
  totientIndex n - lehmerQuotient n

@[simp] theorem rigidityGap_def (n : ℕ) :
    rigidityGap n = totientIndex n - lehmerQuotient n := rfl

theorem rigidityGap_eq_inv_totientQ (n : ℕ) :
    rigidityGap n = 1 / totientQ n := by
  simpa [rigidityGap] using totientIndex_sub_lehmerQuotient n

theorem totientIndex_eq_lehmerQuotient_add_rigidityGap (n : ℕ) :
    totientIndex n = lehmerQuotient n + rigidityGap n := by
  calc
    totientIndex n = lehmerQuotient n + (1 / totientQ n) := by
      exact totientIndex_eq_lehmerQuotient_add_inv n
    _ = lehmerQuotient n + rigidityGap n := by
      rw [rigidityGap_eq_inv_totientQ]

theorem rigidityGap_eq_inv_totientQ_of_LehmerComposite {n : ℕ}
    (_h : LehmerComposite n) :
    rigidityGap n = 1 / totientQ n := by
  exact rigidityGap_eq_inv_totientQ n

theorem exists_integer_center_of_totient_dvd (n : ℕ)
    (h : Nat.totient n ∣ (n - 1)) :
    ∃ k : ℕ, totientIndex n = k + rigidityGap n := by
  rcases lehmerQuotient_exists_int_of_totient_dvd n h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    totientIndex n = lehmerQuotient n + rigidityGap n := by
      exact totientIndex_eq_lehmerQuotient_add_rigidityGap n
    _ = k + rigidityGap n := by
      rw [hk]

theorem exists_integer_center_of_LehmerComposite {n : ℕ}
    (h : LehmerComposite n) :
    ∃ k : ℕ, totientIndex n = k + rigidityGap n := by
  exact exists_integer_center_of_totient_dvd n h.2.2

theorem rigidity_distance_placeholder {n : ℕ}
    (h : LehmerComposite n) :
    ∃ k : ℕ, |totientIndex n - k| = rigidityGap n := by
  rcases exists_integer_center_of_LehmerComposite h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) h.2.1
  have hphi_pos : 0 < Nat.totient n := by
    exact (Nat.totient_pos).2 hnpos
  have hgap_nonneg : 0 ≤ rigidityGap n := by
    rw [rigidityGap_eq_inv_totientQ]
    have htotQ_pos : 0 < totientQ n := by
      dsimp [totientQ]
      exact_mod_cast hphi_pos
    positivity
  calc
    |totientIndex n - k| = |rigidityGap n| := by
      rw [hk]
      ring_nf
    _ = rigidityGap n := abs_of_nonneg hgap_nonneg

end GapClosure
end CaseC
end Lehmer