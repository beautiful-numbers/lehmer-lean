-- FILE: Lean/Lehmer/Basic/OddSquarefree.lean
import Mathlib
import Lehmer.Basic.Defs
import Lehmer.Basic.LehmerBasic

namespace Lehmer
namespace Basic

/--
A Lehmer composite is not prime.
This is just the first projection of the definition.
-/
theorem LehmerComposite.not_prime {n : ℕ} (h : LehmerComposite n) : ¬ Nat.Prime n := by
  exact h.1

/--
A Lehmer composite is at least `2`.
-/
theorem LehmerComposite.two_le {n : ℕ} (h : LehmerComposite n) : 2 ≤ n := by
  exact h.2.1

/--
A Lehmer composite is positive.
-/
theorem LehmerComposite.pos {n : ℕ} (h : LehmerComposite n) : 0 < n := by
  exact lt_of_lt_of_le (by decide : 0 < 2) h.two_le

/--
A Lehmer composite is nonzero.
-/
theorem LehmerComposite.ne_zero {n : ℕ} (h : LehmerComposite n) : n ≠ 0 := by
  exact Nat.ne_of_gt h.pos

/--
A Lehmer composite is greater than `1`.
-/
theorem LehmerComposite.one_lt {n : ℕ} (h : LehmerComposite n) : 1 < n := by
  exact lt_of_lt_of_le (by decide : 1 < 2) h.two_le

/--
A Lehmer composite is not equal to `1`.
-/
theorem LehmerComposite.ne_one {n : ℕ} (h : LehmerComposite n) : n ≠ 1 := by
  exact Nat.ne_of_gt h.one_lt

/--
A Lehmer composite satisfies the Lehmer divisibility condition.
-/
theorem LehmerComposite.totient_dvd_pred {n : ℕ} (h : LehmerComposite n) :
    Nat.totient n ∣ (n - 1) := by
  exact h.2.2

/--
A Lehmer composite is odd.

This is a standard structural fact in Lehmer's problem.
The proof uses that `φ(n)` is even for `n > 2`, while `φ(n) ∣ (n-1)`.
-/
theorem LehmerComposite.odd {n : ℕ} (h : LehmerComposite n) : Odd n := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · exfalso
    have hnot2 : n ≠ 2 := by
      intro hn2
      apply h.not_prime
      simpa [hn2] using Nat.prime_two
    have hn_gt2 : 2 < n := lt_of_le_of_ne h.two_le hnot2.symm
    have hphiEven : Even (Nat.totient n) := Nat.totient_even hn_gt2
    rcases hphiEven with ⟨k, hk⟩
    rcases h.totient_dvd_pred with ⟨m, hm⟩
    have hEvenPred : Even (n - 1) := by
      refine ⟨k * m, ?_⟩
      rw [hm, hk]
      ring
    rcases hEven with ⟨a, ha⟩
    rcases hEvenPred with ⟨b, hb⟩
    omega
  · exact hOdd

/--
A Lehmer composite is squarefree.

If `p^2 ∣ n` for a prime `p`, then `φ(p^2) ∣ φ(n)`, hence `p ∣ φ(n)`.
Since `φ(n) ∣ (n-1)`, this gives `p ∣ (n-1)`, while already `p ∣ n`,
which is impossible.
-/
theorem LehmerComposite.squarefree {n : ℕ} (h : LehmerComposite n) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpp_tot : Nat.totient (p * p) ∣ Nat.totient n := by
    exact Nat.totient_dvd_of_dvd hpp
  have hp_dvd_phi_pp : p ∣ Nat.totient (p * p) := by
    rw [Nat.totient_mul_of_prime_of_dvd hp (dvd_rfl : p ∣ p)]
    refine ⟨Nat.totient p, ?_⟩
    ring
  have hp_dvd_phi_n : p ∣ Nat.totient n := by
    exact dvd_trans hp_dvd_phi_pp hpp_tot
  have hp_dvd_pred : p ∣ n - 1 := by
    exact dvd_trans hp_dvd_phi_n h.totient_dvd_pred
  have hpn : p ∣ n := by
    exact dvd_trans (dvd_mul_right p p) hpp
  have hp_dvd_one : p ∣ n - (n - 1) := by
    exact Nat.dvd_sub hpn hp_dvd_pred
  have hs : n = 1 + (n - 1) := by
    calc
      n = (n - 1) + 1 := by
        exact (Nat.succ_pred_eq_of_pos h.pos).symm
      _ = 1 + (n - 1) := by
        rw [Nat.add_comm]
  have hsub : n - (n - 1) = 1 := by
    exact Nat.sub_eq_of_eq_add hs
  have : p ∣ 1 := by
    simpa [hsub] using hp_dvd_one
  exact hp.not_dvd_one this

/--
Main structural lemma: a Lehmer composite is odd and squarefree.
-/
theorem LehmerComposite.odd_and_squarefree {n : ℕ} (h : LehmerComposite n) :
    Odd n ∧ Squarefree n := by
  exact ⟨h.odd, h.squarefree⟩

end Basic
end Lehmer