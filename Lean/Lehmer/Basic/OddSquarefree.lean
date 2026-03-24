-- FILE: Lean/Lehmer/Basic/OddSquarefree.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs

namespace Lehmer
namespace Basic

/--
A Lehmer composite is not prime.
This is the first field of the structure.
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

Reason:
- if `n` were even, then `n ≠ 2` because a Lehmer composite is not prime,
- hence `2 < n`, so `Nat.totient n` is even,
- since `φ(n) ∣ (n-1)`, the integer `n-1` is even,
- but an even integer minus `1` is odd, contradiction.
-/
theorem LehmerComposite.odd {n : ℕ} (h : LehmerComposite n) : Odd n := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · exfalso
    have hn_ne_two : n ≠ 2 := by
      intro hn2
      apply h.not_prime
      simpa [hn2] using Nat.prime_two

    have hn_gt_two : 2 < n := by
      exact lt_of_le_of_ne h.two_le hn_ne_two.symm

    have hphi_even : Even (Nat.totient n) := by
      exact Nat.totient_even hn_gt_two

    rcases hphi_even with ⟨k, hk⟩
    rcases h.totient_dvd_pred with ⟨m, hm⟩

    have hpred_even : Even (n - 1) := by
      refine ⟨k * m, ?_⟩
      calc
        n - 1 = Nat.totient n * m := by simpa [Nat.mul_comm] using hm.symm
        _ = (2 * k) * m := by rw [hk]
        _ = 2 * (k * m) := by ring

    rcases hEven with ⟨a, ha⟩
    rcases hpred_even with ⟨b, hb⟩
    omega
  · exact hOdd

/--
If `p^2 ∣ n` for a prime `p`, then `p ∣ φ(n)`.

This is the key local ingredient for squarefreeness:
`φ(p^2) = p(p-1)` is divisible by `p`, and `φ(p^2) ∣ φ(n)` whenever `p^2 ∣ n`.
-/
theorem prime_dvd_totient_of_sq_dvd {n p : ℕ} (hp : Nat.Prime p) (hpp : p * p ∣ n) :
    p ∣ Nat.totient n := by
  have hpp_tot : Nat.totient (p * p) ∣ Nat.totient n := by
    exact Nat.totient_dvd_of_dvd hpp
  have hp_dvd_phi_pp : p ∣ Nat.totient (p * p) := by
    rw [Nat.totient_mul_of_prime_of_dvd hp (dvd_rfl : p ∣ p)]
    refine ⟨Nat.totient p, ?_⟩
    ring
  exact dvd_trans hp_dvd_phi_pp hpp_tot

/--
A Lehmer composite is squarefree.

If `p^2 ∣ n` for a prime `p`, then `p ∣ φ(n)`.
Since `φ(n) ∣ (n-1)`, we get `p ∣ (n-1)`.
But already `p ∣ n`, so `p ∣ 1`, impossible.
-/
theorem LehmerComposite.squarefree {n : ℕ} (h : LehmerComposite n) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp

  have hp_dvd_phi_n : p ∣ Nat.totient n := by
    exact prime_dvd_totient_of_sq_dvd hp hpp

  have hp_dvd_pred : p ∣ (n - 1) := by
    exact dvd_trans hp_dvd_phi_n h.totient_dvd_pred

  have hp_dvd_n : p ∣ n := by
    exact dvd_trans (dvd_mul_right p p) hpp

  have hsub : n - (n - 1) = 1 := by
    have hs : n = (n - 1) + 1 := by
      exact Nat.succ_pred_eq_of_pos h.pos
    omega

  have hp_dvd_one : p ∣ 1 := by
    have hp_dvd_diff : p ∣ n - (n - 1) := by
      exact Nat.dvd_sub hp_dvd_n hp_dvd_pred
    simpa [hsub] using hp_dvd_diff

  exact hp.not_dvd_one hp_dvd_one

/--
Main structural package used later:
a Lehmer composite is both odd and squarefree.
-/
theorem LehmerComposite.odd_and_squarefree {n : ℕ} (h : LehmerComposite n) :
    Odd n ∧ Squarefree n := by
  exact ⟨h.odd, h.squarefree⟩

end Basic
end Lehmer