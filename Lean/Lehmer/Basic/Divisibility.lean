-- FILE: Lean/Lehmer/Basic/Divisibility.lean
import Mathlib
import Lehmer.Basic.Defs
import Lehmer.Basic.OddSquarefree
import Lehmer.Basic.SupportLcm
import Lehmer.Basic.PrimeSupport

namespace Lehmer
namespace Basic

/--
For a Lehmer composite `n`, every prime divisor `p` of `n` satisfies `(p - 1) ∣ (n - 1)`.

This is the local divisibility condition coming from `φ(n) ∣ (n - 1)`.
-/
theorem local_divisibility_of_dvd_pred {n p : ℕ}
    (hL : LehmerComposite n) (hp : Nat.Prime p) (hpn : p ∣ n) :
    p - 1 ∣ n - 1 := by
  have htotdvd : Nat.totient p ∣ Nat.totient n := by
    exact Nat.totient_dvd_of_dvd hpn
  rw [hp.totient] at htotdvd
  exact dvd_trans htotdvd hL.totient_dvd_pred

/--
For a Lehmer composite `n`, the support lcm divides `n - 1`.

This is the support-level form of the local divisibility constraints.
-/
theorem supportLcm_dvd_pred_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    supportLcm (primeSupport n) ∣ n - 1 := by
  apply Basic.supportLcm_dvd_of_forall_dvd
  intro p hp
  exact local_divisibility_of_dvd_pred hL
    (prime_of_mem_primeSupport hp)
    (dvd_of_mem_primeSupport hp)

/--
If `S` is a finite support all of whose shifted primes divide `m`,
then the support lcm also divides `m`.
-/
theorem supportLcm_dvd_of_forall_dvd {S : Finset ℕ} {m : ℕ}
    (hS : ∀ p ∈ S, p - 1 ∣ m) :
    supportLcm S ∣ m := by
  exact Basic.supportLcm_dvd_of_forall_dvd hS

/--
For a Lehmer composite `n`, every element of `primeSupport n`
satisfies the local divisibility condition `(p - 1) ∣ (n - 1)`.
-/
theorem local_divisibility_on_primeSupport {n : ℕ}
    (hL : LehmerComposite n) :
    ∀ p ∈ primeSupport n, p - 1 ∣ n - 1 := by
  intro p hp
  exact local_divisibility_of_dvd_pred hL
    (prime_of_mem_primeSupport hp)
    (dvd_of_mem_primeSupport hp)

/--
A packaged version of the local divisibility + lcm consequence.

This is the Lean analogue of the paper statement:
for every `p ∣ n`, one has `(p-1) ∣ (n-1)`, hence
`L(n) := lcm {p-1 : p ∣ n}` also divides `n-1`.
-/
theorem local_divisibility_and_supportLcm {n : ℕ}
    (hL : LehmerComposite n) :
    (∀ p, Nat.Prime p → p ∣ n → p - 1 ∣ n - 1) ∧
      supportLcm (primeSupport n) ∣ n - 1 := by
  refine ⟨?_, supportLcm_dvd_pred_of_LehmerComposite hL⟩
  intro p hp hpn
  exact local_divisibility_of_dvd_pred hL hp hpn

end Basic
end Lehmer