-- FILE: Lean/Lehmer/CaseC/GapClosure/SupportProfiles.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.Totient : def thm
- Lehmer.Basic.PrimeSupport : thm
- Lehmer.Basic.OddSquarefree : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.Totient
import Lehmer.Basic.PrimeSupport
import Lehmer.Basic.OddSquarefree

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def supportIndex (S : Finset ℕ) : ℚ :=
  S.prod (fun p => (p : ℚ) / ((p - 1 : ℕ) : ℚ))

abbrev IS (S : Finset ℕ) : ℚ :=
  supportIndex S

@[simp] theorem supportIndex_def (S : Finset ℕ) :
    supportIndex S = S.prod (fun p => (p : ℚ) / ((p - 1 : ℕ) : ℚ)) := rfl

@[simp] theorem IS_def (S : Finset ℕ) :
    IS S = S.prod (fun p => (p : ℚ) / ((p - 1 : ℕ) : ℚ)) := rfl

@[simp] theorem supportIndex_empty :
    supportIndex ∅ = 1 := by
  simp [supportIndex]

@[simp] theorem supportIndex_singleton (p : ℕ) :
    supportIndex ({p} : Finset ℕ) = (p : ℚ) / ((p - 1 : ℕ) : ℚ) := by
  simp [supportIndex]

theorem supportIndex_insert {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) :
    supportIndex (insert p S) =
      ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) * supportIndex S := by
  rw [supportIndex, Finset.prod_insert hp, supportIndex]

theorem supportIndex_of_mem_erase {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    supportIndex S =
      ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) * supportIndex (S.erase p) := by
  have hp' : p ∉ S.erase p := by
    simp
  simpa [Finset.insert_erase hp] using
    (supportIndex_insert (S := S.erase p) (p := p) hp')

def supportGap (S : Finset ℕ) : ℚ :=
  supportIndex S - (Nat.floor (supportIndex S) : ℚ)

abbrev Delta (S : Finset ℕ) : ℚ :=
  supportGap S

@[simp] theorem supportGap_def (S : Finset ℕ) :
    supportGap S = supportIndex S - (Nat.floor (supportIndex S) : ℚ) := rfl

@[simp] theorem Delta_def (S : Finset ℕ) :
    Delta S = supportIndex S - (Nat.floor (supportIndex S) : ℚ) := rfl

@[simp] theorem supportGap_empty :
    supportGap ∅ = 0 := by
  simp [supportGap, supportIndex]

def supportProfileOfNat (n : ℕ) : ℚ :=
  supportIndex (primeSupport n)

@[simp] theorem supportProfileOfNat_def (n : ℕ) :
    supportProfileOfNat n = supportIndex (primeSupport n) := rfl

/--
For a prime support, the support index is the quotient of the support product
by the rational product of the shifted primes.
-/
theorem supportIndex_eq_supportProd_div_prod_sub_one_of_prime
    {S : Finset ℕ}
    (hPrime : ∀ p ∈ S, Nat.Prime p) :
    supportIndex S =
      (supportProd S : ℚ) / (S.prod (fun p => ((p : ℚ) - 1))) := by
  classical
  revert hPrime
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp [supportIndex, supportProd]
  · intro p T hpT ih hPrimeAll
    have hpprime : Nat.Prime p := hPrimeAll p (Finset.mem_insert_self p T)
    have hPrimeT : ∀ q ∈ T, Nat.Prime q := by
      intro q hq
      exact hPrimeAll q (Finset.mem_insert_of_mem hq)
    have ihT := ih hPrimeT
    have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hpprime.two_le
    have hpm1 : (((p - 1 : ℕ) : ℚ)) = ((p : ℚ) - 1) := by
      rw [Nat.cast_sub hp1]
      norm_num
    have hp_sub_ne_zero : ((p : ℚ) - 1) ≠ 0 := by
      intro h0
      have hp_eq_one_q : (p : ℚ) = 1 := by linarith
      have hp_eq_one : p = 1 := by exact_mod_cast hp_eq_one_q
      exact hpprime.ne_one hp_eq_one
    have hprod_ne_zero : T.prod (fun q => ((q : ℚ) - 1)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro q hq
      have hqprime : Nat.Prime q := hPrimeT q hq
      intro h0
      have hq_eq_one_q : (q : ℚ) = 1 := by linarith
      have hq_eq_one : q = 1 := by exact_mod_cast hq_eq_one_q
      exact hqprime.ne_one hq_eq_one
    rw [supportIndex_insert hpT, supportProd_insert hpT, Finset.prod_insert hpT, ihT, hpm1]
    field_simp [hp_sub_ne_zero, hprod_ne_zero]
    rw [Nat.cast_mul]

theorem supportProfileOfNat_eq_totientIndex_of_squarefree
    {n : ℕ} (hSq : Squarefree n) :
    supportProfileOfNat n = totientIndex n := by
  have hPrime : ∀ p ∈ primeSupport n, Nat.Prime p := by
    intro p hp
    exact prime_of_mem_primeSupport hp
  have hIndex :
      supportIndex (primeSupport n) =
        (supportProd (primeSupport n) : ℚ) /
          ((primeSupport n).prod (fun p => ((p : ℚ) - 1))) := by
    exact supportIndex_eq_supportProd_div_prod_sub_one_of_prime hPrime
  have hNum : (supportProd (primeSupport n) : ℚ) = (n : ℚ) := by
    exact_mod_cast supportProd_primeSupport_of_squarefree hSq
  have hDen : totientQ n = (primeSupport n).prod (fun p => ((p : ℚ) - 1)) := by
    exact totientQ_eq_prod_sub_one_of_squarefree hSq
  calc
    supportProfileOfNat n = supportIndex (primeSupport n) := by
      rfl
    _ = (supportProd (primeSupport n) : ℚ) /
          ((primeSupport n).prod (fun p => ((p : ℚ) - 1))) := by
      exact hIndex
    _ = (n : ℚ) / totientQ n := by
      rw [hNum, ← hDen]
    _ = totientIndex n := by
      rw [totientIndex_eq]

theorem supportProfileOfNat_eq_totientIndex_of_LehmerComposite
    {n : ℕ} (h : LehmerComposite n) :
    supportProfileOfNat n = totientIndex n := by
  exact supportProfileOfNat_eq_totientIndex_of_squarefree h.squarefree

end GapClosure
end CaseC
end Lehmer