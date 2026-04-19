-- FILE: Lean/Lehmer/Support/IncrementIdentity.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.PrimeSupport : thm
- Lehmer.Basic.SupportLcm : thm
- Lehmer.Support.IncrementRatio : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.PrimeSupport
import Lehmer.Basic.SupportLcm
import Lehmer.Support.IncrementRatio

namespace Lehmer
namespace Support

open Lehmer.Basic

/-!
# Increment identity on supports

This file converts the quotient definition of `incrementRatio` into the local
gcd/lcm identity used by the later structural support layers.
-/

/--
If `p ∈ S`, then the support lcm of `S` is obtained by adjoining the shifted
factor `p - 1` to the erased support.
-/
theorem supportLcm_eq_lcm_erase_sub
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S) :
    supportLcm S = Nat.lcm (p - 1) (supportLcm (S.erase p)) := by
  calc
    supportLcm S = supportLcm (insert p (S.erase p)) := by
      rw [Finset.insert_erase hp]
    _ = Nat.lcm (p - 1) (supportLcm (S.erase p)) := by
      rw [supportLcm_insert]
      simp

/--
Symmetric rewriting form of `supportLcm S` under `hp : p ∈ S`.
-/
theorem supportLcm_eq_lcm_erase_sub'
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S) :
    supportLcm S = Nat.lcm (supportLcm (S.erase p)) (p - 1) := by
  rw [supportLcm_eq_lcm_erase_sub hp, Nat.lcm_comm]

/--
Intermediate quotient form of the increment ratio under `hp : p ∈ S`.
-/
theorem incrementRatio_eq_lcm_div
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S) :
    incrementRatio S p =
      Nat.lcm (p - 1) (supportLcm (S.erase p)) / supportLcm (S.erase p) := by
  rw [incrementRatio_def, supportLcm_eq_lcm_erase_sub hp]

/--
Symmetric intermediate quotient form of the increment ratio under `hp : p ∈ S`.
-/
theorem incrementRatio_eq_lcm_div'
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S) :
    incrementRatio S p =
      Nat.lcm (supportLcm (S.erase p)) (p - 1) / supportLcm (S.erase p) := by
  rw [incrementRatio_eq_lcm_div hp, Nat.lcm_comm]

/--
Arithmetic lcm/gcd identity specialized to a quotient by the first argument.
-/
theorem lcm_div_left_eq_div_gcd
    {a b : ℕ}
    (ha : a ≠ 0) :
    Nat.lcm a b / a = b / Nat.gcd a b := by
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
  have hg_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha_pos
  rcases Nat.dvd_lcm_left a b with ⟨l, hl⟩
  rcases Nat.gcd_dvd_right a b with ⟨k, hk⟩
  
  have hmul : Nat.gcd a b * (a * l) = a * (Nat.gcd a b * k) := by
    calc
      Nat.gcd a b * (a * l) = Nat.gcd a b * Nat.lcm a b := congrArg (fun x => Nat.gcd a b * x) hl.symm
      _ = a * b := Nat.gcd_mul_lcm a b
      _ = a * (Nat.gcd a b * k) := congrArg (fun x => a * x) hk
      
  have h1 : a * (Nat.gcd a b * l) = a * (Nat.gcd a b * k) := by
    calc
      a * (Nat.gcd a b * l) = (a * Nat.gcd a b) * l := (Nat.mul_assoc a (Nat.gcd a b) l).symm
      _ = (Nat.gcd a b * a) * l := congrArg (fun x => x * l) (Nat.mul_comm a (Nat.gcd a b))
      _ = Nat.gcd a b * (a * l) := Nat.mul_assoc (Nat.gcd a b) a l
      _ = a * (Nat.gcd a b * k) := hmul
      
  have h2 : Nat.gcd a b * l = Nat.gcd a b * k :=
    Nat.eq_of_mul_eq_mul_left ha_pos h1
    
  have h3 : l = k :=
    Nat.eq_of_mul_eq_mul_left hg_pos h2
    
  calc
    Nat.lcm a b / a = (a * l) / a := congrArg (fun x => x / a) hl
    _ = (l * a) / a := congrArg (fun x => x / a) (Nat.mul_comm a l)
    _ = l := Nat.mul_div_left l ha_pos
    _ = k := h3
    _ = (k * Nat.gcd a b) / Nat.gcd a b := Eq.symm (Nat.mul_div_left k hg_pos)
    _ = (Nat.gcd a b * k) / Nat.gcd a b := congrArg (fun x => x / Nat.gcd a b) (Nat.mul_comm k (Nat.gcd a b))
    _ = b / Nat.gcd a b := congrArg (fun x => x / Nat.gcd a b) hk.symm

/--
Main increment identity under `hp : p ∈ S`.
-/
theorem incrementRatio_eq_div_gcd
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    incrementRatio S p =
      (p - 1) / Nat.gcd (supportLcm (S.erase p)) (p - 1) := by
  rw [incrementRatio_eq_lcm_div' hp]
  exact lcm_div_left_eq_div_gcd
    (supportLcm_erase_ne_zero_of_mem_of_all_prime hp hS)

/--
Commuted-gcd form of the main increment identity.
-/
theorem incrementRatio_eq_div_gcd_comm
    {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    incrementRatio S p =
      (p - 1) / Nat.gcd (p - 1) (supportLcm (S.erase p)) := by
  rw [incrementRatio_eq_div_gcd hp hS, Nat.gcd_comm]

end Support
end Lehmer