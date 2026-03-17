-- FILE: Lean/Lehmer/Support/IncrementIdentity.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.SupportLcm : def thm
- Lehmer.Support.IncrementRatio : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.SupportLcm
import Lehmer.Support.IncrementRatio

namespace Lehmer
namespace Support

open Lehmer.Basic

def incrementIdentityRhs (S : Finset ℕ) (p : ℕ) : ℕ :=
  (p - 1) / Nat.gcd (p - 1) (supportLcm (S.erase p))

@[simp] theorem incrementIdentityRhs_def (S : Finset ℕ) (p : ℕ) :
    incrementIdentityRhs S p =
      (p - 1) / Nat.gcd (p - 1) (supportLcm (S.erase p)) := rfl

def incrementIdentityDen (S : Finset ℕ) (p : ℕ) : ℕ :=
  Nat.gcd (p - 1) (supportLcm (S.erase p))

@[simp] theorem incrementIdentityDen_def (S : Finset ℕ) (p : ℕ) :
    incrementIdentityDen S p =
      Nat.gcd (p - 1) (supportLcm (S.erase p)) := rfl

theorem incrementIdentityDen_dvd_sub (S : Finset ℕ) (p : ℕ) :
    incrementIdentityDen S p ∣ (p - 1) := by
  dsimp [incrementIdentityDen]
  exact Nat.gcd_dvd_left (p - 1) (supportLcm (S.erase p))

theorem incrementIdentityDen_dvd_supportLcm_erase (S : Finset ℕ) (p : ℕ) :
    incrementIdentityDen S p ∣ supportLcm (S.erase p) := by
  dsimp [incrementIdentityDen]
  exact Nat.gcd_dvd_right (p - 1) (supportLcm (S.erase p))

@[simp] theorem incrementIdentityRhs_of_not_mem {S : Finset ℕ} {p : ℕ}
    (hp : p ∉ S) :
    incrementIdentityRhs S p =
      (p - 1) / Nat.gcd (p - 1) (supportLcm S) := by
  simp [incrementIdentityRhs, supportLcm_erase_of_not_mem hp]

theorem incrementRatio_eq_incrementIdentityRhs
    (S : Finset ℕ) (p : ℕ) (hp : p ∈ S)
    (hL : supportLcm (S.erase p) ≠ 0) :
    incrementRatio S p = incrementIdentityRhs S p := by
  let a := p - 1
  let b := supportLcm (S.erase p)
  let g := Nat.gcd a b
  have hne : p ∉ S.erase p := by
    simp
  have hinsert : insert p (S.erase p) = S := by
    exact Finset.insert_erase hp
  have hbpos : 0 < b := Nat.pos_of_ne_zero hL
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right a hbpos
  have hgdvd : g ∣ a := by
    dsimp [g]
    exact Nat.gcd_dvd_left a b
  rcases hgdvd with ⟨k, hk⟩
  have hbdvd : b ∣ Nat.lcm a b := by
    exact Nat.dvd_lcm_right a b
  rcases hbdvd with ⟨t, ht⟩
  have hcancel_b : g * t = a := by
    apply Nat.eq_of_mul_eq_mul_right hbpos
    calc
      (g * t) * b = g * (t * b) := by ring
      _ = g * (b * t) := by rw [Nat.mul_comm t b]
      _ = g * Nat.lcm a b := by rw [ht]
      _ = a * b := by
        dsimp [g]
        exact Nat.gcd_mul_lcm a b
  have ht_eq_k : t = k := by
    apply Nat.eq_of_mul_eq_mul_left hgpos
    calc
      g * t = a := hcancel_b
      _ = g * k := hk

  rw [incrementRatio_def, incrementIdentityRhs]
  rw [← hinsert, supportLcm_insert hne]
  have herase : supportLcm ((insert p (S.erase p)).erase p) = b := by
    simp [b, hne]
  rw [herase]
  change Nat.lcm a b / b = a / g
  rw [ht, ht_eq_k]
  have hleft : b * k / b = k := by
    simpa [Nat.mul_comm] using (Nat.mul_div_right k hbpos)
  rw [hleft, hk]
  symm
  simpa [Nat.mul_comm] using (Nat.mul_div_right k hgpos)

theorem RS_eq_incrementIdentityRhs
    (S : Finset ℕ) (p : ℕ) (hp : p ∈ S)
    (hL : supportLcm (S.erase p) ≠ 0) :
    RS S p = (p - 1) / Nat.gcd (p - 1) (supportLcm (S.erase p)) := by
  simpa [RS, incrementIdentityRhs] using
    incrementRatio_eq_incrementIdentityRhs S p hp hL

end Support
end Lehmer