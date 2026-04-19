-- FILE: Lean/Lehmer/Support/GenericEntangled.lean
import Lehmer.Prelude
import Lehmer.Support.IncrementRatio
import Lehmer.Support.IncrementIdentity

namespace Lehmer
namespace Support

open Lehmer.Basic

/-!
# Generic / entangled classification on supports

This file introduces the low-level dichotomy between large and small increment
ratios relative to an external threshold function.
-/

/--
A prime `p` is generic in the support `S` at level `y` (relative to the
threshold `h`) if its increment ratio is strictly larger than the threshold.
-/
def genericIn (h : ℕ → ℕ) (S : Finset ℕ) (y p : ℕ) : Prop :=
  h y < incrementRatio S p

/--
A prime `p` is entangled in the support `S` at level `y` (relative to the
threshold `h`) if its increment ratio is at most the threshold.
-/
def entangledIn (h : ℕ → ℕ) (S : Finset ℕ) (y p : ℕ) : Prop :=
  incrementRatio S p ≤ h y

@[simp] theorem genericIn_def (h : ℕ → ℕ) (S : Finset ℕ) (y p : ℕ) :
    genericIn h S y p = (h y < incrementRatio S p) := rfl

@[simp] theorem entangledIn_def (h : ℕ → ℕ) (S : Finset ℕ) (y p : ℕ) :
    entangledIn h S y p = (incrementRatio S p ≤ h y) := rfl

/--
Every local increment is either generic or entangled.
-/
theorem generic_or_entangled
    (h : ℕ → ℕ) (S : Finset ℕ) (y p : ℕ) :
    genericIn h S y p ∨ entangledIn h S y p := by
  rw [genericIn_def, entangledIn_def]
  exact lt_or_ge (h y) (incrementRatio S p)

/--
Generic and entangled are mutually exclusive.
-/
theorem generic_not_entangled
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hg : genericIn h S y p) :
    ¬ entangledIn h S y p := by
  rw [genericIn_def] at hg
  rw [entangledIn_def]
  exact not_le_of_gt hg

/--
Entangled and generic are mutually exclusive.
-/
theorem entangled_not_generic
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (he : entangledIn h S y p) :
    ¬ genericIn h S y p := by
  rw [entangledIn_def] at he
  rw [genericIn_def]
  exact not_lt_of_ge he

/--
Logical complementarity: not generic is equivalent to entangled.
-/
theorem not_generic_iff_entangled
    (h : ℕ → ℕ) (S : Finset ℕ) (y p : ℕ) :
    ¬ genericIn h S y p ↔ entangledIn h S y p := by
  rw [genericIn_def, entangledIn_def]
  exact not_lt

/--
Logical complementarity: not entangled is equivalent to generic.
-/
theorem not_entangled_iff_generic
    (h : ℕ → ℕ) (S : Finset ℕ) (y p : ℕ) :
    ¬ entangledIn h S y p ↔ genericIn h S y p := by
  rw [genericIn_def, entangledIn_def]
  exact not_le

/--
If the threshold increases, genericity can only become harder.
-/
theorem genericIn_of_threshold_le
    {h₁ h₂ : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hy : h₁ y ≤ h₂ y)
    (hg : genericIn h₂ S y p) :
    genericIn h₁ S y p := by
  rw [genericIn_def] at hg ⊢
  exact lt_of_le_of_lt hy hg

/--
If the threshold increases, entanglement can only become easier.
-/
theorem entangledIn_of_threshold_le
    {h₁ h₂ : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hy : h₁ y ≤ h₂ y)
    (he : entangledIn h₁ S y p) :
    entangledIn h₂ S y p := by
  rw [entangledIn_def] at he ⊢
  exact le_trans he hy

/--
A generic increment stays generic under pointwise lowering of the threshold.
-/
theorem genericIn_mono_threshold
    {h₁ h₂ : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hmono : ∀ z, h₁ z ≤ h₂ z)
    (hg : genericIn h₂ S y p) :
    genericIn h₁ S y p := by
  exact genericIn_of_threshold_le (hmono y) hg

/--
An entangled increment stays entangled under pointwise raising of the threshold.
-/
theorem entangledIn_mono_threshold
    {h₁ h₂ : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hmono : ∀ z, h₁ z ≤ h₂ z)
    (he : entangledIn h₁ S y p) :
    entangledIn h₂ S y p := by
  exact entangledIn_of_threshold_le (hmono y) he

/--
Under membership and primality of the support, genericity can be rewritten via
the gcd/lcm increment identity.
-/
theorem genericIn_iff_threshold_lt_div_gcd
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    genericIn h S y p ↔
      h y < (p - 1) / Nat.gcd (supportLcm (S.erase p)) (p - 1) := by
  rw [genericIn_def, incrementRatio_eq_div_gcd hp hS]

/--
Under membership and primality of the support, entanglement can be rewritten via
the gcd/lcm increment identity.
-/
theorem entangledIn_iff_div_gcd_le_threshold
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hp : p ∈ S)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    entangledIn h S y p ↔
      (p - 1) / Nat.gcd (supportLcm (S.erase p)) (p - 1) ≤ h y := by
  rw [entangledIn_def, incrementRatio_eq_div_gcd hp hS]

end Support
end Lehmer