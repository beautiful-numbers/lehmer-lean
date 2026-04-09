-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossing.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Data.Real.Basic : def thm
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Parameters : def
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pipeline.Thresholds : def thm
-/

import Mathlib.Data.Real.Basic
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Parameters
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.Mreq
import Lehmer.Pipeline.Thresholds

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot

/--
Local alias of the shared paper constant `C1 = 10^{-3}`.
-/
noncomputable abbrev C1 : ℝ :=
  Lehmer.Pivot.C1

@[simp] theorem C1_def :
    C1 = (1 : ℝ) / 1000 := by
  simpa [C1] using Lehmer.Pivot.C1_def

/--
Local alias of the shared paper pivot threshold `Y0 = 30000`.
-/
abbrev Y0 : ℕ :=
  Lehmer.Pivot.Y0

@[simp] theorem Y0_def :
    Y0 = 30000 := by
  simpa [Y0] using Lehmer.Pivot.Y0_def

/--
Paper real threshold
`T_B = max(17, e^6, 10/C1, Y0)`.

We keep it as a real quantity because it is introduced analytically in the
paper before passing to the prime threshold `Y*`.
-/
noncomputable def TB : ℝ :=
  max (17 : ℝ) (max (Real.exp 6) (max ((10 : ℝ) / C1) (Y0 : ℝ)))

@[simp] theorem TB_def :
    TB = max (17 : ℝ) (max (Real.exp 6) (max ((10 : ℝ) / C1) (Y0 : ℝ))) := rfl

/--
The prime threshold `Y*` is the smallest prime at least `⌈T_B⌉`.

This matches the paper statement "the smallest prime ≥ T_B" in a Lean-friendly
discrete form.
-/
noncomputable def Ystar : ℕ :=
  nextPrimeGe (Nat.ceil TB)

@[simp] theorem Ystar_def :
    Ystar = nextPrimeGe (Nat.ceil TB) := rfl

/--
`Y*` lies above `T_B` after ceiling/discretization.
-/
theorem TB_le_Ystar : TB ≤ (Ystar : ℝ) := by
  have hceil : TB ≤ (Nat.ceil TB : ℝ) := Nat.le_ceil TB
  have hnext_nat : Nat.ceil TB ≤ Ystar := nextPrimeGe_ge (Nat.ceil TB)
  have hnext : (Nat.ceil TB : ℝ) ≤ (Ystar : ℝ) := by
    exact_mod_cast hnext_nat
  exact le_trans hceil hnext

/--
`Y*` is prime.
-/
theorem Ystar_prime :
    Nat.Prime Ystar := by
  simpa [Ystar] using nextPrimeGe_prime (Nat.ceil TB)

/--
Auxiliary lower threshold comparison used to derive `Y0 ≤ y` from `Ystar ≤ y`.
-/
theorem Y0_le_TB : (Y0 : ℝ) ≤ TB := by
  rw [TB_def]
  have h1 : (Y0 : ℝ) ≤ max ((10 : ℝ) / C1) (Y0 : ℝ) := le_max_right _ _
  have h2 :
      max ((10 : ℝ) / C1) (Y0 : ℝ) ≤
        max (Real.exp 6) (max ((10 : ℝ) / C1) (Y0 : ℝ)) := le_max_right _ _
  have h3 :
      max (Real.exp 6) (max ((10 : ℝ) / C1) (Y0 : ℝ)) ≤
        max (17 : ℝ) (max (Real.exp 6) (max ((10 : ℝ) / C1) (Y0 : ℝ))) := le_max_right _ _
  exact le_trans h1 (le_trans h2 h3)

/--
Natural-number form of the threshold comparison `Y0 ≤ Ystar`.
-/
theorem Y0_le_Ystar : Y0 ≤ Ystar := by
  have h : (Y0 : ℝ) ≤ (Ystar : ℝ) := le_trans Y0_le_TB TB_le_Ystar
  exact_mod_cast h

/--
A simple concrete lower bound on `Ystar`.
-/
theorem four_le_Ystar : 4 ≤ Ystar := by
  have h4 : 4 ≤ Y0 := by
    simp [Y0]
  exact le_trans h4 Y0_le_Ystar

/--
Pipeline threshold `YA` lies below the Case B terminal threshold `Ystar`.
-/
theorem YA_le_Ystar : Lehmer.Pipeline.YA ≤ Ystar := by
  have hYA4 : Lehmer.Pipeline.YA ≤ 4 := by
    simp [Lehmer.Pipeline.YA]
  exact le_trans hYA4 four_le_Ystar

/--
Pipeline threshold `YC` lies below the Case B terminal threshold `Ystar`.
-/
theorem YC_le_Ystar : Lehmer.Pipeline.YC ≤ Ystar := by
  have hYC4 : Lehmer.Pipeline.YC ≤ 4 := by
    simp [Lehmer.Pipeline.YC]
  exact le_trans hYC4 four_le_Ystar

/--
Paper-facing closed Case B majorant.

This is the public Case B no-crossing majorant used in the paper-facing API.
It is intentionally exposed under the name `M`.
-/
noncomputable def M (y : ℕ) : ℝ :=
  ((20 : ℝ) / 3) * (yB y) / Real.log (yB y) +
    3 * (Real.log (yB y)) ^ 4 + 2

@[simp] theorem M_def (y : ℕ) :
    M y =
      ((20 : ℝ) / 3) * (yB y) / Real.log (yB y) +
        3 * (Real.log (yB y)) ^ 4 + 2 := rfl

/--
Paper-facing no-crossing target:
the Case B closed majorant lies strictly below the pivot demand threshold.
-/
def NoCrossingAt (y : ℕ) : Prop :=
  M y < (mreq y : ℝ)

@[simp] theorem NoCrossingAt_def (y : ℕ) :
    NoCrossingAt y = (M y < (mreq y : ℝ)) := rfl

/--
Uniform no-crossing target beyond `Y*`.
-/
def NoCrossingBeyondYstar : Prop :=
  ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt y

@[simp] theorem NoCrossingBeyondYstar_def :
    NoCrossingBeyondYstar =
      (∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt y) := rfl

/--
Interface constructor for no-crossing at a given pivot.
-/
theorem noCrossingAt_of_assumption
    {y : ℕ}
    (h : M y < (mreq y : ℝ)) :
    NoCrossingAt y := by
  exact h

/--
Uniform no-crossing constructor.
-/
theorem noCrossingBeyondYstar_of_assumption
    (h : ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → M y < (mreq y : ℝ)) :
    NoCrossingBeyondYstar := by
  intro y hy hp
  exact h y hy hp

/--
Elimination form of the uniform no-crossing interface.
-/
theorem noCrossingAt_of_noCrossingBeyondYstar
    (h : NoCrossingBeyondYstar)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    M y < (mreq y : ℝ) := by
  exact h y hy hp

/--
Convenient packaged form for downstream contradiction layers.
-/
theorem noCrossing_ready_for_contradiction
    (h : NoCrossingBeyondYstar)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt y := by
  exact h y hy hp

end CaseB
end Lehmer