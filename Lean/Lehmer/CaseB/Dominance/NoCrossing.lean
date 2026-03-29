-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossing.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Data.Real.Basic : def thm
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Parameters : def
- Lehmer.CaseB.Dominance.MajorantMc : def thm
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pipeline.Thresholds : def thm
-/

import Mathlib.Data.Real.Basic
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Dominance.MajorantMc
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
Continuous paper majorant used in the analytic comparison step.
-/
noncomputable def Mhat (t : ℝ) : ℝ :=
  ((20 : ℝ) / 3) * (t / Real.log t) + 3 * (Real.log t)^4 + 2

@[simp] theorem Mhat_def (t : ℝ) :
    Mhat t =
      ((20 : ℝ) / 3) * (t / Real.log t) + 3 * (Real.log t)^4 + 2 := rfl

/--
Continuous analytic barrier from the paper.
-/
noncomputable def analyticBarrier (t : ℝ) : ℝ :=
  C1 * t^2 / Real.log t

@[simp] theorem analyticBarrier_def (t : ℝ) :
    analyticBarrier t = C1 * t^2 / Real.log t := rfl

/--
Large-`y` analytic dominance target from the paper.
-/
def UniformDominanceAt (t : ℝ) : Prop :=
  McNat (Nat.floor t) < Nat.ceil (analyticBarrier t)

@[simp] theorem UniformDominanceAt_def (t : ℝ) :
    UniformDominanceAt t =
      (McNat (Nat.floor t) < Nat.ceil (analyticBarrier t)) := rfl

/--
Discrete large-`y` dominance target specialized to integer pivots.
-/
def UniformDominanceAtNat (y : ℕ) : Prop :=
  Mc y < analyticBarrier (y : ℝ)

@[simp] theorem UniformDominanceAtNat_def (y : ℕ) :
    UniformDominanceAtNat y =
      (Mc y < analyticBarrier (y : ℝ)) := rfl

/--
Paper-facing no-crossing target:
the Case B closed majorant lies strictly below the pivot demand threshold.
-/
def NoCrossingAt (y : ℕ) : Prop :=
  McNat y < mreq y

@[simp] theorem NoCrossingAt_def (y : ℕ) :
    NoCrossingAt y = (McNat y < mreq y) := rfl

/--
Uniform no-crossing target beyond `Y*`.
-/
def NoCrossingBeyondYstar : Prop :=
  ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt y

@[simp] theorem NoCrossingBeyondYstar_def :
    NoCrossingBeyondYstar =
      (∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt y) := rfl

/--
Analytic package needed to close the no-crossing step.

This is the exact missing bridge layer:
1. dominate `Mc` by the continuous paper majorant `Mhat`,
2. compare `Mhat` to the analytic barrier,
3. discretize from the real strict inequality to `McNat`,
4. compare the discretized barrier to `mreq`.
-/
structure CaseBAnalyticBounds where
  /-- Continuous domination of the closed majorant by the paper majorant. -/
  Mc_le_Mhat :
    ∀ y : ℕ, 3 ≤ y → Mc y ≤ Mhat (y : ℝ)
  /-- Strict analytic dominance beyond `T_B`. -/
  Mhat_lt_barrier :
    ∀ t : ℝ, TB ≤ t → Mhat t < analyticBarrier t
  /-- Discretization step from the real strict dominance to the natural majorant. -/
  McNat_lt_barrierCeil :
    ∀ y : ℕ, Y0 ≤ y →
      Mc y < analyticBarrier (y : ℝ) →
      McNat y < Nat.ceil (analyticBarrier (y : ℝ))
  /-- Comparison of the discretized analytic barrier with the pivot demand threshold. -/
  barrierCeil_le_mreq :
    ∀ y : ℕ, Y0 ≤ y →
      Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y

/--
Interface constructor for large-`y` dominance at an integer pivot.
-/
theorem uniformDominanceAtNat_of_assumption
    {y : ℕ}
    (h : Mc y < analyticBarrier (y : ℝ)) :
    UniformDominanceAtNat y := by
  exact h

/--
Interface constructor for no-crossing at a given pivot.
-/
theorem noCrossingAt_of_assumption
    {y : ℕ}
    (h : McNat y < mreq y) :
    NoCrossingAt y := by
  exact h

/--
Main analytic bridge:
from the paper large-`y` comparison package, obtain `McNat y < mreq y`.
-/
theorem noCrossingAt_of_analyticBounds
    (bounds : CaseBAnalyticBounds)
    {y : ℕ} (hy : Ystar ≤ y) :
    NoCrossingAt y := by
  rw [NoCrossingAt_def]

  have hy_real : (Ystar : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hy

  have hTB : TB ≤ (y : ℝ) := by
    exact le_trans TB_le_Ystar hy_real

  have hY0_real : (Y0 : ℝ) ≤ (y : ℝ) := by
    exact le_trans Y0_le_TB hTB

  have hY0 : Y0 ≤ y := by
    exact_mod_cast hY0_real

  have h3_le_Y0 : 3 ≤ Y0 := by
    decide

  have h3 : 3 ≤ y := by
    exact le_trans h3_le_Y0 hY0

  have hMc_le_Mhat : Mc y ≤ Mhat (y : ℝ) := by
    exact bounds.Mc_le_Mhat y h3

  have hMhat_lt_barrier : Mhat (y : ℝ) < analyticBarrier (y : ℝ) := by
    exact bounds.Mhat_lt_barrier (y : ℝ) hTB

  have hMc_lt_barrier : Mc y < analyticBarrier (y : ℝ) := by
    exact lt_of_le_of_lt hMc_le_Mhat hMhat_lt_barrier

  have hdisc : McNat y < Nat.ceil (analyticBarrier (y : ℝ)) := by
    exact bounds.McNat_lt_barrierCeil y hY0 hMc_lt_barrier

  have hmreq : Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y := by
    exact bounds.barrierCeil_le_mreq y hY0

  exact lt_of_lt_of_le hdisc hmreq

/--
Uniform no-crossing beyond `Y*` obtained from the analytic package.
-/
theorem noCrossingBeyondYstar_of_analyticBounds
    (bounds : CaseBAnalyticBounds) :
    NoCrossingBeyondYstar := by
  intro y hy _hp
  exact noCrossingAt_of_analyticBounds bounds hy

/--
Uniform no-crossing constructor.
-/
theorem noCrossingBeyondYstar_of_assumption
    (h : ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → McNat y < mreq y) :
    NoCrossingBeyondYstar := by
  intro y hy hp
  exact h y hy hp

/--
Elimination form of the uniform no-crossing interface.
-/
theorem noCrossingAt_of_noCrossingBeyondYstar
    (h : NoCrossingBeyondYstar)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    McNat y < mreq y := by
  exact h y hy hp

/--
Convenient packaged form: once the analytic large-`y` comparison has been
discretized into the `McNat y < mreq y` inequality, the no-crossing interface
is ready for the final Case B contradiction layer.
-/
theorem noCrossing_ready_for_contradiction
    (h : NoCrossingBeyondYstar)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt y := by
  exact h y hy hp

end CaseB
end Lehmer