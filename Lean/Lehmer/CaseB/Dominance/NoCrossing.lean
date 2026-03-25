-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossing.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Parameters : def
- Lehmer.CaseB.Dominance.MajorantMc : def thm
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pivot.UBm : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Dominance.MajorantMc
import Lehmer.Pivot.Mreq
import Lehmer.Pivot.UBm

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot

/--
Paper constant `C1 = 10^{-3}` used in the large-`y` Case B dominance step.
-/
noncomputable def C1 : ℝ :=
  (1 : ℝ) / 1000

@[simp] theorem C1_def :
    C1 = (1 : ℝ) / 1000 := rfl

/--
Paper pivot threshold `Y0 = 30000`.
-/
def Y0 : ℕ :=
  30000

@[simp] theorem Y0_def :
    Y0 = 30000 := rfl

/--
Paper real threshold
`T_B = max(17, e^6, 10/C1, Y0)`.

We keep it as a real quantity because it is introduced analytically in the
paper before passing to the prime threshold `Y*`.
-/
noncomputable def TB : ℝ :=
  max 17 (max (Real.exp 6) (max (10 / C1) Y0))

@[simp] theorem TB_def :
    TB = max 17 (max (Real.exp 6) (max (10 / C1) Y0)) := rfl

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
theorem TB_le_Ystar : TB ≤ Ystar := by
  have hceil : TB ≤ (Nat.ceil TB : ℝ) := by
    exact Nat.le_ceil TB
  have hnext : (Nat.ceil TB : ℝ) ≤ Ystar := by
    exact_mod_cast nextPrimeGe_ge (Nat.ceil TB)
  exact le_trans hceil hnext

/--
`Y*` is prime.
-/
theorem Ystar_prime :
    Nat.Prime Ystar := by
  simpa [Ystar] using nextPrimeGe_prime (Nat.ceil TB)

/--
Large-`y` analytic dominance target from the paper:
`Mc(t) < C1 * t^2 / log t`.
-/
def UniformDominanceAt (t : ℝ) : Prop :=
  McNat (Nat.floor t) < Nat.ceil (C1 * t^2 / Real.log t)

@[simp] theorem UniformDominanceAt_def (t : ℝ) :
    UniformDominanceAt t =
      (McNat (Nat.floor t) < Nat.ceil (C1 * t^2 / Real.log t)) := rfl

/--
Discrete large-`y` dominance target specialized to prime pivots.
-/
def UniformDominanceAtNat (y : ℕ) : Prop :=
  ((Mc y) < C1 * (y : ℝ)^2 / Real.log y)

@[simp] theorem UniformDominanceAtNat_def (y : ℕ) :
    UniformDominanceAtNat y =
      ((Mc y) < C1 * (y : ℝ)^2 / Real.log y) := rfl

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
Interface constructor for large-`y` dominance at a prime pivot.
-/
theorem uniformDominanceAtNat_of_assumption
    {y : ℕ}
    (h : Mc y < C1 * (y : ℝ)^2 / Real.log y) :
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