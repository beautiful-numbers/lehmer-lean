-- FILE: Lean/Lehmer/CaseB/Parameters.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Spec : struct spec def
-/

import Lehmer.Prelude
import Lehmer.CaseB.Spec

namespace Lehmer
namespace CaseB

/--
Real-valued Case B level.

We use `max y 3` so that the parameter formulas remain total and are aligned
with the paper regime where Case B only starts in the large-pivot range
(`3 ≤ y` in particular).
-/
noncomputable def yB (y : ℕ) : ℝ :=
  (max y 3 : ℕ)

@[simp] theorem yB_def (y : ℕ) :
    yB y = (max y 3 : ℕ) := rfl

/--
Paper Case B slack parameter:
`ε_B = 2/5`.
-/
noncomputable def epsilonB_paper (_y : ℕ) : ℝ :=
  (2 : ℝ) / 5

@[simp] theorem epsilonB_paper_def (y : ℕ) :
    epsilonB_paper y = (2 : ℝ) / 5 := rfl

/--
Paper Case B decrement parameter:
`δ_B(y) = 1 / (3 (log y)^4)`.
-/
noncomputable def deltaB (y : ℕ) : ℝ :=
  1 / (3 * (Real.log (yB y))^4)

@[simp] theorem deltaB_def (y : ℕ) :
    deltaB y = 1 / (3 * (Real.log (yB y))^4) := rfl

/--
Paper auxiliary exponent for the Case B height function:
`2/5 - 1/(3 (log y)^4) = ε_B - δ_B(y)`.
-/
noncomputable def exponentB (y : ℕ) : ℝ :=
  epsilonB_paper y - deltaB y

@[simp] theorem exponentB_def (y : ℕ) :
    exponentB y = epsilonB_paper y - deltaB y := rfl

/--
Paper Case B height function:
`h(y) = y^(2/5 - 1/(3 (log y)^4))`.
-/
noncomputable def hB (y : ℕ) : ℝ :=
  (yB y) ^ (exponentB y)

@[simp] theorem hB_def (y : ℕ) :
    hB y = (yB y) ^ (exponentB y) := rfl

/--
Paper Case B descent budget:
`Kmax,B(y) = ⌈1 / δ_B(y)⌉ = ⌈3 (log y)^4⌉`.

We keep the `Nat.ceil (1 / δ_B(y))` presentation because it matches the proof
logic directly.
-/
noncomputable def kappaB (y : ℕ) : ℕ :=
  Nat.ceil (1 / deltaB y)

@[simp] theorem kappaB_def (y : ℕ) :
    kappaB y = Nat.ceil (1 / deltaB y) := rfl

/--
A minimal abstract slack parameter for Case B.

At the paper level this is the same constant `ε_B = 2/5`. We expose it
through `sigmaB` so that the downstream descent layer can consume a stable
parameter interface.
-/
noncomputable def sigmaB (y : ℕ) : ℝ :=
  epsilonB_paper y

@[simp] theorem sigmaB_def (y : ℕ) :
    sigmaB y = epsilonB_paper y := rfl

/--
Expanded closed form of the descent budget:
`Kmax,B(y) = ⌈3 (log y)^4⌉`.
-/
theorem kappaB_eq_ceil_three_log_four (y : ℕ) :
    kappaB y = Nat.ceil (3 * (Real.log (yB y))^4) := by
  simp [kappaB, deltaB]

/--
The descent budget is nonnegative.
-/
theorem kappaB_nonneg (y : ℕ) :
    0 ≤ kappaB y := by
  exact Nat.zero_le _

/--
The slack parameter is the paper constant `2/5`.
-/
theorem sigmaB_eq_epsilonB_paper (y : ℕ) :
    sigmaB y = (2 : ℝ) / 5 := by
  simp [sigmaB, epsilonB_paper]

/--
Parameters attached to a fixed Case B level.
-/
structure Parameters where
  y : ℕ

/--
The default parameter package at level `y`.
-/
def params (y : ℕ) : Parameters :=
  ⟨y⟩

/--
Read the descent budget from a parameter package.
-/
noncomputable def paramsKappa (P : Parameters) : ℕ :=
  kappaB P.y

/--
Read the slack parameter from a parameter package.
-/
noncomputable def paramsSigma (P : Parameters) : ℝ :=
  sigmaB P.y

/--
Read the decrement parameter from a parameter package.
-/
noncomputable def paramsDelta (P : Parameters) : ℝ :=
  deltaB P.y

/--
Read the height function from a parameter package.
-/
noncomputable def paramsH (P : Parameters) : ℝ :=
  hB P.y

@[simp] theorem params_y (y : ℕ) :
    (params y).y = y := rfl

@[simp] theorem paramsKappa_def (P : Parameters) :
    paramsKappa P = kappaB P.y := rfl

@[simp] theorem paramsSigma_def (P : Parameters) :
    paramsSigma P = sigmaB P.y := rfl

@[simp] theorem paramsDelta_def (P : Parameters) :
    paramsDelta P = deltaB P.y := rfl

@[simp] theorem paramsH_def (P : Parameters) :
    paramsH P = hB P.y := rfl

@[simp] theorem paramsKappa_params (y : ℕ) :
    paramsKappa (params y) = kappaB y := rfl

@[simp] theorem paramsSigma_params (y : ℕ) :
    paramsSigma (params y) = sigmaB y := rfl

@[simp] theorem paramsDelta_params (y : ℕ) :
    paramsDelta (params y) = deltaB y := rfl

@[simp] theorem paramsH_params (y : ℕ) :
    paramsH (params y) = hB y := rfl

end CaseB
end Lehmer