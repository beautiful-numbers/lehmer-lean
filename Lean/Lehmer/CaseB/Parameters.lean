-- FILE: Lean/Lehmer/CaseB/Parameters.lean
import Lehmer.Prelude
import Lehmer.CaseB.Spec

namespace Lehmer
namespace CaseB

/--
The abstract descent budget attached to the Case B level `y`.

For MVP-2 this is kept intentionally simple and coincides with the level.
It serves only as a stable placeholder parameter for later refinements.
-/
def kappaB (y : ℕ) : ℕ :=
  y

/--
A minimal abstract slack parameter for Case B.

At MVP-2 this is just the threshold already introduced in `Spec`.
-/
noncomputable def sigmaB (y : ℕ) : ℝ :=
  threshold y

@[simp] theorem kappaB_def (y : ℕ) :
    kappaB y = y := rfl

@[simp] theorem sigmaB_def (y : ℕ) :
    sigmaB y = threshold y := rfl

/--
The descent budget is nonnegative.
-/
theorem kappaB_nonneg (y : ℕ) :
    0 ≤ kappaB y := by
  simp [kappaB]

/--
The slack parameter is definitionally the Case B threshold.
-/
theorem sigmaB_eq_threshold (y : ℕ) :
    sigmaB y = threshold y := rfl

/--
Parameters attached to a fixed Case B level.
-/
structure Parameters where
  y : ℕ

/--
The default abstract parameter package at level `y`.
-/
def params (y : ℕ) : Parameters :=
  ⟨y⟩

/--
Read the descent budget from a parameter package.
-/
def paramsKappa (P : Parameters) : ℕ :=
  kappaB P.y

/--
Read the slack parameter from a parameter package.
-/
noncomputable def paramsSigma (P : Parameters) : ℝ :=
  sigmaB P.y

@[simp] theorem params_y (y : ℕ) :
    (params y).y = y := rfl

@[simp] theorem paramsKappa_def (P : Parameters) :
    paramsKappa P = kappaB P.y := rfl

@[simp] theorem paramsSigma_def (P : Parameters) :
    paramsSigma P = sigmaB P.y := rfl

@[simp] theorem paramsKappa_params (y : ℕ) :
    paramsKappa (params y) = kappaB y := rfl

@[simp] theorem paramsSigma_params (y : ℕ) :
    paramsSigma (params y) = sigmaB y := rfl

end CaseB
end Lehmer