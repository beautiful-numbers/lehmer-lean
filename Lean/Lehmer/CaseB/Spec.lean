-- FILE: Lean/Lehmer/CaseB/Spec.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Support.PotentialP
import Lehmer.Support.PotentialP2

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Support

/--
Case B paper threshold parameter `ε_B = 2/5`.
-/
noncomputable def epsilonB (_ : ℕ) : ℝ :=
  (2 : ℝ) / 5

@[simp] theorem epsilonB_def (y : ℕ) :
    epsilonB y = (2 : ℝ) / 5 := rfl

/--
A support `S` is viewed at Case B level `y`.
-/
structure Context where
  y : ℕ
  S : Finset ℕ

/-- Paper-style access to the support component. -/
abbrev support (C : Context) : Finset ℕ :=
  C.S

/-- Paper-style access to the level component. -/
abbrev level (C : Context) : ℕ :=
  C.y

@[simp] theorem support_mk (y : ℕ) (S : Finset ℕ) :
    support ⟨y, S⟩ = S := rfl

@[simp] theorem level_mk (y : ℕ) (S : Finset ℕ) :
    level ⟨y, S⟩ = y := rfl

/--
Paper Case B decrement parameter.

This is the local spec-level copy of the paper quantity
`δ_B(y) = 1 / (3 (log (max y 3))^4)`.
It is intentionally defined here so that the main Case B potential can be
paper-calibrated directly at the spec layer without creating an import cycle
through `CaseB.Parameters`.
-/
noncomputable def paperDelta (y : ℕ) : ℝ :=
  1 / (3 * (Real.log ((max y 3 : ℕ)))^4)

@[simp] theorem paperDelta_def (y : ℕ) :
    paperDelta y = 1 / (3 * (Real.log ((max y 3 : ℕ)))^4) := rfl

/--
Paper-calibrated discrete Case B potential attached to a context.

This is now the principal Case B potential used by the local constructive
strategy.
-/
noncomputable def paperPotential (C : Context) : ℕ :=
  potentialP2 (epsilonB C.y) (paperDelta C.y) C.S

@[simp] theorem paperPotential_def (C : Context) :
    paperPotential C = potentialP2 (epsilonB C.y) (paperDelta C.y) C.S := rfl

/--
Legacy/local discrete Case B potential, retained explicitly under its own name
for compatibility with older local plumbing when needed.
-/
noncomputable def legacyPotential (C : Context) : ℕ :=
  potentialP2 (epsilonB C.y) 0.01 C.S

@[simp] theorem legacyPotential_def (C : Context) :
    legacyPotential C = potentialP2 (epsilonB C.y) 0.01 C.S := rfl

/--
The principal Case B potential.

This is intentionally the paper-calibrated potential.
-/
noncomputable def potential (C : Context) : ℕ :=
  paperPotential C

@[simp] theorem potential_def (C : Context) :
    potential C = paperPotential C := rfl

@[simp] theorem potential_spec (C : Context) :
    potential C = potentialP2 (epsilonB C.y) (paperDelta C.y) C.S := by
  rfl

/--
A minimal abstract threshold for Case B.
-/
noncomputable def threshold (y : ℕ) : ℝ :=
  epsilonB y

@[simp] theorem threshold_def (y : ℕ) :
    threshold y = epsilonB y := rfl

/--
A support is non-saturated at level `y` if its support potential lies below
the abstract threshold.
-/
noncomputable def NonSaturated (S : Finset ℕ) (y : ℕ) : Prop :=
  supportPotential S ≤ 1 - threshold y

/-- Context version of non-saturation. -/
noncomputable def ContextNonSaturated (C : Context) : Prop :=
  NonSaturated C.S C.y

@[simp] theorem NonSaturated_def (S : Finset ℕ) (y : ℕ) :
    NonSaturated S y = (supportPotential S ≤ 1 - threshold y) := rfl

@[simp] theorem ContextNonSaturated_def (C : Context) :
    ContextNonSaturated C = NonSaturated C.S C.y := rfl

/-- Saturation is the negation of non-saturation. -/
noncomputable def Saturated (S : Finset ℕ) (y : ℕ) : Prop :=
  ¬ NonSaturated S y

/-- Context version of saturation. -/
noncomputable def ContextSaturated (C : Context) : Prop :=
  Saturated C.S C.y

@[simp] theorem Saturated_def (S : Finset ℕ) (y : ℕ) :
    Saturated S y = ¬ NonSaturated S y := rfl

@[simp] theorem ContextSaturated_def (C : Context) :
    ContextSaturated C = Saturated C.S C.y := rfl

/--
A support is descent-eligible at level `y` when it is non-saturated and
nonempty.
-/
noncomputable def DescentEligible (S : Finset ℕ) (y : ℕ) : Prop :=
  NonSaturated S y ∧ S.Nonempty

/-- Context version of descent eligibility. -/
noncomputable def ContextDescentEligible (C : Context) : Prop :=
  DescentEligible C.S C.y

@[simp] theorem DescentEligible_def (S : Finset ℕ) (y : ℕ) :
    DescentEligible S y = (NonSaturated S y ∧ S.Nonempty) := rfl

@[simp] theorem ContextDescentEligible_def (C : Context) :
    ContextDescentEligible C = DescentEligible C.S C.y := rfl

/-- The support cardinality at Case B level. -/
def omegaB (S : Finset ℕ) : ℕ :=
  supportCard S

@[simp] theorem omegaB_def (S : Finset ℕ) :
    omegaB S = supportCard S := rfl

/--
Minimal explicit bridge seed between the local constructive Case B strategy and
the terminal/global strategy.

The local side naturally produces data at a fixed level together with a support
bound; the global side consumes terminal structured data of the same shape.
This seed makes that interface explicit already at the spec layer.
-/
structure CaseBStrategyBridgeSeed (C : Context) where
  y0 : ℕ
  omega0 : ℕ
  hy : y0 = C.y
  homega : omega0 = supportCard C.S

/--
Canonical bridge seed attached to a context.
-/
def caseBStrategyBridgeSeed_of_context (C : Context) :
    CaseBStrategyBridgeSeed C :=
  { y0 := C.y
    omega0 := supportCard C.S
    hy := rfl
    homega := rfl }

@[simp] theorem caseBStrategyBridgeSeed_of_context_y
    (C : Context) :
    (caseBStrategyBridgeSeed_of_context C).y0 = C.y := rfl

@[simp] theorem caseBStrategyBridgeSeed_of_context_omega
    (C : Context) :
    (caseBStrategyBridgeSeed_of_context C).omega0 = supportCard C.S := rfl

@[simp] theorem caseBStrategyBridgeSeed_of_context_hy
    (C : Context) :
    (caseBStrategyBridgeSeed_of_context C).hy = rfl := rfl

@[simp] theorem caseBStrategyBridgeSeed_of_context_homega
    (C : Context) :
    (caseBStrategyBridgeSeed_of_context C).homega = rfl := rfl

end CaseB
end Lehmer