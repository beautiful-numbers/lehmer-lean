-- FILE: Lean/Lehmer/CaseB/Spec.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Support.PotentialP2

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Support

/--
A support `S` is viewed at Case B level `y`.
For MVP-2 this is just a lightweight pairing of the support and the level.
-/
structure Context where
  y : ℕ
  S : Finset ℕ

/--
Paper-style access to the support component.
-/
abbrev support (C : Context) : Finset ℕ :=
  C.S

/--
Paper-style access to the level component.
-/
abbrev level (C : Context) : ℕ :=
  C.y

@[simp] theorem support_mk (y : ℕ) (S : Finset ℕ) :
    support ⟨y, S⟩ = S := rfl

@[simp] theorem level_mk (y : ℕ) (S : Finset ℕ) :
    level ⟨y, S⟩ = y := rfl

/--
The Case B potential attached to a context.
-/
noncomputable def potential (C : Context) : ℝ :=
  P2 C.S C.y

@[simp] theorem potential_def (C : Context) :
    potential C = P2 C.S C.y := rfl

/--
A minimal abstract threshold for Case B.
For MVP-2 we reuse `epsilonB`.
-/
noncomputable def threshold (y : ℕ) : ℝ :=
  epsilonB y

@[simp] theorem threshold_def (y : ℕ) :
    threshold y = epsilonB y := rfl

/--
A support is non-saturated at level `y` if its first potential lies below
the abstract threshold.
This is the minimal interface needed for the descent skeleton.
-/
noncomputable def NonSaturated (S : Finset ℕ) (y : ℕ) : Prop :=
  P S ≤ 1 - threshold y

/--
Context version of non-saturation.
-/
noncomputable def ContextNonSaturated (C : Context) : Prop :=
  NonSaturated C.S C.y

@[simp] theorem NonSaturated_def (S : Finset ℕ) (y : ℕ) :
    NonSaturated S y = (P S ≤ 1 - threshold y) := rfl

@[simp] theorem ContextNonSaturated_def (C : Context) :
    ContextNonSaturated C = NonSaturated C.S C.y := rfl

/--
A placeholder notion of saturation, defined as the negation of non-saturation.
-/
noncomputable def Saturated (S : Finset ℕ) (y : ℕ) : Prop :=
  ¬ NonSaturated S y

/--
Context version of saturation.
-/
noncomputable def ContextSaturated (C : Context) : Prop :=
  Saturated C.S C.y

@[simp] theorem Saturated_def (S : Finset ℕ) (y : ℕ) :
    Saturated S y = ¬ NonSaturated S y := rfl

@[simp] theorem ContextSaturated_def (C : Context) :
    ContextSaturated C = Saturated C.S C.y := rfl

/--
A minimal placeholder predicate expressing that a support is eligible for
Case B descent at level `y`.
-/
noncomputable def DescentEligible (S : Finset ℕ) (y : ℕ) : Prop :=
  NonSaturated S y ∧ S.Nonempty

/--
Context version of descent eligibility.
-/
noncomputable def ContextDescentEligible (C : Context) : Prop :=
  DescentEligible C.S C.y

@[simp] theorem DescentEligible_def (S : Finset ℕ) (y : ℕ) :
    DescentEligible S y = (NonSaturated S y ∧ S.Nonempty) := rfl

@[simp] theorem ContextDescentEligible_def (C : Context) :
    ContextDescentEligible C = DescentEligible C.S C.y := rfl

/--
The support cardinality at Case B level.
-/
def omegaB (S : Finset ℕ) : ℕ :=
  supportCard S

@[simp] theorem omegaB_def (S : Finset ℕ) :
    omegaB S = supportCard S := rfl

end CaseB
end Lehmer