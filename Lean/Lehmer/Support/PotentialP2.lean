-- FILE: Lean/Lehmer/Support/PotentialP2.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Support.PotentialP

namespace Lehmer
namespace Support

open Lehmer.Basic

/--
A minimal MVP-2 parameter for the Case B descent potential.

At this stage we keep the weight abstract and attach it only to the
roughness level `y`.
-/
noncomputable def epsilonB (y : ℕ) : ℝ :=
  1 / (y : ℝ)

/--
A second support potential used for the descent skeleton.

For MVP-2 we define it as a weighted version of `P(S)`, with an abstract
`y`-dependent correction term using only the support cardinality.
This is enough to stabilize the interface for the descent files without
committing yet to the final analytic formula.
-/
noncomputable def potentialP2 (S : Finset ℕ) (y : ℕ) : ℝ :=
  potentialP S - epsilonB y * (supportCard S : ℝ)

/--
Paper-style alias for the second potential.
-/
noncomputable abbrev P2 (S : Finset ℕ) (y : ℕ) : ℝ :=
  potentialP2 S y

@[simp] theorem epsilonB_def (y : ℕ) :
    epsilonB y = 1 / (y : ℝ) := rfl

@[simp] theorem potentialP2_def (S : Finset ℕ) (y : ℕ) :
    potentialP2 S y = potentialP S - epsilonB y * (supportCard S : ℝ) := rfl

@[simp] theorem P2_def (S : Finset ℕ) (y : ℕ) :
    P2 S y = potentialP S - epsilonB y * (supportCard S : ℝ) := rfl

@[simp] theorem P2_eq_potentialP2 (S : Finset ℕ) (y : ℕ) :
    P2 S y = potentialP2 S y := rfl

/--
Expanded form of `P2` in terms of the raw support quantities.
-/
theorem P2_expand (S : Finset ℕ) (y : ℕ) :
    P2 S y =
      Real.log (supportLcm S) / Real.log (supportProd S)
        - epsilonB y * (supportCard S : ℝ) := by
  rfl

/--
For fixed `y`, `P2` differs from `P` by the cardinality correction term.
-/
theorem P2_eq_P_sub_card_term (S : Finset ℕ) (y : ℕ) :
    P2 S y = P S - epsilonB y * (supportCard S : ℝ) := by
  rfl

/--
The empty-support value of `P2` is given by direct expansion.
-/
@[simp] theorem P2_empty (y : ℕ) :
    P2 ∅ y = potentialP ∅ - epsilonB y * (supportCard (∅ : Finset ℕ) : ℝ) := by
  rfl

/--
Removing an element from the support changes `P2` by the corresponding
difference of `P` plus the cardinality correction term.

This is the basic algebraic rewrite used later in the descent layer.
-/
theorem P2_erase_expand (S : Finset ℕ) (p y : ℕ) :
    P2 (S.erase p) y =
      potentialP (S.erase p) - epsilonB y * (supportCard (S.erase p) : ℝ) := by
  rfl

/--
Stable MVP-2 placeholder: a controlled removal should strictly decrease `P2`.

The exact descent hypotheses are introduced later in `CaseB`, but the target
shape of the conclusion is fixed here as an interface.
-/
theorem P2_strict_decrease_placeholder
    (S : Finset ℕ) (p y : ℕ) (hp : p ∈ S) :
    P2 (S.erase p) y < P2 S y := by
  sorry

end Support
end Lehmer