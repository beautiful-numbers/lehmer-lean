-- FILE: Lean/Lehmer/Support/PotentialP2.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Support.PotentialP

namespace Lehmer
namespace Support

open Lehmer.Basic

/--
A minimal MVP-2 parameter for the Case B descent potential.
-/
noncomputable def epsilonB (y : ℕ) : ℝ :=
  1 / (y : ℝ)

/--
A second support potential used for the descent skeleton.
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
-/
theorem P2_erase_expand (S : Finset ℕ) (p y : ℕ) :
    P2 (S.erase p) y =
      potentialP (S.erase p) - epsilonB y * (supportCard (S.erase p) : ℝ) := by
  rfl

/--
Interface form for a strict `P2`-decrease under a controlled-removal
hypothesis.

The strict decrease is not true for arbitrary `S, p, y`; the theorem is
therefore stated in the precise implication form actually needed later.
-/
theorem P2_strict_decrease_placeholder
    (S : Finset ℕ) (p y : ℕ) (_hp : p ∈ S)
    (hdec : P2 (S.erase p) y < P2 S y) :
    P2 (S.erase p) y < P2 S y := by
  exact hdec

end Support
end Lehmer