-- FILE: Lean/Lehmer/CaseB/Descent/P2Decrease.lean
import Lehmer.Prelude
import Lehmer.Support.PotentialP2
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain

namespace Lehmer
namespace CaseB

open Lehmer.Support

/--
The central MVP-2 descent statement:
under a removable controlled removal and a gain hypothesis,
the second potential `P2` strictly decreases.
-/
theorem P2_strict_decrease_of_removable
    (S : Finset ℕ) (p y : ℕ) (hp : Removable S p)
    (hgain : HasGain S p y) :
    P2 (remove S p) y < P2 S y := by
  exact hasGain_of_removable S p y hp hgain

/--
Context-level form of strict decrease for the Case B potential.
-/
theorem potential_strict_decrease_of_removable
    (C : Context) (p : ℕ) (hp : Removable C.S p)
    (hgain : ContextHasGain C p) :
    potential (nextContext C p) < potential C := by
  exact contextHasGain_of_removable C p hp hgain

/--
A controlled removal step carries strict decrease of `P2`,
provided the gain hypothesis is available.
-/
theorem P2_strict_decrease_of_controlledRemoval
    (S T : Finset ℕ) (p y : ℕ)
    (hstep : ControlledRemoval S p T)
    (hgain : HasGain S p y) :
    P2 T y < P2 S y := by
  rcases hstep with ⟨hp, rfl⟩
  exact P2_strict_decrease_of_removable S p y hp hgain

/--
Context-level version of strict decrease under a controlled-removal step.
-/
theorem potential_strict_decrease_of_contextControlledRemoval
    (C C' : Context) (p : ℕ)
    (hstep : ContextControlledRemoval C p C')
    (hgain : ContextHasGain C p) :
    potential C' < potential C := by
  rcases hstep with ⟨hp, rfl⟩
  exact potential_strict_decrease_of_removable C p hp hgain

/--
The gain predicate is equivalent to strict decrease of `P2`.
-/
theorem hasGain_iff_P2_strict_decrease
    (S : Finset ℕ) (p y : ℕ) :
    HasGain S p y ↔ P2 (remove S p) y < P2 S y := by
  rfl

/--
Context-level gain is equivalent to strict decrease of the Case B potential.
-/
theorem contextHasGain_iff_potential_strict_decrease
    (C : Context) (p : ℕ) :
    ContextHasGain C p ↔ potential (nextContext C p) < potential C := by
  rfl

/--
Every removable element determines a canonical strictly-decreasing successor,
provided the gain hypothesis is available.
-/
theorem exists_strictly_decreasing_successor_of_removable
    (C : Context) {p : ℕ} (hp : Removable C.S p)
    (hgain : ContextHasGain C p) :
    ∃ C', ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  refine ⟨nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hp,
    potential_strict_decrease_of_removable C p hp hgain⟩

end CaseB
end Lehmer