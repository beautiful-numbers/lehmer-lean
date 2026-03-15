-- FILE: Lean/Lehmer/CaseB/Descent/Gain.lean
import Lehmer.Prelude
import Lehmer.Support.PotentialP2
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval

namespace Lehmer
namespace CaseB

open Lehmer.Support

/--
A local gain predicate for a controlled removal step.

For MVP-2, "gain" means strict decrease of the second potential `P2`.
This keeps the descent interface simple and stable.
-/
def HasGain (S : Finset ℕ) (p y : ℕ) : Prop :=
  P2 (remove S p) y < P2 S y

/--
Context-level gain predicate.
-/
def ContextHasGain (C : Context) (p : ℕ) : Prop :=
  potential (nextContext C p) < potential C

@[simp] theorem HasGain_def (S : Finset ℕ) (p y : ℕ) :
    HasGain S p y = (P2 (remove S p) y < P2 S y) := rfl

@[simp] theorem ContextHasGain_def (C : Context) (p : ℕ) :
    ContextHasGain C p = (potential (nextContext C p) < potential C) := rfl

/--
Expanded form of context-level gain in terms of `P2`.
-/
theorem contextHasGain_iff_P2 (C : Context) (p : ℕ) :
    ContextHasGain C p ↔ P2 (remove C.S p) C.y < P2 C.S C.y := by
  rfl

/--
A controlled removal carries the placeholder gain coming from the support
potential interface.
-/
theorem hasGain_of_removable (S : Finset ℕ) (p y : ℕ)
    (hp : Removable S p) :
    HasGain S p y := by
  simpa [HasGain] using controlledRemoval_gain_placeholder S p y hp

/--
Context version of the previous gain statement.
-/
theorem contextHasGain_of_removable (C : Context) (p : ℕ)
    (hp : Removable C.S p) :
    ContextHasGain C p := by
  simpa [ContextHasGain, potential_def, nextContext, remove] using
    hasGain_of_removable C.S p C.y hp

/--
A canonical controlled removal step carries gain.
-/
theorem controlledRemoval_hasGain (S : Finset ℕ) (p y : ℕ)
    (hp : Removable S p) :
    ControlledRemoval S p (remove S p) ∧ HasGain S p y := by
  exact ⟨controlledRemoval_canonical S p hp, hasGain_of_removable S p y hp⟩

/--
Context-level canonical controlled removal together with gain.
-/
theorem contextControlledRemoval_hasGain (C : Context) (p : ℕ)
    (hp : Removable C.S p) :
    ContextControlledRemoval C p (nextContext C p) ∧ ContextHasGain C p := by
  exact ⟨contextControlledRemoval_canonical C p hp, contextHasGain_of_removable C p hp⟩

/--
Stable MVP-2 interface lemma: every removable element yields a gainful
successor context.
-/
theorem exists_gainful_successor_of_removable (C : Context)
    {p : ℕ} (hp : Removable C.S p) :
    ∃ C', ContextControlledRemoval C p C' ∧ ContextHasGain C p := by
  refine ⟨nextContext C p, ?_⟩
  exact contextControlledRemoval_hasGain C p hp

end CaseB
end Lehmer