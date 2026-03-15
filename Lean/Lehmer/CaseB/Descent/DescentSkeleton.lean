-- FILE: Lean/Lehmer/CaseB/Descent/DescentSkeleton.lean
import Lehmer.Prelude
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB

namespace Lehmer
namespace CaseB

/--
A context admits a one-step descent if there exists a removable element
producing a controlled-removal successor.
-/
def HasDescentStep (C : Context) : Prop :=
  ∃ p : ℕ, Removable C.S p

/--
A bounded descent claim for a Case B context.

For MVP-2 this is expressed only as the existence of the abstract
`KmaxB` bound attached to the level `y`.
-/
def HasBoundedDescent (C : Context) : Prop :=
  contextDescentLength C ≤ KmaxB C.y

@[simp] theorem HasDescentStep_def (C : Context) :
    HasDescentStep C = ∃ p : ℕ, Removable C.S p := rfl

@[simp] theorem HasBoundedDescent_def (C : Context) :
    HasBoundedDescent C = (contextDescentLength C ≤ KmaxB C.y) := rfl

/--
If a context is descent-eligible, then it has a removable element.
-/
theorem exists_removable_of_descentEligible (C : Context)
    (hC : ContextDescentEligible C) :
    ∃ p : ℕ, Removable C.S p := by
  rcases hC with ⟨_, hne⟩
  rcases hne with ⟨p, hp⟩
  exact ⟨p, hp⟩

/--
A descent-eligible context admits a canonical one-step descent.
-/
theorem hasDescentStep_of_descentEligible (C : Context)
    (hC : ContextDescentEligible C) :
    HasDescentStep C := by
  simpa [HasDescentStep] using exists_removable_of_descentEligible C hC

/--
A descent-eligible context admits a canonical successor with strict
decrease of the Case B potential.
-/
theorem exists_strictly_decreasing_successor_of_descentEligible
    (C : Context) (hC : ContextDescentEligible C) :
    ∃ p : ℕ, ∃ C' : Context,
      ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  rcases exists_removable_of_descentEligible C hC with ⟨p, hp⟩
  refine ⟨p, nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hp,
    potential_strict_decrease_of_removable C p hp⟩

/--
A descent-eligible context admits a canonical successor with strict
decrease of the discrete descent-length proxy.
-/
theorem exists_length_decreasing_successor_of_descentEligible
    (C : Context) (hC : ContextDescentEligible C) :
    ∃ p : ℕ, ∃ C' : Context,
      ContextControlledRemoval C p C' ∧
      contextDescentLength C' < contextDescentLength C := by
  rcases exists_removable_of_descentEligible C hC with ⟨p, hp⟩
  refine ⟨p, nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hp,
    contextDescentLength_strict_decrease_of_removable C p hp⟩

/--
Every context carries the abstract bounded-descent interface of MVP-2.
-/
theorem hasBoundedDescent_of_context (C : Context) :
    HasBoundedDescent C := by
  simpa [HasBoundedDescent] using exists_descent_bound_placeholder C

/--
Main MVP-2 skeleton statement:
non-saturated and nonempty supports admit a descent step, and the descent
is controlled by strict decrease together with an abstract bound.
-/
theorem descent_skeleton (C : Context)
    (hC : ContextDescentEligible C) :
    HasDescentStep C ∧ HasBoundedDescent C := by
  exact ⟨hasDescentStep_of_descentEligible C hC,
    hasBoundedDescent_of_context C⟩

/--
Expanded form of the descent skeleton with an explicit canonical successor.
-/
theorem descent_skeleton_explicit (C : Context)
    (hC : ContextDescentEligible C) :
    ∃ p : ℕ, ∃ C' : Context,
      ContextControlledRemoval C p C' ∧
      potential C' < potential C ∧
      contextDescentLength C' < contextDescentLength C ∧
      HasBoundedDescent C := by
  rcases exists_removable_of_descentEligible C hC with ⟨p, hp⟩
  refine ⟨p, nextContext C p, ?_⟩
  refine ⟨contextControlledRemoval_canonical C p hp, ?_, ?_, ?_⟩
  · exact potential_strict_decrease_of_removable C p hp
  · exact contextDescentLength_strict_decrease_of_removable C p hp
  · exact hasBoundedDescent_of_context C

end CaseB
end Lehmer