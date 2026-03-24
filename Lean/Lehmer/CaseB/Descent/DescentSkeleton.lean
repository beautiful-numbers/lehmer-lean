-- FILE: Lean/Lehmer/CaseB/Descent/DescentSkeleton.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
A context admits a one-step descent if there exists a removable element
producing a controlled-removal successor.
-/
def HasDescentStep (C : Context) : Prop :=
  ∃ p : ℕ, Removable C.S p

/--
A bounded descent claim for a Case B context.

For MVP-2 this is now expressed conditionally: the abstract length proxy
is bounded once the support cardinality is known to be dominated by `KmaxB`.
-/
def HasBoundedDescent (C : Context) : Prop :=
  ∃ _hbound : supportCard C.S ≤ KmaxB C.y, contextDescentLength C ≤ KmaxB C.y

@[simp] theorem HasDescentStep_def (C : Context) :
    HasDescentStep C = ∃ p : ℕ, Removable C.S p := rfl

@[simp] theorem HasBoundedDescent_def (C : Context) :
    HasBoundedDescent C =
      ∃ _hbound : supportCard C.S ≤ KmaxB C.y, contextDescentLength C ≤ KmaxB C.y := rfl

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
decrease of the Case B potential, provided every removable element has gain.
-/
theorem exists_strictly_decreasing_successor_of_descentEligible
    (C : Context) (hC : ContextDescentEligible C)
    (hgain : ∀ p, Removable C.S p → ContextHasGain C p) :
    ∃ p : ℕ, ∃ C' : Context,
      ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  rcases exists_removable_of_descentEligible C hC with ⟨p, hp⟩
  refine ⟨p, nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hp,
    potential_strict_decrease_of_removable C p hp (hgain p hp)⟩

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
Any explicit cardinality bound yields the bounded-descent interface.
-/
theorem hasBoundedDescent_of_bound (C : Context)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    HasBoundedDescent C := by
  refine ⟨hbound, ?_⟩
  exact exists_descent_bound_of_assumption C hbound

/--
Main MVP-2 skeleton statement:
non-saturated and nonempty supports admit a descent step.
The bounded part is intentionally not asserted unconditionally at this stage.
-/
theorem descent_skeleton (C : Context)
    (hC : ContextDescentEligible C) :
    HasDescentStep C := by
  exact hasDescentStep_of_descentEligible C hC

/--
Expanded form of the descent skeleton with an explicit canonical successor,
provided every removable element has gain and an explicit cardinality bound
is supplied.
-/
theorem descent_skeleton_explicit (C : Context)
    (hC : ContextDescentEligible C)
    (hgain : ∀ p, Removable C.S p → ContextHasGain C p)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    ∃ p : ℕ, ∃ C' : Context,
      ContextControlledRemoval C p C' ∧
      potential C' < potential C ∧
      contextDescentLength C' < contextDescentLength C ∧
      HasBoundedDescent C := by
  rcases exists_removable_of_descentEligible C hC with ⟨p, hp⟩
  refine ⟨p, nextContext C p, ?_⟩
  refine ⟨contextControlledRemoval_canonical C p hp, ?_, ?_, ?_⟩
  · exact potential_strict_decrease_of_removable C p hp (hgain p hp)
  · exact contextDescentLength_strict_decrease_of_removable C p hp
  · exact hasBoundedDescent_of_bound C hbound

end CaseB
end Lehmer