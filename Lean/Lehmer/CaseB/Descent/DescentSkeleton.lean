-- FILE: Lean/Lehmer/CaseB/Descent/DescentSkeleton.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
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

At the current stage, bounded descent means that the canonical discrete
descent-length proxy is bounded by the paper budget `KmaxB C.y`.
-/
def HasBoundedDescent (C : Context) : Prop :=
  contextDescentLength C ≤ KmaxB C.y

/--
A context is `ε_B`-saturated when it is not non-saturated.
This is the terminal target of the Case B descent window.
-/
def EpsBSaturated (C : Context) : Prop :=
  ContextSaturated C

/--
A one-step progress package for the descent window.
-/
structure DescentStepData (C : Context) where
  p : ℕ
  C' : Context
  hstep : ContextControlledRemoval C p C'
  hP2dec : potential C' < potential C
  hLenDec : contextDescentLength C' < contextDescentLength C

/--
A finite descent chain starting from `C`, of length at most `k`,
ending at a saturated context.

This is the proof-layer object matching the paper's bounded descent window:
one iterates controlled removals until an `ε_B`-saturated support is reached.
-/
structure DescentWindow (C : Context) where
  k : ℕ
  hk : k ≤ KmaxB C.y
  terminal : Context
  hterminal_y : terminal.y = C.y
  hterminal_saturated : EpsBSaturated terminal
  hterminal_bound : contextDescentLength terminal ≤ contextDescentLength C

@[simp] theorem HasDescentStep_def (C : Context) :
    HasDescentStep C = ∃ p : ℕ, Removable C.S p := rfl

@[simp] theorem HasBoundedDescent_def (C : Context) :
    HasBoundedDescent C = (contextDescentLength C ≤ KmaxB C.y) := rfl

@[simp] theorem EpsBSaturated_def (C : Context) :
    EpsBSaturated C = ContextSaturated C := rfl

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
  exact exists_removable_of_descentEligible C hC

/--
A descent-eligible context admits a canonical successor with strict
decrease of the Case B potential, provided every removable element satisfies
the paper-style gain criterion.
-/
theorem exists_strictly_decreasing_successor_of_descentEligible
    (C : Context) (hC : ContextDescentEligible C)
    (hgain : ∀ p, Removable C.S p → ContextGainCriterion C p) :
    ∃ p : ℕ, ∃ C' : Context,
      ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  rcases exists_removable_of_descentEligible C hC with ⟨p, hp⟩
  refine ⟨p, nextContext C p, ?_⟩
  refine ⟨contextControlledRemoval_canonical C p hp, ?_⟩
  exact potential_strict_decrease_of_removable C p hp (hgain p hp)

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
  refine ⟨contextControlledRemoval_canonical C p hp, ?_⟩
  exact contextDescentLength_strict_decrease_of_removable C p hp

/--
Any explicit cardinality bound yields the bounded-descent interface.
-/
theorem hasBoundedDescent_of_bound (C : Context)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    HasBoundedDescent C := by
  exact exists_descent_bound_of_assumption C hbound

/--
The descent-length bound is the pipeline-facing form of the paper budget.
-/
theorem descentLength_bounded_by_KmaxB_of_bound (C : Context)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    contextDescentLength C ≤ KmaxB C.y := by
  exact hasBoundedDescent_of_bound C hbound

/--
One-step descent data extracted from a descent-eligible context, provided every
removable element satisfies the paper-style gain criterion.
-/
theorem descentStepData_of_descentEligible
    (C : Context) (hC : ContextDescentEligible C)
    (hgain : ∀ p, Removable C.S p → ContextGainCriterion C p) :
    ∃ _D : DescentStepData C, True := by
  rcases exists_removable_of_descentEligible C hC with ⟨p, hp⟩
  refine ⟨{ p := p
          , C' := nextContext C p
          , hstep := contextControlledRemoval_canonical C p hp
          , hP2dec := potential_strict_decrease_of_removable C p hp (hgain p hp)
          , hLenDec := contextDescentLength_strict_decrease_of_removable C p hp }, trivial⟩

/--
Main one-step skeleton statement:
non-saturated and nonempty supports admit a descent step.
-/
theorem descent_skeleton (C : Context)
    (hC : ContextDescentEligible C) :
    HasDescentStep C := by
  exact hasDescentStep_of_descentEligible C hC

/--
Expanded one-step skeleton:
a descent-eligible context admits a controlled-removal successor with strict
decrease both of the potential and of the discrete descent length, provided
every removable element satisfies the paper-style gain criterion.
-/
theorem descent_skeleton_explicit (C : Context)
    (hC : ContextDescentEligible C)
    (hgain : ∀ p, Removable C.S p → ContextGainCriterion C p)
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

/--
Window-level formulation of the current Case B descent skeleton.

If the starting context is already saturated, the descent window has length `0`.
This is the terminal side of the paper descent dichotomy.
-/
def descent_window_of_saturated
    (C : Context)
    (hC : EpsBSaturated C)
    (_hbound : supportCard C.S ≤ KmaxB C.y) :
    DescentWindow C :=
  { k := 0
    hk := by
      have hK : 0 ≤ KmaxB C.y := KmaxB_nonneg C.y
      exact hK
    terminal := C
    hterminal_y := rfl
    hterminal_saturated := hC
    hterminal_bound := by
      exact le_rfl }

/--
Window-level entry theorem for the descent regime.

At the current stage, the proof layer isolates the exact two ingredients needed
for the paper descent window:
- either the current context is already `ε_B`-saturated;
- or it lies in the non-saturated regime and satisfies the explicit paper
  budget bound.

This is the stable interface needed before passing to the saturation and
supply-bound layers.
-/
theorem descent_window_interface
    (C : Context)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    EpsBSaturated C ∨
      (ContextNonSaturated C ∧ HasBoundedDescent C) := by
  by_cases hs : EpsBSaturated C
  · exact Or.inl hs
  · have hns : ContextNonSaturated C := by
      simp [ContextNonSaturated, EpsBSaturated] at hs ⊢
      exact hs
    exact Or.inr ⟨hns, hasBoundedDescent_of_bound C hbound⟩

/--
If the context lies in the descent regime and every removable element satisfies
the paper-style gain criterion, then there is a one-step strictly decreasing
successor together with the explicit paper budget bound.
-/
theorem descent_window_step
    (C : Context)
    (hC : ContextDescentEligible C)
    (hgain : ∀ p, Removable C.S p → ContextGainCriterion C p)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    ∃ p : ℕ, ∃ C' : Context,
      ContextControlledRemoval C p C' ∧
      potential C' < potential C ∧
      contextDescentLength C' < contextDescentLength C ∧
      HasBoundedDescent C := by
  exact descent_skeleton_explicit C hC hgain hbound

end CaseB
end Lehmer