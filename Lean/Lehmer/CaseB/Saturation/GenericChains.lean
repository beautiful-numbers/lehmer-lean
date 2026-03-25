-- FILE: Lean/Lehmer/CaseB/Saturation/GenericChains.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
-/

import Lehmer.Prelude
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.DescentSkeleton

namespace Lehmer
namespace CaseB

/--
A one-step generic descent datum.

This is the generic-side counterpart of the paper dichotomy:
a removable prime is treated as generic when it carries the generic gain
criterion and therefore yields a strict decrease of the Case B potential.
-/
structure GenericStepData (C : Context) where
  p : ℕ
  C' : Context
  hstep : ContextControlledRemoval C p C'
  hgeneric : ContextGenericGain C p
  hP2dec : potential C' < potential C
  hLenDec : contextDescentLength C' < contextDescentLength C

/--
Inductive generic chains.

A generic chain is a finite sequence of controlled removals in which every
removed prime satisfies the generic-side gain criterion.
-/
inductive GenericChain : Context → Context → Type where
  | nil (C : Context) : GenericChain C C
  | cons {C D : Context} (s : GenericStepData C) :
      GenericChain s.C' D → GenericChain C D

/--
Length of a generic chain.
-/
def genericChainLength {C D : Context} : GenericChain C D → ℕ
  | .nil _ => 0
  | .cons s Γ => genericChainLength Γ + 1

@[simp] theorem genericChainLength_nil (C : Context) :
    genericChainLength (GenericChain.nil C) = 0 := rfl

@[simp] theorem genericChainLength_cons {C D : Context}
    (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    genericChainLength (GenericChain.cons s Γ) = genericChainLength Γ + 1 := rfl

/--
A one-step generic chain from a generic removable prime.
-/
def singletonGenericChain {C : Context} (p : ℕ)
    (hp : Removable C.S p) (hgen : ContextGenericGain C p) :
    GenericChain C (nextContext C p) :=
  GenericChain.cons
    { p := p
      C' := nextContext C p
      hstep := contextControlledRemoval_canonical C p hp
      hgeneric := hgen
      hP2dec := potential_strict_decrease_of_genericGain C p hp hgen
      hLenDec := contextDescentLength_strict_decrease_of_removable C p hp }
    (GenericChain.nil (nextContext C p))

/--
The terminal context of a generic chain lies at the same Case B level as the
initial context.
-/
theorem GenericChain_preserves_level
    {C D : Context} (Γ : GenericChain C D) :
    D.y = C.y := by
  induction Γ with
  | nil C =>
      rfl
  | cons s Γ ih =>
      have hs : s.C'.y = C.y := ContextControlledRemoval_preserves_level s.hstep
      exact Eq.trans ih hs

/--
Every generic chain starts from its declared initial context.
-/
theorem GenericChain_refl_target (C : Context) :
    GenericChain C C := by
  exact GenericChain.nil C

/--
The head step of a nonempty generic chain strictly decreases the potential.
-/
theorem GenericChain_head_potential_decrease
    {C D : Context} (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    potential s.C' < potential C := by
  exact s.hP2dec

/--
The head step of a nonempty generic chain strictly decreases the discrete
descent-length proxy.
-/
theorem GenericChain_head_length_decrease
    {C D : Context} (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    contextDescentLength s.C' < contextDescentLength C := by
  exact s.hLenDec

/--
A generic chain is bounded by the Case B budget when its length is at most
`KmaxB` at the starting level.
-/
def GenericChainWithinBudget {C D : Context} (Γ : GenericChain C D) : Prop :=
  genericChainLength Γ ≤ KmaxB C.y

@[simp] theorem GenericChainWithinBudget_def {C D : Context} (Γ : GenericChain C D) :
    GenericChainWithinBudget Γ = (genericChainLength Γ ≤ KmaxB C.y) := rfl

/--
The empty generic chain is always within budget.
-/
theorem genericChainWithinBudget_nil (C : Context) :
    GenericChainWithinBudget (GenericChain.nil C) := by
  simp [GenericChainWithinBudget, KmaxB_nonneg]

/--
Package of a terminal generic chain ending at a saturated context.

This is the generic-side saturation interface that will be consumed later by
the witness-accounting / scarcity layer.
-/
structure GenericChainToSaturated (C : Context) where
  terminal : Context
  chain : GenericChain C terminal
  hbudget : GenericChainWithinBudget chain
  hsaturated : EpsBSaturated terminal

/--
If the starting context is already saturated, there is a trivial generic chain
to saturation of length `0`.
-/
def trivialGenericChainToSaturated (C : Context)
    (hC : EpsBSaturated C) :
    GenericChainToSaturated C where
  terminal := C
  chain := GenericChain.nil C
  hbudget := genericChainWithinBudget_nil C
  hsaturated := hC

/--
A generic one-step descent exists from a descent-eligible context provided
there is a removable prime satisfying the generic-side gain criterion.
-/
theorem exists_generic_step_of_descentEligible
    (C : Context) (hC : ContextDescentEligible C)
    (hgen : ∃ p : ℕ, Removable C.S p ∧ ContextGenericGain C p) :
    ∃ s : GenericStepData C, True := by
  rcases hgen with ⟨p, hp, hgp⟩
  refine ⟨{ p := p
          , C' := nextContext C p
          , hstep := contextControlledRemoval_canonical C p hp
          , hgeneric := hgp
          , hP2dec := potential_strict_decrease_of_genericGain C p hp hgp
          , hLenDec := contextDescentLength_strict_decrease_of_removable C p hp }, trivial⟩

end CaseB
end Lehmer