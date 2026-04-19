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
Canonical conversion from a context-level generic gain to a generic step datum.
-/
def genericStepData_of_contextGenericGain
    (C : Context) {p : ℕ}
    (hgen : ContextGenericGain C p) :
    GenericStepData C :=
  { p := p
    C' := nextContext C p
    hstep := contextControlledRemoval_canonical C p hgen.1.1
    hgeneric := hgen
    hP2dec := potential_strict_decrease_of_genericGain C p hgen.1.1 hgen
    hLenDec := contextDescentLength_strict_decrease_of_removable C p hgen.1.1 }

@[simp] theorem genericStepData_of_contextGenericGain_p
    (C : Context) {p : ℕ}
    (hgen : ContextGenericGain C p) :
    (genericStepData_of_contextGenericGain C hgen).p = p := rfl

@[simp] theorem genericStepData_of_contextGenericGain_C'
    (C : Context) {p : ℕ}
    (hgen : ContextGenericGain C p) :
    (genericStepData_of_contextGenericGain C hgen).C' = nextContext C p := rfl

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
A nonempty generic chain, exposing the head step and tail separately.
-/
structure NonemptyGenericChain (C D : Context) where
  head : GenericStepData C
  tail : GenericChain head.C' D

def NonemptyGenericChain.toGenericChain
    {C D : Context}
    (Γ : NonemptyGenericChain C D) :
    GenericChain C D :=
  GenericChain.cons Γ.head Γ.tail

/--
Length of a generic chain.
-/
def genericChainLength {C D : Context} : GenericChain C D → ℕ
  | .nil _ => 0
  | .cons _ Γ => genericChainLength Γ + 1

@[simp] theorem genericChainLength_nil (C : Context) :
    genericChainLength (GenericChain.nil C) = 0 := rfl

@[simp] theorem genericChainLength_cons {C D : Context}
    (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    genericChainLength (GenericChain.cons s Γ) = genericChainLength Γ + 1 := rfl

theorem genericChainLength_pos_of_cons
    {C D : Context}
    (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    0 < genericChainLength (GenericChain.cons s Γ) := by
  simp [genericChainLength]

theorem genericChainLength_tail_le
    {C D : Context}
    (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    genericChainLength Γ ≤ genericChainLength (GenericChain.cons s Γ) := by
  simp [genericChainLength]

/--
A one-step generic chain from a generic removable prime.
-/
def singletonGenericChain {C : Context} (p : ℕ)
    (_hp : Removable C.S p) (hgen : ContextGenericGain C p) :
    GenericChain C (nextContext C p) :=
  GenericChain.cons
    (genericStepData_of_contextGenericGain C hgen)
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
  | @cons C D s Γ ih =>
      have hs : s.C'.y = C.y := by
        exact ContextControlledRemoval_preserves_level s.hstep
      exact Eq.trans ih hs

/--
Every generic chain starts from its declared initial context.
-/
def GenericChain_refl_target (C : Context) :
    GenericChain C C :=
  GenericChain.nil C

/--
The head step of a nonempty generic chain strictly decreases the potential.
-/
theorem GenericChain_head_potential_decrease
    {C D : Context} (s : GenericStepData C) (_Γ : GenericChain s.C' D) :
    potential s.C' < potential C := by
  exact s.hP2dec

/--
The head step of a nonempty generic chain strictly decreases the discrete
descent-length proxy.
-/
theorem GenericChain_head_length_decrease
    {C D : Context} (s : GenericStepData C) (_Γ : GenericChain s.C' D) :
    contextDescentLength s.C' < contextDescentLength C := by
  exact s.hLenDec

theorem GenericStepData_preserves_level
    {C : Context} (s : GenericStepData C) :
    s.C'.y = C.y := by
  exact ContextControlledRemoval_preserves_level s.hstep

theorem GenericChain_tail_preserves_level
    {C D : Context}
    (_s : GenericStepData C) (Γ : GenericChain _s.C' D) :
    D.y = _s.C'.y := by
  exact GenericChain_preserves_level Γ

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
  simp [GenericChainWithinBudget]

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
A context-level generic gain canonically yields a generic step datum.
-/
theorem exists_genericStepData_of_contextGenericGain
    (C : Context) {p : ℕ}
    (hgen : ContextGenericGain C p) :
    ∃ s : GenericStepData C, s.p = p := by
  exact ⟨genericStepData_of_contextGenericGain C hgen, rfl⟩

/--
A context-level generic gain canonically yields a singleton generic chain.
-/
theorem exists_singletonGenericChain_of_contextGenericGain
    (C : Context) {p : ℕ}
    (hgen : ContextGenericGain C p) :
    ∃ Γ : GenericChain C (nextContext C p), genericChainLength Γ = 1 := by
  refine ⟨singletonGenericChain p hgen.1.1 hgen, ?_⟩
  simp [singletonGenericChain, genericChainLength]

/--
Structured generic-step extraction from a descent-eligible context, provided a
generic pivot is already available.
-/
theorem genericStepData_of_descentEligible
    (C : Context) (_hC : ContextDescentEligible C)
    (hgen : ∃ p : ℕ, Removable C.S p ∧ ContextGenericGain C p) :
    ∃ _ : GenericStepData C, True := by
  rcases hgen with ⟨p, _hp, hgp⟩
  exact ⟨genericStepData_of_contextGenericGain C hgp, trivial⟩

/--
A generic one-step descent exists from a descent-eligible context provided
there is a removable prime satisfying the generic-side gain criterion.
-/
theorem exists_generic_step_of_descentEligible
    (C : Context) (_hC : ContextDescentEligible C)
    (hgen : ∃ p : ℕ, Removable C.S p ∧ ContextGenericGain C p) :
    ∃ _s : GenericStepData C, True := by
  exact genericStepData_of_descentEligible C _hC hgen

/--
A lightweight profile of a generic chain, recording level preservation and
budget compatibility explicitly.
-/
structure GenericChainProfile (C D : Context) where
  chain : GenericChain C D
  hlevel : D.y = C.y
  hbudget : genericChainLength chain ≤ KmaxB C.y

def genericChainProfile_nil (C : Context) :
    GenericChainProfile C C :=
  { chain := GenericChain.nil C
    hlevel := rfl
    hbudget := by
      exact KmaxB_nonneg C.y }

end CaseB
end Lehmer