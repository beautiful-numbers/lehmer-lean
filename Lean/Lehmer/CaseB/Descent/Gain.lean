-- FILE: Lean/Lehmer/CaseB/Descent/Gain.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Support.PotentialP2 : def param
- Lehmer.Support.IncrementRatio : def thm
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Parameters : def thm
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
-/

import Lehmer.Prelude
import Lehmer.Support.PotentialP2
import Lehmer.Support.IncrementRatio
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.ControlledRemoval

namespace Lehmer
namespace CaseB

open Lehmer.Support

/--
A local gain predicate for a controlled removal step.

At the descent layer, gain means strict decrease of the principal Case B
potential, i.e. the paper-calibrated discrete potential using `paperDelta y`.
-/
def HasGain (S : Finset ℕ) (p y : ℕ) : Prop :=
  potentialP2 (epsilonB y) (paperDelta y) (remove S p) <
    potentialP2 (epsilonB y) (paperDelta y) S

/-- Context-level gain predicate. -/
def ContextHasGain (C : Context) (p : ℕ) : Prop :=
  HasGain C.S p C.y

@[simp] theorem HasGain_def (S : Finset ℕ) (p y : ℕ) :
    HasGain S p y =
      (potentialP2 (epsilonB y) (paperDelta y) (remove S p) <
        potentialP2 (epsilonB y) (paperDelta y) S) := rfl

@[simp] theorem ContextHasGain_def (C : Context) (p : ℕ) :
    ContextHasGain C p = HasGain C.S p C.y := rfl

/--
Expanded form of context-level gain in terms of the local `HasGain` predicate.
-/
theorem contextHasGain_iff_HasGain (C : Context) (p : ℕ) :
    ContextHasGain C p ↔ HasGain C.S p C.y := by
  rfl

/--
Expanded form of context-level gain in terms of the principal discrete
paper-calibrated `potentialP2`.
-/
theorem contextHasGain_iff_potentialP2 (C : Context) (p : ℕ) :
    ContextHasGain C p ↔
      potentialP2 (epsilonB C.y) (paperDelta C.y) (remove C.S p) <
        potentialP2 (epsilonB C.y) (paperDelta C.y) C.S := by
  rfl

/--
Compatibility with the context-level principal potential notation from
`CaseB.Spec`.
-/
theorem contextHasGain_iff_potential (C : Context) (p : ℕ) :
    ContextHasGain C p ↔ potential (nextContext C p) < potential C := by
  simp [ContextHasGain, HasGain, potential, paperPotential, nextContext, remove]

/--
Analytic-style increment-ratio test `R_S(p) > h(y)` used to separate generic
and entangled local steps.
-/
def IncrementRatioGtH (S : Finset ℕ) (p y : ℕ) : Prop :=
  hB y < incrementRatio S p

@[simp] theorem IncrementRatioGtH_def (S : Finset ℕ) (p y : ℕ) :
    IncrementRatioGtH S p y = (hB y < incrementRatio S p) := rfl

/--
Paper-facing generic prime predicate for the Case B descent layer.
This strictly enforces the `R_S(p) > h(y)` side of the dichotomy.
-/
def GenericPrime (S : Finset ℕ) (p y : ℕ) : Prop :=
  Removable S p ∧ IncrementRatioGtH S p y

/--
Paper-facing entangled prime predicate for the Case B descent layer.
This strictly enforces the complementary side of the dichotomy.
-/
def EntangledPrime (S : Finset ℕ) (p y : ℕ) : Prop :=
  Removable S p ∧ ¬ IncrementRatioGtH S p y

@[simp] theorem GenericPrime_def (S : Finset ℕ) (p y : ℕ) :
    GenericPrime S p y = (Removable S p ∧ IncrementRatioGtH S p y) := rfl

@[simp] theorem EntangledPrime_def (S : Finset ℕ) (p y : ℕ) :
    EntangledPrime S p y = (Removable S p ∧ ¬ IncrementRatioGtH S p y) := rfl

/--
A generic removable prime is one that yields strict principal-potential
decrease through the generic side of the paper dichotomy.
-/
def GenericGain (S : Finset ℕ) (p y : ℕ) : Prop :=
  GenericPrime S p y ∧ HasGain S p y

/--
An entangled removable prime is one that yields strict principal-potential
decrease through the entangled side of the paper dichotomy.
-/
def EntangledGain (S : Finset ℕ) (p y : ℕ) : Prop :=
  EntangledPrime S p y ∧ HasGain S p y

@[simp] theorem GenericGain_def (S : Finset ℕ) (p y : ℕ) :
    GenericGain S p y = (GenericPrime S p y ∧ HasGain S p y) := rfl

@[simp] theorem EntangledGain_def (S : Finset ℕ) (p y : ℕ) :
    EntangledGain S p y = (EntangledPrime S p y ∧ HasGain S p y) := rfl

/--
Paper-style gain criterion: a removable prime yields gain either through the
generic side or through the entangled side.
-/
def GainCriterion (S : Finset ℕ) (p y : ℕ) : Prop :=
  GenericGain S p y ∨ EntangledGain S p y

@[simp] theorem GainCriterion_def (S : Finset ℕ) (p y : ℕ) :
    GainCriterion S p y = (GenericGain S p y ∨ EntangledGain S p y) := rfl

/-- Context-level generic gain predicate. -/
def ContextGenericGain (C : Context) (p : ℕ) : Prop :=
  GenericGain C.S p C.y

/-- Context-level entangled gain predicate. -/
def ContextEntangledGain (C : Context) (p : ℕ) : Prop :=
  EntangledGain C.S p C.y

/-- Context-level paper-style gain criterion. -/
def ContextGainCriterion (C : Context) (p : ℕ) : Prop :=
  GainCriterion C.S p C.y

@[simp] theorem ContextGenericGain_def (C : Context) (p : ℕ) :
    ContextGenericGain C p = GenericGain C.S p C.y := rfl

@[simp] theorem ContextEntangledGain_def (C : Context) (p : ℕ) :
    ContextEntangledGain C p = EntangledGain C.S p C.y := rfl

@[simp] theorem ContextGainCriterion_def (C : Context) (p : ℕ) :
    ContextGainCriterion C p = GainCriterion C.S p C.y := rfl

--------------------------------------------------------------------------------
-- LOCAL BRIDGE OBJECT FOR DOWNSTREAM LOCAL/TARGETED TERMINAL READINGS
--------------------------------------------------------------------------------

/--
Local gain-step profile exposed explicitly for downstream consumers.

It records:
- the removable pivot,
- the generic/entangled local kind split based on the true increment ratio,
- the strict decrease of the principal Case B potential.
-/
structure GainStepProfile (C : Context) where
  p : ℕ
  hrem : Removable C.S p
  hkind : IncrementRatioGtH C.S p C.y ∨ ¬ IncrementRatioGtH C.S p C.y
  hgain : HasGain C.S p C.y

def gainStepProfile_of_genericGain
    {C : Context} {p : ℕ}
    (h : ContextGenericGain C p) :
    GainStepProfile C := by
  refine
    { p := p
      hrem := h.1.1
      hkind := Or.inl h.1.2
      hgain := h.2 }

def gainStepProfile_of_entangledGain
    {C : Context} {p : ℕ}
    (h : ContextEntangledGain C p) :
    GainStepProfile C := by
  refine
    { p := p
      hrem := h.1.1
      hkind := Or.inr h.1.2
      hgain := h.2 }

@[simp] theorem gainStepProfile_of_genericGain_p
    {C : Context} {p : ℕ}
    (h : ContextGenericGain C p) :
    (gainStepProfile_of_genericGain h).p = p := rfl

@[simp] theorem gainStepProfile_of_entangledGain_p
    {C : Context} {p : ℕ}
    (h : ContextEntangledGain C p) :
    (gainStepProfile_of_entangledGain h).p = p := rfl

--------------------------------------------------------------------------------
-- DISJOINTNESS LEMMAS
--------------------------------------------------------------------------------

/--
Generic and entangled gains are mutually exclusive.
-/
theorem genericGain_not_entangledGain {S : Finset ℕ} {p y : ℕ}
    (hgen : GenericGain S p y) (hent : EntangledGain S p y) : False := by
  exact hent.1.2 hgen.1.2

/--
Context-level generic and entangled gains are mutually exclusive.
-/
theorem contextGeneric_not_entangled {C : Context} {p : ℕ}
    (hgen : ContextGenericGain C p) (hent : ContextEntangledGain C p) : False := by
  exact genericGain_not_entangledGain hgen hent

--------------------------------------------------------------------------------
-- DOWNSTREAM GAIN THEOREMS
--------------------------------------------------------------------------------

/--
Generic gain implies strict decrease of the local gain predicate.
-/
theorem hasGain_of_genericGain (S : Finset ℕ) (p y : ℕ)
    (hgain : GenericGain S p y) :
    HasGain S p y := by
  exact hgain.2

/--
Entangled gain implies strict decrease of the local gain predicate.
-/
theorem hasGain_of_entangledGain (S : Finset ℕ) (p y : ℕ)
    (hgain : EntangledGain S p y) :
    HasGain S p y := by
  exact hgain.2

/--
Paper-style dichotomy criterion implies strict decrease of the local gain
predicate.
-/
theorem hasGain_of_gainCriterion (S : Finset ℕ) (p y : ℕ)
    (hgain : GainCriterion S p y) :
    HasGain S p y := by
  rcases hgain with hgen | hent
  · exact hasGain_of_genericGain S p y hgen
  · exact hasGain_of_entangledGain S p y hent

/--
Context-level generic gain implies strict decrease of the context-level gain
predicate.
-/
theorem contextHasGain_of_genericGain (C : Context) (p : ℕ)
    (hgain : ContextGenericGain C p) :
    ContextHasGain C p := by
  exact hgain.2

/--
Context-level entangled gain implies strict decrease of the context-level gain
predicate.
-/
theorem contextHasGain_of_entangledGain (C : Context) (p : ℕ)
    (hgain : ContextEntangledGain C p) :
    ContextHasGain C p := by
  exact hgain.2

/--
Context-level paper-style gain criterion implies strict decrease of the
context-level gain predicate.
-/
theorem contextHasGain_of_gainCriterion (C : Context) (p : ℕ)
    (hgain : ContextGainCriterion C p) :
    ContextHasGain C p := by
  exact hasGain_of_gainCriterion C.S p C.y hgain

theorem GainStepProfile.removable
    {C : Context} (G : GainStepProfile C) :
    Removable C.S G.p := by
  exact G.hrem

theorem GainStepProfile.hasGain
    {C : Context} (G : GainStepProfile C) :
    HasGain C.S G.p C.y := by
  exact G.hgain

theorem GainStepProfile.hasCriterion
    {C : Context} (G : GainStepProfile C) :
    ContextGainCriterion C G.p := by
  rcases G.hkind with hgen | hent
  · exact Or.inl ⟨⟨G.hrem, hgen⟩, G.hgain⟩
  · exact Or.inr ⟨⟨G.hrem, hent⟩, G.hgain⟩

theorem contextGainCriterion_of_gainStepProfile
    {C : Context} (G : GainStepProfile C) :
    ContextGainCriterion C G.p := by
  exact G.hasCriterion

theorem contextHasGain_of_gainStepProfile
    {C : Context} (G : GainStepProfile C) :
    ContextHasGain C G.p := by
  exact contextHasGain_of_gainCriterion C G.p G.hasCriterion

theorem potential_strict_decrease_of_gainStepProfile
    {C : Context} (G : GainStepProfile C) :
    potential (nextContext C G.p) < potential C := by
  exact (contextHasGain_iff_potential C G.p).mp
    (contextHasGain_of_gainStepProfile G)

/--
A canonical controlled-removal step carries gain, provided the paper-style
gain criterion holds.
-/
theorem controlledRemoval_hasGain (S : Finset ℕ) (p y : ℕ)
    (hp : Removable S p)
    (hgain : GainCriterion S p y) :
    ControlledRemoval S p (remove S p) ∧ HasGain S p y := by
  exact ⟨controlledRemoval_canonical S p hp, hasGain_of_gainCriterion S p y hgain⟩

/--
Context-level canonical controlled removal together with gain.
-/
theorem contextControlledRemoval_hasGain (C : Context) (p : ℕ)
    (hp : Removable C.S p)
    (hgain : ContextGainCriterion C p) :
    ContextControlledRemoval C p (nextContext C p) ∧ ContextHasGain C p := by
  exact ⟨contextControlledRemoval_canonical C p hp, contextHasGain_of_gainCriterion C p hgain⟩

theorem exists_successor_of_gainStepProfile
    {C : Context} (G : GainStepProfile C) :
    ∃ C', ContextControlledRemoval C G.p C' ∧ ContextHasGain C G.p := by
  refine ⟨nextContext C G.p, ?_⟩
  exact contextControlledRemoval_hasGain C G.p G.hrem G.hasCriterion

theorem exists_potential_decreasing_successor_of_gainStepProfile
    {C : Context} (G : GainStepProfile C) :
    ∃ C', ContextControlledRemoval C G.p C' ∧ potential C' < potential C := by
  refine ⟨nextContext C G.p, ?_⟩
  refine ⟨contextControlledRemoval_canonical C G.p G.hrem, ?_⟩
  exact potential_strict_decrease_of_gainStepProfile G

/--
Every removable element yields a gainful successor context, provided the
paper-style gain criterion is available.
-/
theorem exists_gainful_successor_of_removable (C : Context)
    {p : ℕ} (hp : Removable C.S p)
    (hgain : ContextGainCriterion C p) :
    ∃ C', ContextControlledRemoval C p C' ∧ ContextHasGain C p := by
  refine ⟨nextContext C p, ?_⟩
  exact contextControlledRemoval_hasGain C p hp hgain

/--
A context-level generic gain yields a gainful controlled-removal successor
together with strict decrease of the principal Case B potential.
-/
theorem exists_gainful_successor_of_contextGenericGain
    (C : Context) {p : ℕ}
    (h : ContextGenericGain C p) :
    ∃ C', ContextControlledRemoval C p C' ∧
      ContextGenericGain C p ∧
      potential C' < potential C := by
  refine ⟨nextContext C p, ?_⟩
  refine ⟨contextControlledRemoval_canonical C p h.1.1, h, ?_⟩
  simpa [contextHasGain_iff_potential] using contextHasGain_of_genericGain C p h

/--
A context-level entangled gain yields a gainful controlled-removal successor
together with strict decrease of the principal Case B potential.
-/
theorem exists_gainful_successor_of_contextEntangledGain
    (C : Context) {p : ℕ}
    (h : ContextEntangledGain C p) :
    ∃ C', ContextControlledRemoval C p C' ∧
      ContextEntangledGain C p ∧
      potential C' < potential C := by
  refine ⟨nextContext C p, ?_⟩
  refine ⟨contextControlledRemoval_canonical C p h.1.1, h, ?_⟩
  simpa [contextHasGain_iff_potential] using contextHasGain_of_entangledGain C p h

end CaseB
end Lehmer