-- FILE: Lean/Lehmer/CaseB/Descent/P2Decrease.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Support.PotentialP2 : def param
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
-/

import Lehmer.Prelude
import Lehmer.Support.PotentialP2
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain

namespace Lehmer
namespace CaseB

open Lehmer.Support

/--
The central Case B descent statement:
under a removable controlled removal and the paper-style gain criterion,
the principal paper-calibrated discrete potential strictly decreases.
-/
theorem P2_strict_decrease_of_removable
    (S : Finset ℕ) (p y : ℕ) (_hp : Removable S p)
    (hgain : GainCriterion S p y) :
    potentialP2 (epsilonB y) (paperDelta y) (remove S p) <
      potentialP2 (epsilonB y) (paperDelta y) S := by
  exact hasGain_of_gainCriterion S p y hgain

/--
Generic primes force strict decrease of the principal paper-calibrated discrete
potential.
-/
theorem P2_strict_decrease_of_genericGain
    (S : Finset ℕ) (p y : ℕ) (_hp : Removable S p)
    (hgain : GenericGain S p y) :
    potentialP2 (epsilonB y) (paperDelta y) (remove S p) <
      potentialP2 (epsilonB y) (paperDelta y) S := by
  exact hasGain_of_genericGain S p y hgain

/--
Entangled primes force strict decrease of the principal paper-calibrated
discrete potential.
-/
theorem P2_strict_decrease_of_entangledGain
    (S : Finset ℕ) (p y : ℕ) (_hp : Removable S p)
    (hgain : EntangledGain S p y) :
    potentialP2 (epsilonB y) (paperDelta y) (remove S p) <
      potentialP2 (epsilonB y) (paperDelta y) S := by
  exact hasGain_of_entangledGain S p y hgain

/--
The gain criterion implies strict decrease of the principal paper-calibrated
discrete potential.
-/
theorem P2_strict_decrease_of_gainCriterion
    (S : Finset ℕ) (p y : ℕ)
    (hgain : GainCriterion S p y) :
    potentialP2 (epsilonB y) (paperDelta y) (remove S p) <
      potentialP2 (epsilonB y) (paperDelta y) S := by
  exact hasGain_of_gainCriterion S p y hgain

/--
Context-level form of strict decrease for the principal Case B potential.
-/
theorem potential_strict_decrease_of_removable
    (C : Context) (p : ℕ) (_hp : Removable C.S p)
    (hgain : ContextGainCriterion C p) :
    potential (nextContext C p) < potential C := by
  exact (contextHasGain_iff_potential C p).mp
    (contextHasGain_of_gainCriterion C p hgain)

/--
Context-level generic gain implies strict decrease of the principal Case B
potential.
-/
theorem potential_strict_decrease_of_genericGain
    (C : Context) (p : ℕ) (_hp : Removable C.S p)
    (hgain : ContextGenericGain C p) :
    potential (nextContext C p) < potential C := by
  exact (contextHasGain_iff_potential C p).mp
    (contextHasGain_of_genericGain C p hgain)

/--
Context-level entangled gain implies strict decrease of the principal Case B
potential.
-/
theorem potential_strict_decrease_of_entangledGain
    (C : Context) (p : ℕ) (_hp : Removable C.S p)
    (hgain : ContextEntangledGain C p) :
    potential (nextContext C p) < potential C := by
  exact (contextHasGain_iff_potential C p).mp
    (contextHasGain_of_entangledGain C p hgain)

/--
Context-level gain criterion implies strict decrease of the principal Case B
potential.
-/
theorem P2_strict_decrease_of_contextGainCriterion
    (C : Context) (p : ℕ)
    (hgain : ContextGainCriterion C p) :
    potential (nextContext C p) < potential C := by
  exact (contextHasGain_iff_potential C p).mp
    (contextHasGain_of_gainCriterion C p hgain)

/--
A controlled removal step carries strict decrease of the principal
paper-calibrated discrete potential, provided the paper-style gain criterion is
available.
-/
theorem P2_strict_decrease_of_controlledRemoval
    (S T : Finset ℕ) (p y : ℕ)
    (hstep : ControlledRemoval S p T)
    (hgain : GainCriterion S p y) :
    potentialP2 (epsilonB y) (paperDelta y) T <
      potentialP2 (epsilonB y) (paperDelta y) S := by
  rcases hstep with ⟨hp, rfl⟩
  exact P2_strict_decrease_of_removable S p y hp hgain

/--
Context-level version of strict decrease under a controlled-removal step.
-/
theorem potential_strict_decrease_of_contextControlledRemoval
    (C C' : Context) (p : ℕ)
    (hstep : ContextControlledRemoval C p C')
    (hgain : ContextGainCriterion C p) :
    potential C' < potential C := by
  rcases hstep with ⟨hp, rfl⟩
  exact potential_strict_decrease_of_removable C p hp hgain

/--
The gain criterion implies strict decrease of the principal paper-calibrated
discrete potential.
-/
theorem gainCriterion_implies_P2_strict_decrease
    (S : Finset ℕ) (p y : ℕ) :
    GainCriterion S p y →
      potentialP2 (epsilonB y) (paperDelta y) (remove S p) <
        potentialP2 (epsilonB y) (paperDelta y) S := by
  intro hgain
  exact hasGain_of_gainCriterion S p y hgain

/--
Context-level gain criterion implies strict decrease of the principal Case B
potential.
-/
theorem contextGainCriterion_implies_potential_strict_decrease
    (C : Context) (p : ℕ) :
    ContextGainCriterion C p → potential (nextContext C p) < potential C := by
  intro hgain
  exact (contextHasGain_iff_potential C p).mp
    (contextHasGain_of_gainCriterion C p hgain)

/--
Generic gain is sufficient for the full paper-style gain criterion.
-/
theorem gainCriterion_of_genericGain
    (S : Finset ℕ) (p y : ℕ)
    (hgain : GenericGain S p y) :
    GainCriterion S p y := by
  exact Or.inl hgain

/--
Entangled gain is sufficient for the full paper-style gain criterion.
-/
theorem gainCriterion_of_entangledGain
    (S : Finset ℕ) (p y : ℕ)
    (hgain : EntangledGain S p y) :
    GainCriterion S p y := by
  exact Or.inr hgain

/--
Every removable element determines a canonical strictly-decreasing successor,
provided the paper-style gain criterion is available.
-/
theorem exists_strictly_decreasing_successor_of_removable
    (C : Context) {p : ℕ} (hp : Removable C.S p)
    (hgain : ContextGainCriterion C p) :
    ∃ C', ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  refine ⟨nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hp,
    potential_strict_decrease_of_removable C p hp hgain⟩

/--
A context-level generic gain yields a strictly-decreasing controlled-removal
successor.
-/
theorem exists_strictly_decreasing_successor_of_contextGenericGain
    (C : Context) {p : ℕ}
    (hgain : ContextGenericGain C p) :
    ∃ C', ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  refine ⟨nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hgain.1.1,
    potential_strict_decrease_of_genericGain C p hgain.1.1 hgain⟩

/--
A context-level entangled gain yields a strictly-decreasing controlled-removal
successor.
-/
theorem exists_strictly_decreasing_successor_of_contextEntangledGain
    (C : Context) {p : ℕ}
    (hgain : ContextEntangledGain C p) :
    ∃ C', ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  refine ⟨nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hgain.1.1,
    potential_strict_decrease_of_entangledGain C p hgain.1.1 hgain⟩

/--
Local explicit profile of a classified decreasing step in the principal Case B
potential.
-/
structure DecreasingStepProfile (C : Context) where
  p : ℕ
  C' : Context
  hstep : ContextControlledRemoval C p C'
  hgain : ContextGainCriterion C p
  hdec : potential C' < potential C

def decreasingStepProfile_of_genericGain
    (C : Context) {p : ℕ}
    (h : ContextGenericGain C p) :
    DecreasingStepProfile C := by
  refine
    { p := p
      C' := nextContext C p
      hstep := contextControlledRemoval_canonical C p h.1.1
      hgain := Or.inl h
      hdec := potential_strict_decrease_of_genericGain C p h.1.1 h }

def decreasingStepProfile_of_entangledGain
    (C : Context) {p : ℕ}
    (h : ContextEntangledGain C p) :
    DecreasingStepProfile C := by
  refine
    { p := p
      C' := nextContext C p
      hstep := contextControlledRemoval_canonical C p h.1.1
      hgain := Or.inr h
      hdec := potential_strict_decrease_of_entangledGain C p h.1.1 h }

@[simp] theorem decreasingStepProfile_of_genericGain_p
    (C : Context) {p : ℕ}
    (h : ContextGenericGain C p) :
    (decreasingStepProfile_of_genericGain C h).p = p := rfl

@[simp] theorem decreasingStepProfile_of_genericGain_C'
    (C : Context) {p : ℕ}
    (h : ContextGenericGain C p) :
    (decreasingStepProfile_of_genericGain C h).C' = nextContext C p := rfl

@[simp] theorem decreasingStepProfile_of_entangledGain_p
    (C : Context) {p : ℕ}
    (h : ContextEntangledGain C p) :
    (decreasingStepProfile_of_entangledGain C h).p = p := rfl

@[simp] theorem decreasingStepProfile_of_entangledGain_C'
    (C : Context) {p : ℕ}
    (h : ContextEntangledGain C p) :
    (decreasingStepProfile_of_entangledGain C h).C' = nextContext C p := rfl

theorem DecreasingStepProfile.hasCriterion
    {C : Context} (D : DecreasingStepProfile C) :
    ContextGainCriterion C D.p := by
  exact D.hgain

theorem DecreasingStepProfile.hasDecrease
    {C : Context} (D : DecreasingStepProfile C) :
    potential D.C' < potential C := by
  exact D.hdec

theorem DecreasingStepProfile.hasStep
    {C : Context} (D : DecreasingStepProfile C) :
    ContextControlledRemoval C D.p D.C' := by
  exact D.hstep

theorem DecreasingStepProfile.preserves_level
    {C : Context} (D : DecreasingStepProfile C) :
    D.C'.y = C.y := by
  exact ContextControlledRemoval_preserves_level D.hstep

theorem DecreasingStepProfile.support_eq
    {C : Context} (D : DecreasingStepProfile C) :
    D.C'.S = remove C.S D.p := by
  exact ContextControlledRemoval_support_eq D.hstep

theorem contextGainCriterion_of_decreasingStepProfile
    {C : Context} (D : DecreasingStepProfile C) :
    ContextGainCriterion C D.p := by
  exact D.hgain

theorem potential_strict_decrease_of_decreasingStepProfile
    {C : Context} (D : DecreasingStepProfile C) :
    potential D.C' < potential C := by
  exact D.hdec

theorem exists_successor_of_decreasingStepProfile
    {C : Context} (D : DecreasingStepProfile C) :
    ∃ C', ContextControlledRemoval C D.p C' ∧ potential C' < potential C := by
  exact ⟨D.C', D.hstep, D.hdec⟩

end CaseB
end Lehmer