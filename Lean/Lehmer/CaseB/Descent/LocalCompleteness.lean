-- FILE: Lean/Lehmer/CaseB/Descent/LocalCompleteness.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Parameters : def thm
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Classical

def PurelyGenericSupport (S : Finset ℕ) (y : ℕ) : Prop :=
  ∀ p : ℕ, Removable S p → IncrementRatioGtH S p y

def ContextPurelyGeneric (C : Context) : Prop :=
  PurelyGenericSupport C.S C.y

@[simp] theorem PurelyGenericSupport_def (S : Finset ℕ) (y : ℕ) :
    PurelyGenericSupport S y =
      (∀ p : ℕ, Removable S p → IncrementRatioGtH S p y) := rfl

@[simp] theorem ContextPurelyGeneric_def (C : Context) :
    ContextPurelyGeneric C = PurelyGenericSupport C.S C.y := rfl

theorem nonSaturated_of_descentEligible_local
    {C : Context} (hC : ContextDescentEligible C) :
    ContextNonSaturated C := by
  exact hC.1

theorem nonempty_of_descentEligible_local
    {C : Context} (hC : ContextDescentEligible C) :
    C.S.Nonempty := by
  exact hC.2

theorem exists_removable_pivot_of_descentEligible
    (C : Context) (hC : ContextDescentEligible C) :
    ∃ p : ℕ, Removable C.S p := by
  rcases hC.2 with ⟨p, hp⟩
  exact ⟨p, hp⟩

theorem incrementRatioGtH_or_not_of_removable
    (S : Finset ℕ) (p y : ℕ)
    (_hp : Removable S p) :
    IncrementRatioGtH S p y ∨ ¬ IncrementRatioGtH S p y := by
  by_cases hk : IncrementRatioGtH S p y
  · exact Or.inl hk
  · exact Or.inr hk

theorem genericPrime_or_entangledPrime_of_removable
    (S : Finset ℕ) (p y : ℕ)
    (hp : Removable S p) :
    GenericPrime S p y ∨ EntangledPrime S p y := by
  by_cases hk : IncrementRatioGtH S p y
  · exact Or.inl ⟨hp, hk⟩
  · exact Or.inr ⟨hp, hk⟩

theorem contextGenericPrime_or_contextEntangledPrime_of_removable
    (C : Context) (p : ℕ)
    (hp : Removable C.S p) :
    GenericPrime C.S p C.y ∨ EntangledPrime C.S p C.y := by
  exact genericPrime_or_entangledPrime_of_removable C.S p C.y hp

theorem purelyGeneric_or_exists_entangledPrime_of_nonempty
    (S : Finset ℕ) (y : ℕ)
    (_hne : S.Nonempty) :
    PurelyGenericSupport S y ∨
      ∃ p : ℕ, EntangledPrime S p y := by
  classical
  by_cases hent : ∃ p : ℕ, EntangledPrime S p y
  · exact Or.inr hent
  · left
    intro p hp
    by_cases hk : IncrementRatioGtH S p y
    · exact hk
    · exfalso
      exact hent ⟨p, ⟨hp, hk⟩⟩

theorem purelyGeneric_or_exists_entangledPrime_of_descentEligible
    (C : Context)
    (hC : ContextDescentEligible C) :
    ContextPurelyGeneric C ∨
      ∃ p : ℕ, EntangledPrime C.S p C.y := by
  exact purelyGeneric_or_exists_entangledPrime_of_nonempty C.S C.y hC.2

structure LocalGenericEntangledBoundary (C : Context) where
  boundary :
    ContextPurelyGeneric C ∨ ∃ p : ℕ, EntangledPrime C.S p C.y

noncomputable def localGenericEntangledBoundary_of_descentEligible
    (C : Context)
    (hC : ContextDescentEligible C) :
    LocalGenericEntangledBoundary C :=
  { boundary := purelyGeneric_or_exists_entangledPrime_of_descentEligible C hC }

theorem localGenericEntangledBoundary_of_descentEligible_spec
    (C : Context)
    (hC : ContextDescentEligible C) :
    ContextPurelyGeneric C ∨
      ∃ p : ℕ, EntangledPrime C.S p C.y := by
  exact (localGenericEntangledBoundary_of_descentEligible C hC).boundary

theorem gainCriterion_of_removable_and_hasGain
    (C : Context) {p : ℕ}
    (hp : Removable C.S p)
    (hgain : HasGain C.S p C.y) :
    ContextGainCriterion C p := by
  by_cases hk : IncrementRatioGtH C.S p C.y
  · exact Or.inl ⟨⟨hp, hk⟩, hgain⟩
  · exact Or.inr ⟨⟨hp, hk⟩, hgain⟩

theorem exists_gainStepProfile_of_gainCriterion
    (C : Context) {p : ℕ}
    (hcrit : ContextGainCriterion C p) :
    ∃ G : GainStepProfile C, G.p = p := by
  rcases hcrit with hgen | hent
  · exact ⟨gainStepProfile_of_genericGain hgen, rfl⟩
  · exact ⟨gainStepProfile_of_entangledGain hent, rfl⟩

theorem exists_decreasingStepProfile_of_gainCriterion
    (C : Context) {p : ℕ}
    (hcrit : ContextGainCriterion C p) :
    ∃ D : DecreasingStepProfile C, D.p = p := by
  rcases hcrit with hgen | hent
  · exact ⟨decreasingStepProfile_of_genericGain C hgen, rfl⟩
  · exact ⟨decreasingStepProfile_of_entangledGain C hent, rfl⟩

theorem exists_strictly_decreasing_successor_of_gainCriterion_pivot
    (C : Context) {p : ℕ}
    (hp : Removable C.S p)
    (hcrit : ContextGainCriterion C p) :
    ∃ C' : Context, ContextControlledRemoval C p C' ∧ potential C' < potential C := by
  refine ⟨nextContext C p, ?_⟩
  exact ⟨contextControlledRemoval_canonical C p hp,
    potential_strict_decrease_of_removable C p hp hcrit⟩

theorem exists_full_local_progress_of_gainCriterion_pivot
    (C : Context) {p : ℕ}
    (hp : Removable C.S p)
    (hcrit : ContextGainCriterion C p) :
    ∃ C' : Context,
      ContextControlledRemoval C p C' ∧
      potential C' < potential C ∧
      contextDescentLength C' < contextDescentLength C := by
  refine ⟨nextContext C p, ?_⟩
  refine ⟨contextControlledRemoval_canonical C p hp, ?_, ?_⟩
  · exact potential_strict_decrease_of_removable C p hp hcrit
  · exact contextDescentLength_strict_decrease_of_removable C p hp

end CaseB
end Lehmer