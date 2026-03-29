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
the second potential `P2` strictly decreases.
-/
theorem P2_strict_decrease_of_removable
    (S : Finset ℕ) (p y : ℕ) (_hp : Removable S p)
    (hgain : GainCriterion S p y) :
    P2 (remove S p) y < P2 S y := by
  exact hasGain_of_gainCriterion S p y hgain

/--
Generic primes force strict decrease of `P2`.
-/
theorem P2_strict_decrease_of_genericGain
    (S : Finset ℕ) (p y : ℕ) (_hp : Removable S p)
    (hgain : GenericGain S p y) :
    P2 (remove S p) y < P2 S y := by
  exact hasGain_of_genericGain S p y hgain

/--
Entangled primes force strict decrease of `P2`.
-/
theorem P2_strict_decrease_of_entangledGain
    (S : Finset ℕ) (p y : ℕ) (_hp : Removable S p)
    (hgain : EntangledGain S p y) :
    P2 (remove S p) y < P2 S y := by
  exact hasGain_of_entangledGain S p y hgain

/--
Context-level form of strict decrease for the Case B potential.
-/
theorem potential_strict_decrease_of_removable
    (C : Context) (p : ℕ) (_hp : Removable C.S p)
    (hgain : ContextGainCriterion C p) :
    potential (nextContext C p) < potential C := by
  exact contextHasGain_of_gainCriterion C p hgain

/--
Context-level generic gain implies strict decrease of the Case B potential.
-/
theorem potential_strict_decrease_of_genericGain
    (C : Context) (p : ℕ) (_hp : Removable C.S p)
    (hgain : ContextGenericGain C p) :
    potential (nextContext C p) < potential C := by
  exact contextHasGain_of_genericGain C p hgain

/--
Context-level entangled gain implies strict decrease of the Case B potential.
-/
theorem potential_strict_decrease_of_entangledGain
    (C : Context) (p : ℕ) (_hp : Removable C.S p)
    (hgain : ContextEntangledGain C p) :
    potential (nextContext C p) < potential C := by
  exact contextHasGain_of_entangledGain C p hgain

/--
A controlled removal step carries strict decrease of `P2`,
provided the paper-style gain criterion is available.
-/
theorem P2_strict_decrease_of_controlledRemoval
    (S T : Finset ℕ) (p y : ℕ)
    (hstep : ControlledRemoval S p T)
    (hgain : GainCriterion S p y) :
    P2 T y < P2 S y := by
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
The gain criterion implies strict decrease of `P2`.
-/
theorem gainCriterion_implies_P2_strict_decrease
    (S : Finset ℕ) (p y : ℕ) :
    GainCriterion S p y → P2 (remove S p) y < P2 S y := by
  intro hgain
  exact hasGain_of_gainCriterion S p y hgain

/--
Context-level gain criterion implies strict decrease of the Case B potential.
-/
theorem contextGainCriterion_implies_potential_strict_decrease
    (C : Context) (p : ℕ) :
    ContextGainCriterion C p → potential (nextContext C p) < potential C := by
  intro hgain
  exact contextHasGain_of_gainCriterion C p hgain

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

end CaseB
end Lehmer