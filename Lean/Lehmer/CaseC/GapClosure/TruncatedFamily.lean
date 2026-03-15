-- FILE: Lean/Lehmer/CaseC/GapClosure/TruncatedFamily.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.GapClosure.SupportProfiles

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

/--
A support belongs to the truncated Case C family at parameters `(y, W)`
if every element is at least `y` and the support cardinality is at most `W`.

For MVP-3 this is the minimal finite-support profile family used to state
the gap-to-closure pipeline.
-/
def InTruncatedFamily (y W : ℕ) (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, y ≤ p) ∧ supportCard S ≤ W

/--
Context-free alias for the truncated family.
-/
abbrev TruncatedFamily (y W : ℕ) : Set (Finset ℕ) :=
  {S | InTruncatedFamily y W S}

@[simp] theorem InTruncatedFamily_def (y W : ℕ) (S : Finset ℕ) :
    InTruncatedFamily y W S = ((∀ p ∈ S, y ≤ p) ∧ supportCard S ≤ W) := rfl

@[simp] theorem mem_TruncatedFamily_iff (y W : ℕ) (S : Finset ℕ) :
    S ∈ TruncatedFamily y W ↔ InTruncatedFamily y W S := Iff.rfl

/--
The empty support belongs to every truncated family.
-/
theorem empty_mem_TruncatedFamily (y W : ℕ) :
    (∅ : Finset ℕ) ∈ TruncatedFamily y W := by
  simp [TruncatedFamily, InTruncatedFamily, supportCard]

/--
Membership in the truncated family gives the lower-bound condition.
-/
theorem truncated_lower_bound {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S) :
    ∀ p ∈ S, y ≤ p := by
  exact hS.1

/--
Membership in the truncated family gives the cardinality bound.
-/
theorem truncated_card_bound {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S) :
    supportCard S ≤ W := by
  exact hS.2

/--
If `T ⊆ S` and `S` lies in the truncated family, then `T` satisfies the
same lower-bound condition.
-/
theorem truncated_lower_bound_mono
    {y W : ℕ} {S T : Finset ℕ}
    (hTS : T ⊆ S) (hS : InTruncatedFamily y W S) :
    ∀ p ∈ T, y ≤ p := by
  intro p hp
  exact hS.1 p (hTS hp)

/--
A subset of a truncated-family support with no larger cardinality bound
remains in the same truncated family.
-/
theorem truncated_subset
    {y W : ℕ} {S T : Finset ℕ}
    (hTS : T ⊆ S) (hS : InTruncatedFamily y W S)
    (hcard : supportCard T ≤ supportCard S) :
    InTruncatedFamily y W T := by
  refine ⟨truncated_lower_bound_mono hTS hS, ?_⟩
  exact le_trans hcard hS.2

/--
Erasing an element preserves membership in the truncated family.
-/
theorem truncated_erase {y W : ℕ} {S : Finset ℕ} {p : ℕ}
    (hS : InTruncatedFamily y W S) :
    InTruncatedFamily y W (S.erase p) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    exact hS.1 q (Finset.mem_of_mem_erase hq)
  ·
    have hsub : S.erase p ⊆ S := by
      intro q hq
      exact Finset.mem_of_mem_erase hq
    have hcard : supportCard (S.erase p) ≤ supportCard S := by
      simpa [supportCard] using Finset.card_le_card hsub
    exact le_trans hcard hS.2

/--
The support profile attached to a support in the truncated family.
This is just a named wrapper around `supportIndex`, useful for the later
gap-optimization files.
-/
def truncatedProfile (y W : ℕ) (S : Finset ℕ) : ℚ :=
  supportIndex S

@[simp] theorem truncatedProfile_def (y W : ℕ) (S : Finset ℕ) :
    truncatedProfile y W S = supportIndex S := rfl

/--
Stable MVP-3 placeholder: the truncated family at `(y, W)` is finite in the
sense needed later for the Case C gap optimization pipeline.
-/
theorem truncatedFamily_finite_placeholder (y W : ℕ) :
    Set.Finite {S : Finset ℕ | InTruncatedFamily y W S} := by
  sorry

end GapClosure
end CaseC
end Lehmer