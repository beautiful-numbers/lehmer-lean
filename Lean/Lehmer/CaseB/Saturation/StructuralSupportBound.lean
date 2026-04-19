-- FILE: Lean/Lehmer/CaseB/Saturation/StructuralSupportBound.lean
import Lehmer.Prelude
import Lehmer.Support.GenericEntangled
import Lehmer.CaseB.Saturation.GenericBudget
import Lehmer.CaseB.Saturation.EntangledBudget

namespace Lehmer
namespace CaseB
namespace Saturation

open Lehmer.Support

-- Enable classical reasoning locally to satisfy `Finset.filter` decidability
attribute [local instance] Classical.propDecidable

/-- The generic part of a support at level `y` relative to the threshold `h`. -/
noncomputable def genericSupport (h : ℕ → ℕ) (S : Finset ℕ) (y : ℕ) : Finset ℕ :=
  S.filter (fun p => genericIn h S y p)

@[simp] theorem genericSupport_def (h : ℕ → ℕ) (S : Finset ℕ) (y : ℕ) :
    genericSupport h S y = S.filter (fun p => genericIn h S y p) := rfl

/-- Membership in the generic support is exactly support membership plus the
    generic predicate. -/
theorem mem_genericSupport_iff
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ} :
    p ∈ genericSupport h S y ↔ p ∈ S ∧ genericIn h S y p := by
  rw [genericSupport_def, Finset.mem_filter]

/-- The generic support is a sub-support of the ambient support. -/
theorem genericSupport_subset
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ} :
    genericSupport h S y ⊆ S := by
  intro p hp
  exact (mem_genericSupport_iff.mp hp).1

/-- Every element of the support is either generic or entangled. -/
theorem mem_support_implies_mem_generic_or_mem_entangled
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (hp : p ∈ S) :
    p ∈ genericSupport h S y ∨ p ∈ entangledSupport h S y := by
  rcases generic_or_entangled h S y p with hg | he
  · left
    exact mem_genericSupport_iff.mpr ⟨hp, hg⟩
  · right
    exact mem_entangledSupport_iff.mpr ⟨hp, he⟩

/-- The generic and entangled parts of the support are disjoint. -/
theorem disjoint_genericSupport_entangledSupport
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ} :
    Disjoint (genericSupport h S y) (entangledSupport h S y) := by
  rw [Finset.disjoint_left]
  intro p hpG hpE
  have hg : genericIn h S y p := (mem_genericSupport_iff.mp hpG).2
  have he : entangledIn h S y p := (mem_entangledSupport_iff.mp hpE).2
  exact (generic_not_entangled hg) he

/-- The support is the union of its generic and entangled parts. -/
theorem support_eq_union_generic_entangled
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ} :
    S = genericSupport h S y ∪ entangledSupport h S y := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_union.mpr (mem_support_implies_mem_generic_or_mem_entangled hp)
  · intro hp
    rcases Finset.mem_union.mp hp with hpG | hpE
    · exact genericSupport_subset hpG
    · exact entangledSupport_subset hpE

/-- Cardinal decomposition of the support into its generic and entangled parts. -/
theorem card_support_eq_card_generic_plus_card_entangled
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ} :
    S.card = (genericSupport h S y).card + (entangledSupport h S y).card := by
  have h_eq : S = genericSupport h S y ∪ entangledSupport h S y := support_eq_union_generic_entangled
  calc
    S.card = (genericSupport h S y ∪ entangledSupport h S y).card := congrArg Finset.card h_eq
    _ = (genericSupport h S y).card + (entangledSupport h S y).card := Finset.card_union_of_disjoint disjoint_genericSupport_entangledSupport

/-- Optional packaged structural bound as the sum of a generic and an entangled budget. -/
def structuralSupportBound (G E : ℕ) : ℕ :=
  G + E

@[simp] theorem structuralSupportBound_def (G E : ℕ) :
    structuralSupportBound G E = G + E := rfl

/-- Main structural support bound obtained by summing the generic and entangled budgets. -/
theorem supportCard_le_genericBudget_add_entangledBudget
    {h : ℕ → ℕ} {S : Finset ℕ} {y G E : ℕ}
    (hG : (genericSupport h S y).card ≤ G)
    (hE : (entangledSupport h S y).card ≤ E) :
    S.card ≤ G + E := by
  rw [card_support_eq_card_generic_plus_card_entangled]
  exact Nat.add_le_add hG hE

/-- Structured version of the previous theorem using `structuralSupportBound`. -/
theorem supportCard_le_structuralSupportBound
    {h : ℕ → ℕ} {S : Finset ℕ} {y G E : ℕ}
    (hG : (genericSupport h S y).card ≤ G)
    (hE : (entangledSupport h S y).card ≤ E) :
    S.card ≤ structuralSupportBound G E := by
  simpa [structuralSupportBound] using
    supportCard_le_genericBudget_add_entangledBudget hG hE

end Saturation
end CaseB
end Lehmer