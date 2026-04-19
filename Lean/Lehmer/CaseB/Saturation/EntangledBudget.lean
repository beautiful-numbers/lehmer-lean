-- FILE: Lean/Lehmer/CaseB/Saturation/EntangledBudget.lean

import Lehmer.Prelude
import Lehmer.Support.GenericEntangled

namespace Lehmer
namespace CaseB
namespace Saturation

open Lehmer.Support
open Classical

/-- The entangled part of a support at level `y` relative to the threshold `h`. -/
noncomputable def entangledSupport (h : ℕ → ℕ) (S : Finset ℕ) (y : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun p => entangledIn h S y p) (Classical.decPred _) S

@[simp] theorem entangledSupport_def (h : ℕ → ℕ) (S : Finset ℕ) (y : ℕ) :
    entangledSupport h S y =
      @Finset.filter ℕ (fun p => entangledIn h S y p) (Classical.decPred _) S := rfl

/-- Membership in the entangled support is exactly support membership plus the
    entangled predicate. -/
theorem mem_entangledSupport_iff
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ} :
    p ∈ entangledSupport h S y ↔ p ∈ S ∧ entangledIn h S y p := by
  simp [entangledSupport]

/-- The entangled support is a sub-support of the ambient support. -/
theorem entangledSupport_subset
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ} :
    entangledSupport h S y ⊆ S := by
  intro p hp
  exact (mem_entangledSupport_iff.mp hp).1

/-- Consequently, the entangled cardinality is bounded by the ambient support
    cardinality. -/
theorem card_entangledSupport_le_card_support
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ} :
    (entangledSupport h S y).card ≤ S.card := by
  exact Finset.card_le_card (entangledSupport_subset (h := h) (S := S) (y := y))

/-- Abstract witness data for the entangled part of a support. -/
structure EntangledWitnessData (h : ℕ → ℕ) (S : Finset ℕ) (y : ℕ) where
  witness : ℕ → ℕ
  witnessSet : Finset ℕ
  witness_mem :
    ∀ p, p ∈ entangledSupport h S y → witness p ∈ witnessSet

/-- Abstract bounded-reuse condition for a witness map on a finite set. -/
def WitnessReuseBound (E : Finset ℕ) (witness : ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ q, (E.filter (fun p => witness p = q)).card ≤ B

@[simp] theorem WitnessReuseBound_def
    (E : Finset ℕ) (witness : ℕ → ℕ) (B : ℕ) :
    WitnessReuseBound E witness B =
      (∀ q, (E.filter (fun p => witness p = q)).card ≤ B) := rfl

/-- Coverage of the entangled support by the witness set. -/
theorem witness_mem_of_mem_entangledSupport
    {h : ℕ → ℕ} {S : Finset ℕ} {y p : ℕ}
    (D : EntangledWitnessData h S y)
    (hp : p ∈ entangledSupport h S y) :
    D.witness p ∈ D.witnessSet := by
  exact D.witness_mem p hp

/-- Combinatorial fiber bound: if every element of `E` lands in `W`, and every
    witness fiber has cardinality at most `B`, then `|E| ≤ B * |W|`. -/
theorem card_le_reuseBound_mul_card_witnessSet
    {E W : Finset ℕ} {witness : ℕ → ℕ} {B : ℕ}
    (hcover : ∀ p, p ∈ E → witness p ∈ W)
    (hreuse : ∀ q, (E.filter (fun p => witness p = q)).card ≤ B) :
    E.card ≤ B * W.card := by
  classical
  let fiber : ℕ → Finset ℕ := fun q => E.filter (fun p => witness p = q)

  have hEq : E = W.biUnion fiber := by
    ext p
    constructor
    · intro hp
      exact Finset.mem_biUnion.mpr ⟨witness p, hcover p hp, by
        dsimp [fiber]
        rw [Finset.mem_filter]
        exact ⟨hp, rfl⟩⟩
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨q, _, hpq⟩
      dsimp [fiber] at hpq
      exact (Finset.mem_filter.mp hpq).1

  have hdisj :
      ∀ q₁ ∈ W, ∀ q₂ ∈ W, q₁ ≠ q₂ → Disjoint (fiber q₁) (fiber q₂) := by
    intro q₁ _ q₂ _ hneq
    refine Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    dsimp [fiber] at hp₁ hp₂
    have h1 : witness p = q₁ := (Finset.mem_filter.mp hp₁).2
    have h2 : witness p = q₂ := (Finset.mem_filter.mp hp₂).2
    exact hneq (h1.symm.trans h2)

  calc
    E.card = (W.biUnion fiber).card := by rw [hEq]
    _ = ∑ q ∈ W, (fiber q).card := by
      exact Finset.card_biUnion hdisj
    _ ≤ ∑ q ∈ W, B := by
      refine Finset.sum_le_sum ?_
      intro q hq
      dsimp [fiber]
      exact hreuse q
    _ = B * W.card := by
      simp [Nat.mul_comm]

/-- Specialization of the abstract fiber bound to the entangled support. -/
theorem entangled_budget_bound
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ}
    (D : EntangledWitnessData h S y)
    (B : ℕ)
    (hreuse :
      ∀ q, ((entangledSupport h S y).filter (fun p => D.witness p = q)).card ≤ B) :
    (entangledSupport h S y).card ≤ B * D.witnessSet.card := by
  exact card_le_reuseBound_mul_card_witnessSet
    (fun p hp => D.witness_mem p hp)
    hreuse

/-- Practical specialization to the frequent “at most two reuses” regime. -/
theorem entangled_budget_bound_two
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ}
    (D : EntangledWitnessData h S y)
    (hreuse :
      ∀ q, ((entangledSupport h S y).filter (fun p => D.witness p = q)).card ≤ 2) :
    (entangledSupport h S y).card ≤ 2 * D.witnessSet.card := by
  exact entangled_budget_bound D 2 hreuse

end Saturation
end CaseB
end Lehmer