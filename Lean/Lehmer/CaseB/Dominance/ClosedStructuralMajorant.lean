-- FILE: Lean/Lehmer/CaseB/Dominance/ClosedStructuralMajorant.lean
import Lehmer.Prelude
import Lehmer.CaseB.Saturation.GenericBudget
import Lehmer.CaseB.Saturation.EntangledBudget
import Lehmer.CaseB.Dominance.StructuralMajorant

namespace Lehmer
namespace CaseB
namespace Dominance

open Lehmer.CaseB.Saturation

/--
Closed budget functions in the level parameter `y`.

This packages the two closed structural budgets needed to bound the generic and
entangled parts of the support.
-/
structure ClosedBudgetFunctions where
  closedGenericBudget : ℕ → ℕ
  closedEntangledBudget : ℕ → ℕ

/-- Closed generic budget at level `y`. -/
abbrev closedGenericBudget (B : ClosedBudgetFunctions) (y : ℕ) : ℕ :=
  B.closedGenericBudget y

/-- Closed entangled budget at level `y`. -/
abbrev closedEntangledBudget (B : ClosedBudgetFunctions) (y : ℕ) : ℕ :=
  B.closedEntangledBudget y

/-- Closed structural majorant at level `y`. -/
def closedStructuralMajorant (B : ClosedBudgetFunctions) (y : ℕ) : ℕ :=
  closedGenericBudget B y + closedEntangledBudget B y

@[simp] theorem closedStructuralMajorant_def
    (B : ClosedBudgetFunctions) (y : ℕ) :
    closedStructuralMajorant B y =
      closedGenericBudget B y + closedEntangledBudget B y := rfl

/-- Main closed structural support bound from separate closed generic and
    entangled budget bounds. -/
theorem supportCard_le_closedStructuralMajorant
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ}
    (B : ClosedBudgetFunctions)
    (hG : (genericSupport h S y).card ≤ closedGenericBudget B y)
    (hE : (entangledSupport h S y).card ≤ closedEntangledBudget B y) :
    S.card ≤ closedStructuralMajorant B y := by
  simpa [closedStructuralMajorant] using
    supportCard_le_structuralMajorantFromBounds
      (h := h) (S := S) (y := y) hG hE

/-- Structured-budget version of the closed structural support bound. -/
theorem supportCard_le_closedStructuralMajorant_of_data
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ}
    (B : ClosedBudgetFunctions)
    (D : StructuralBudgetData h S y)
    (hG : D.genericBound ≤ closedGenericBudget B y)
    (hE : D.entangledBound ≤ closedEntangledBudget B y) :
    S.card ≤ closedStructuralMajorant B y := by
  have hD : S.card ≤ structuralMajorantOfData D :=
    supportCard_le_structuralMajorantOfData D
  have hM :
      structuralMajorantOfData D ≤ closedStructuralMajorant B y := by
    rw [structuralMajorantOfData_def, closedStructuralMajorant_def]
    exact Nat.add_le_add hG hE
  exact le_trans hD hM

/-- The closed generic budget is bounded by the closed structural majorant. -/
theorem closedGenericBudget_le_closedStructuralMajorant
    (B : ClosedBudgetFunctions) (y : ℕ) :
    closedGenericBudget B y ≤ closedStructuralMajorant B y := by
  rw [closedStructuralMajorant_def]
  exact Nat.le_add_right _ _

/-- The closed entangled budget is bounded by the closed structural majorant. -/
theorem closedEntangledBudget_le_closedStructuralMajorant
    (B : ClosedBudgetFunctions) (y : ℕ) :
    closedEntangledBudget B y ≤ closedStructuralMajorant B y := by
  rw [closedStructuralMajorant_def]
  exact Nat.le_add_left _ _

/-- Monotonicity of the closed structural majorant with respect to the two closed
    component budgets. -/
theorem closedStructuralMajorant_mono
    {B₁ B₂ : ClosedBudgetFunctions} {y : ℕ}
    (hG : closedGenericBudget B₁ y ≤ closedGenericBudget B₂ y)
    (hE : closedEntangledBudget B₁ y ≤ closedEntangledBudget B₂ y) :
    closedStructuralMajorant B₁ y ≤ closedStructuralMajorant B₂ y := by
  rw [closedStructuralMajorant_def, closedStructuralMajorant_def]
  exact Nat.add_le_add hG hE

end Dominance
end CaseB
end Lehmer