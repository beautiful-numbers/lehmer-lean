-- FILE: Lean/Lehmer/CaseB/Dominance/StructuralMajorant.lean
import Lehmer.Prelude
import Lehmer.CaseB.Saturation.GenericBudget
import Lehmer.CaseB.Saturation.EntangledBudget
import Lehmer.CaseB.Saturation.StructuralSupportBound

namespace Lehmer
namespace CaseB
namespace Dominance

open Lehmer.CaseB.Saturation

/--
Abstract structural budget data: a generic bound plus an entangled bound for a
fixed support at level `y`.
-/
structure StructuralBudgetData (h : ℕ → ℕ) (S : Finset ℕ) (y : ℕ) where
  genericBound : ℕ
  entangledBound : ℕ
  hgeneric : (genericSupport h S y).card ≤ genericBound
  hentangled : (entangledSupport h S y).card ≤ entangledBound

/-- Structural majorant built from separate generic and entangled bounds. -/
def structuralMajorantFromBounds (G E : ℕ) : ℕ :=
  G + E

@[simp] theorem structuralMajorantFromBounds_def (G E : ℕ) :
    structuralMajorantFromBounds G E = G + E := rfl

/-- Structural majorant attached to a structured budget package. -/
def structuralMajorantOfData
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ}
    (D : StructuralBudgetData h S y) : ℕ :=
  structuralMajorantFromBounds D.genericBound D.entangledBound

@[simp] theorem structuralMajorantOfData_def
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ}
    (D : StructuralBudgetData h S y) :
    structuralMajorantOfData D = D.genericBound + D.entangledBound := rfl

/-- Main synthesis theorem from separate generic and entangled bounds. -/
theorem supportCard_le_structuralMajorantFromBounds
    {h : ℕ → ℕ} {S : Finset ℕ} {y G E : ℕ}
    (hG : (genericSupport h S y).card ≤ G)
    (hE : (entangledSupport h S y).card ≤ E) :
    S.card ≤ structuralMajorantFromBounds G E := by
  simpa [structuralMajorantFromBounds] using
    supportCard_le_structuralSupportBound (h := h) (S := S) (y := y) hG hE

/-- Structured-budget version of the structural support bound. -/
theorem supportCard_le_structuralMajorantOfData
    {h : ℕ → ℕ} {S : Finset ℕ} {y : ℕ}
    (D : StructuralBudgetData h S y) :
    S.card ≤ structuralMajorantOfData D := by
  exact supportCard_le_structuralMajorantFromBounds
    (h := h) (S := S) (y := y) D.hgeneric D.hentangled

/-- Monotonicity of the structural majorant in its two budget arguments. -/
theorem structuralMajorantFromBounds_mono
    {G₁ G₂ E₁ E₂ : ℕ}
    (hG : G₁ ≤ G₂)
    (hE : E₁ ≤ E₂) :
    structuralMajorantFromBounds G₁ E₁ ≤ structuralMajorantFromBounds G₂ E₂ := by
  simpa [structuralMajorantFromBounds] using Nat.add_le_add hG hE

end Dominance
end CaseB
end Lehmer