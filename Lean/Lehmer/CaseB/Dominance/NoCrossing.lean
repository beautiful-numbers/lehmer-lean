-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossing.lean

import Lehmer.Prelude
import Mathlib.Data.Real.Basic
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.UBm
import Lehmer.Pivot.CaseAMreq
import Lehmer.Pipeline.Thresholds
import Lehmer.CaseB.Dominance.ClosedStructuralMajorant

namespace Lehmer
namespace CaseB
namespace Dominance

open Lehmer.Pivot

/-- Public alias for the shared analytic constant `C1`. -/
noncomputable def C1 : ℝ := Lehmer.Pivot.C1

@[simp] theorem C1_def :
    C1 = Lehmer.Pivot.C1 := rfl

/-- Public alias for the shared pivot threshold `Y0`. -/
def Y0 : ℕ := Lehmer.Pivot.Y0

@[simp] theorem Y0_def :
    Y0 = Lehmer.Pivot.Y0 := rfl

/-- Public real terminal threshold. -/
noncomputable def TB : ℝ :=
  max 17 (max (Real.exp 6) (max (10 / C1) Y0))

@[simp] theorem TB_def :
    TB = max 17 (max (Real.exp 6) (max (10 / C1) Y0)) := rfl

/-- Public prime terminal threshold. -/
noncomputable def Ystar : ℕ :=
  nextPrimeGe (Nat.ceil TB)

@[simp] theorem Ystar_def :
    Ystar = nextPrimeGe (Nat.ceil TB) := rfl

/-- `TB` lies below the public prime threshold `Ystar`. -/
theorem TB_le_Ystar :
    TB ≤ (Ystar : ℝ) := by
  rw [Ystar_def]
  have hceil : TB ≤ (Nat.ceil TB : ℝ) := Nat.le_ceil TB
  have hnext : (Nat.ceil TB : ℝ) ≤ (nextPrimeGe (Nat.ceil TB) : ℝ) := by
    exact_mod_cast nextPrimeGe_ge (Nat.ceil TB)
  exact le_trans hceil hnext

/-- `Ystar` is prime. -/
theorem Ystar_prime :
    Nat.Prime Ystar := by
  rw [Ystar_def]
  exact nextPrimeGe_prime (Nat.ceil TB)

/-- The base pivot threshold lies below `TB`. -/
theorem Y0_le_TB :
    (Y0 : ℝ) ≤ TB := by
  rw [TB_def]
  have h1 : (Y0 : ℝ) ≤ max (10 / C1) Y0 := by
    exact le_max_right _ _
  have h2 : max (10 / C1) Y0 ≤ max (Real.exp 6) (max (10 / C1) Y0) := by
    exact le_max_right _ _
  have h3 : max (Real.exp 6) (max (10 / C1) Y0) ≤ max 17 (max (Real.exp 6) (max (10 / C1) Y0)) := by
    exact le_max_right _ _
  exact le_trans h1 (le_trans h2 h3)

/-- Consequently `Y0 ≤ Ystar`. -/
theorem Y0_le_Ystar :
    Y0 ≤ Ystar := by
  have h0 : (Y0 : ℝ) ≤ TB := Y0_le_TB
  have h1 : TB ≤ (Ystar : ℝ) := TB_le_Ystar
  exact_mod_cast le_trans h0 h1

/-- A small useful public lower bound on `Ystar`. -/
theorem four_le_Ystar :
    4 ≤ Ystar := by
  have h4 : 4 ≤ Y0 := by
    simp [Y0]
  exact le_trans h4 Y0_le_Ystar

/-- Public structural majorant, obtained by casting the closed structural
    majorant to `ℝ`. -/
noncomputable def M (B : ClosedBudgetFunctions) (y : ℕ) : ℝ :=
  (closedStructuralMajorant B y : ℝ)

@[simp] theorem M_def (B : ClosedBudgetFunctions) (y : ℕ) :
    M B y = (closedStructuralMajorant B y : ℝ) := rfl

/-- Local no-crossing predicate at level `y`. -/
def NoCrossingAt (B : ClosedBudgetFunctions) (y : ℕ) : Prop :=
  M B y < (caseAMreq y : ℝ)

@[simp] theorem NoCrossingAt_def (B : ClosedBudgetFunctions) (y : ℕ) :
    NoCrossingAt B y = (M B y < (caseAMreq y : ℝ)) := rfl

/-- Uniform no-crossing predicate beyond the public terminal threshold `Ystar`. -/
def NoCrossingBeyondYstar (B : ClosedBudgetFunctions) : Prop :=
  ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt B y

@[simp] theorem NoCrossingBeyondYstar_def (B : ClosedBudgetFunctions) :
    NoCrossingBeyondYstar B =
      (∀ y : ℕ, Ystar ≤ y → Nat.Prime y → NoCrossingAt B y) := rfl

/-- Direct constructor for the local no-crossing predicate. -/
theorem noCrossingAt_of_assumption
    {B : ClosedBudgetFunctions} {y : ℕ}
    (h : M B y < (caseAMreq y : ℝ)) :
    NoCrossingAt B y := by
  exact h

/-- Direct constructor for the uniform no-crossing predicate. -/
theorem noCrossingBeyondYstar_of_assumption
    {B : ClosedBudgetFunctions}
    (h : ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → M B y < (caseAMreq y : ℝ)) :
    NoCrossingBeyondYstar B := by
  intro y hy hp
  exact h y hy hp

/-- Elimination form of the uniform no-crossing predicate. -/
theorem noCrossingAt_of_noCrossingBeyondYstar
    {B : ClosedBudgetFunctions} {y : ℕ}
    (h : NoCrossingBeyondYstar B)
    (hy : Ystar ≤ y)
    (hp : Nat.Prime y) :
    NoCrossingAt B y := by
  exact h y hy hp

/-- Contradiction-ready elimination form of uniform no-crossing. -/
theorem noCrossing_ready_for_contradiction
    {B : ClosedBudgetFunctions} {y : ℕ}
    (h : NoCrossingBeyondYstar B)
    (hy : Ystar ≤ y)
    (hp : Nat.Prime y) :
    M B y < (caseAMreq y : ℝ) := by
  exact noCrossingAt_of_noCrossingBeyondYstar h hy hp

end Dominance
end CaseB
end Lehmer