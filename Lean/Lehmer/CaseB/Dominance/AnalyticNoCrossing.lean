-- FILE: Lean/Lehmer/CaseB/Dominance/AnalyticNoCrossing.lean
import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.ClosedStructuralMajorant
import Lehmer.Pivot.CaseAMreq

namespace Lehmer
namespace CaseB
namespace Dominance

open Lehmer.Pivot

/-- Local analytic barrier used to compare the closed structural majorant against
the pivot-side demand. -/
noncomputable def analyticBarrier (y : ℕ) : ℝ :=
  C1 * (y : ℝ)^2 / Real.log y

@[simp] theorem analyticBarrier_def (y : ℕ) :
    analyticBarrier y = C1 * (y : ℝ)^2 / Real.log y := rfl

/-- Sufficient analytic data on a closed budget package to derive no-crossing
beyond `Ystar`. -/
structure AnalyticNoCrossingData (B : ClosedBudgetFunctions) : Prop where
  majorant_lt_barrier :
    ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → M B y < analyticBarrier y
  barrier_lt_mreq :
    ∀ y : ℕ, Ystar ≤ y → Nat.Prime y -> analyticBarrier y < (caseAMreq y : ℝ)

@[simp] theorem AnalyticNoCrossingData.majorant_lt_barrier_apply
    {B : ClosedBudgetFunctions} (hB : AnalyticNoCrossingData B)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    M B y < analyticBarrier y := by
  exact hB.majorant_lt_barrier y hy hp

@[simp] theorem AnalyticNoCrossingData.barrier_lt_mreq_apply
    {B : ClosedBudgetFunctions} (hB : AnalyticNoCrossingData B)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    analyticBarrier y < (caseAMreq y : ℝ) := by
  exact hB.barrier_lt_mreq y hy hp

/-- Local no-crossing consequence of the analytic barrier bounds. -/
theorem analytic_noCrossingAt
    {B : ClosedBudgetFunctions} (hB : AnalyticNoCrossingData B)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt B y := by
  rw [NoCrossingAt_def]
  exact lt_trans
    (hB.majorant_lt_barrier y hy hp)
    (hB.barrier_lt_mreq y hy hp)

/-- Uniform no-crossing beyond `Ystar` from the corresponding analytic budget
data. -/
theorem analytic_noCrossingBeyondYstar
    {B : ClosedBudgetFunctions} (hB : AnalyticNoCrossingData B) :
    NoCrossingBeyondYstar B := by
  intro y hy hp
  exact analytic_noCrossingAt hB hy hp

/-- Unpacked version of the previous theorem. -/
theorem noCrossingBeyondYstar_of_bounds
    {B : ClosedBudgetFunctions}
    (h1 : ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → M B y < analyticBarrier y)
    (h2 : ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → analyticBarrier y < (caseAMreq y : ℝ)) :
    NoCrossingBeyondYstar B := by
  apply analytic_noCrossingBeyondYstar
  exact ⟨h1, h2⟩

end Dominance
end CaseB
end Lehmer