-- FILE: Lean/Lehmer/CaseB/Dominance/NoCrossingGlobal.lean
import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.AnalyticNoCrossing
import Lehmer.Pivot.CaseAMreq

namespace Lehmer
namespace CaseB
namespace Dominance

open Lehmer.Pivot

/-- Stable downstream alias for the global Case B no-crossing certificate. -/
def NoCrossingGlobalCertificate (B : ClosedBudgetFunctions) : Prop :=
  NoCrossingBeyondYstar B

@[simp] theorem NoCrossingGlobalCertificate_def (B : ClosedBudgetFunctions) :
    NoCrossingGlobalCertificate B = NoCrossingBeyondYstar B := rfl

/-- Build a global no-crossing certificate from the analytic no-crossing data. -/
theorem noCrossingGlobal_of_analytic
    {B : ClosedBudgetFunctions}
    (hB : AnalyticNoCrossingData B) :
    NoCrossingGlobalCertificate B := by
  exact analytic_noCrossingBeyondYstar hB

/-- Elimination form: a global no-crossing certificate yields the local
no-crossing statement at every prime level beyond `Ystar`. -/
theorem noCrossingAt_of_global
    {B : ClosedBudgetFunctions}
    (h : NoCrossingGlobalCertificate B)
    {y : ℕ} (hy : Ystar ≤ y) (hp : Nat.Prime y) :
    NoCrossingAt B y := by
  exact noCrossingAt_of_noCrossingBeyondYstar h hy hp

/-- Unpacked constructor for the global no-crossing certificate. -/
theorem noCrossingGlobal_of_bounds
    {B : ClosedBudgetFunctions}
    (h1 : ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → M B y < analyticBarrier y)
    (h2 : ∀ y : ℕ, Ystar ≤ y → Nat.Prime y → analyticBarrier y < (caseAMreq y : ℝ)) :
    NoCrossingGlobalCertificate B := by
  exact noCrossingBeyondYstar_of_bounds h1 h2

end Dominance
end CaseB
end Lehmer