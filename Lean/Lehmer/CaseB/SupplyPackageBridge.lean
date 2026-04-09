-- FILE: Lean/Lehmer/CaseB/SupplyPackageBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.Defs : def thm
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Main : def thm
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Main
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.ClosedMajorantBound

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot

theorem caseB_contradiction_candidate_of_accounting
    {n : ℕ}
    (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hno : NoCrossingBeyondYstar)
    (A : WitnessAccounting (candidateContext n))
    (hsupply : HasSupplyBound (candidateContext n) A)
    (hclosed : ClosedWitnessBound A) :
    False := by
  have h_y_eq : (candidateContext n).y = pivotVal n := candidateContext_y n
  have h_S_eq : (candidateContext n).S = primeSupport n := candidateContext_S n

  have h_demand_ctx :
      mreq (candidateContext n).y ≤ supportCard (candidateContext n).S :=
    meetsPivotDemand_candidate hL

  have h_demand : mreq (pivotVal n) ≤ supportCard (primeSupport n) := by
    rwa [h_y_eq, h_S_eq] at h_demand_ctx

  have h_supply_ctx : supportCard (candidateContext n).S ≤ MboundOfAccounting A := by
    -- This line is correct iff `HasSupplyBound` unfolds to the raw inequality.
    simpa [HasSupplyBound] using hsupply

  have h_supply_bound : supportCard (primeSupport n) ≤ MboundOfAccounting A := by
    rwa [h_S_eq] at h_supply_ctx

  have h_le_nat : mreq (pivotVal n) ≤ MboundOfAccounting A :=
    le_trans h_demand h_supply_bound

  have h_le_real :
      ((mreq (pivotVal n) : ℕ) : ℝ) ≤ ((MboundOfAccounting A : ℕ) : ℝ) :=
    Nat.cast_le.mpr h_le_nat

  have h_closed_ctx :
      ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc (candidateContext n).y :=
    closedMajorantOfAccounting_bound_of_closedWitnessBound A hclosed

  have h_closed_majorant :
      ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc (pivotVal n) := by
    rwa [h_y_eq] at h_closed_ctx

  have h_demand_le_Mc :
      ((mreq (pivotVal n) : ℕ) : ℝ) ≤ Mc (pivotVal n) :=
    le_trans h_le_real h_closed_majorant

  have h_prime : Nat.Prime (pivotVal n) := by
    -- This line is correct iff `pivotVal` is definitionally `Nat.minFac`.
    simpa [pivotVal] using Nat.minFac_prime hL.ne_one

  have h_no_cross : Mc (pivotVal n) < ((mreq (pivotVal n) : ℕ) : ℝ) :=
    hno (pivotVal n) hy h_prime

  exact absurd h_demand_le_Mc (not_le_of_lt h_no_cross)

theorem pivotVal_lt_Ystar_of_accounting
    {n : ℕ}
    (hL : LehmerComposite n)
    (hno : NoCrossingBeyondYstar)
    (A : WitnessAccounting (candidateContext n))
    (hsupply : HasSupplyBound (candidateContext n) A)
    (hclosed : ClosedWitnessBound A) :
    pivotVal n < Ystar := by
  by_contra hnot
  have hy : Ystar ≤ pivotVal n := le_of_not_lt hnot
  exact caseB_contradiction_candidate_of_accounting hL hy hno A hsupply hclosed

end CaseB
end Lehmer