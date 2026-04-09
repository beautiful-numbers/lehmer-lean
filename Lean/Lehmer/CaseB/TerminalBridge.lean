-- FILE: Lean/Lehmer/CaseB/TerminalBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Dominance.Contradiction : def thm
- Lehmer.Pivot.Defs : def thm
- Lehmer.Pivot.SupportInterface : def thm
- Lehmer.Pivot.LowerBoundAbstract : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Dominance.Contradiction
import Lehmer.Pivot.Defs
import Lehmer.Pivot.SupportInterface
import Lehmer.Pivot.LowerBoundAbstract

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot

/--
Natural Case B context attached to a Lehmer candidate:
the level is the canonical pivot value, and the support is the prime support.
-/
def contextOfLehmer (n : ℕ) : Context where
  y := pivotVal n
  S := primeSupport n

@[simp] theorem contextOfLehmer_level (n : ℕ) :
    (contextOfLehmer n).y = pivotVal n := rfl

@[simp] theorem contextOfLehmer_support (n : ℕ) :
    (contextOfLehmer n).S = primeSupport n := rfl

/--
The support cardinality of the natural Case B context is exactly `omega n`.
-/
theorem supportCard_contextOfLehmer_eq_omega (n : ℕ) :
    supportCard (contextOfLehmer n).S = omega n := by
  simpa [contextOfLehmer] using (omega_def n).symm

/--
The natural Case B context attached to a Lehmer composite satisfies the pivot
demand inequality.
-/
theorem meetsPivotDemand_of_LehmerComposite
    {n : ℕ}
    (hL : LehmerComposite n) :
    MeetsPivotDemand (contextOfLehmer n) := by
  dsimp [MeetsPivotDemand, contextOfLehmer]
  simpa [omega_def] using
    (pivot_lower_bound_at_pivotVal_of_LehmerComposite hL)

/--
If the pivot value of a Lehmer composite lies beyond `Y*`, then the associated
natural Case B context is in the large-pivot regime.
-/
theorem largePivotRegime_of_ge_Ystar
    {n : ℕ}
    (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n) :
    LargePivotRegime (contextOfLehmer n) := by
  dsimp [LargePivotRegime, contextOfLehmer]
  refine ⟨hy, ?_⟩
  have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hL.2.1
  have hprime : Nat.Prime (Nat.minFac n) := Nat.minFac_prime (ne_of_gt hn)
  simpa [pivotVal] using hprime

/--
Terminal Case B contradiction for a Lehmer composite, assuming the natural
Case B context carries a supply/accounting package and the uniform no-crossing
statement is available.
-/
theorem caseB_contradiction_of_LehmerComposite_of_supplyPackage
    {n : ℕ}
    (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hno : NoCrossingBeyondYstar)
    (hsupply :
      ∃ A : WitnessAccounting (contextOfLehmer n),
        HasSupplyBound (contextOfLehmer n) A ∧ ClosedWitnessBound A) :
    False := by
  have hdemand : MeetsPivotDemand (contextOfLehmer n) :=
    meetsPivotDemand_of_LehmerComposite hL
  have hlarge : LargePivotRegime (contextOfLehmer n) :=
    largePivotRegime_of_ge_Ystar hL hy
  exact caseB_contradiction_of_largePivot
    (C := contextOfLehmer n)
    hdemand
    hsupply
    hlarge
    hno

/--
Conditional exclusion form:
if the natural Case B supply/accounting package exists and uniform no-crossing
holds, then a Lehmer composite cannot have pivot value at least `Y*`.
-/
theorem pivotVal_lt_Ystar_of_LehmerComposite_of_supplyPackage
    {n : ℕ}
    (hL : LehmerComposite n)
    (hno : NoCrossingBeyondYstar)
    (hsupply :
      ∃ A : WitnessAccounting (contextOfLehmer n),
        HasSupplyBound (contextOfLehmer n) A ∧ ClosedWitnessBound A) :
    pivotVal n < Ystar := by
  by_contra hnot
  have hy : Ystar ≤ pivotVal n := le_of_not_lt hnot
  exact caseB_contradiction_of_LehmerComposite_of_supplyPackage
    hL hy hno hsupply

end CaseB
end Lehmer