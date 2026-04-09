-- FILE: Lean/Lehmer/CaseB/Main.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.Defs : def thm
- Lehmer.Pivot.SupportInterface : def thm
- Lehmer.Pivot.LowerBoundAbstract : thm
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Parameters : def thm
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
- Lehmer.CaseB.Saturation.GenericChains : def thm
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.CaseB.Saturation.EntanglementScarcity : def thm
- Lehmer.CaseB.Saturation.SaturatedSupportBound : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.MajorantMc : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : def thm
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.CaseB.Dominance.Contradiction : def thm
-/

import Lehmer.Basic.Defs
import Lehmer.Pivot.Defs
import Lehmer.Pivot.SupportInterface
import Lehmer.Pivot.LowerBoundAbstract
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.GenericChains
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.CaseB.Saturation.EntanglementScarcity
import Lehmer.CaseB.Saturation.SaturatedSupportBound
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.MajorantMc
import Lehmer.CaseB.Dominance.ClosedMajorantBound
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.Contradiction

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot

/--
Canonical Case B context attached to a global candidate `n`.

This is the minimal unification point between the global Lehmer candidate
architecture and the local Case B `Context`-based dominance contradiction:
- the Case B level is the canonical pivot `pivotVal n`,
- the Case B support is the prime support of `n`.
-/
def candidateContext (n : ℕ) : Context where
  y := pivotVal n
  S := primeSupport n

@[simp] theorem candidateContext_y (n : ℕ) :
    (candidateContext n).y = pivotVal n := rfl

@[simp] theorem candidateContext_S (n : ℕ) :
    (candidateContext n).S = primeSupport n := rfl

@[simp] theorem candidateContext_level (n : ℕ) :
    level (candidateContext n) = pivotVal n := rfl

@[simp] theorem candidateContext_support (n : ℕ) :
    support (candidateContext n) = primeSupport n := rfl

/--
The canonical candidate context satisfies the pivot-demand inequality.

This is exactly the abstract pivot lower bound already proved in the pivot
layer, rewritten in the `Context` language used by Case B.
-/
theorem meetsPivotDemand_candidate
    {n : ℕ} (hL : LehmerComposite n) :
    MeetsPivotDemand (candidateContext n) := by
  change mreq (pivotVal n) ≤ supportCard (primeSupport n)
  simpa [omega_def] using
    (pivot_lower_bound_at_pivotVal_of_LehmerComposite hL)

/--
If the canonical pivot lies beyond `Ystar`, then the canonical candidate
context is in the local large-pivot regime.
-/
theorem largePivotRegime_candidate_of_le
    {n : ℕ} (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n) :
    LargePivotRegime (candidateContext n) := by
  refine ⟨?_, ?_⟩
  · simpa using hy
  · change Nat.Prime (pivotVal n)
    simpa [pivotVal] using Nat.minFac_prime hL.ne_one

/--
Global no-crossing immediately specializes to the canonical candidate context
once the pivot lies beyond `Ystar`.
-/
theorem noCrossingAt_candidate_of_global
    {n : ℕ} (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hno : NoCrossingBeyondYstar) :
    NoCrossingAt (candidateContext n).y := by
  change NoCrossingAt (pivotVal n)
  apply hno (pivotVal n) hy
  simpa [pivotVal] using Nat.minFac_prime hL.ne_one

/--
Expanded inequality form of the previous specialization.
-/
theorem candidate_M_lt_mreq_of_global
    {n : ℕ} (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hno : NoCrossingBeyondYstar) :
    M (candidateContext n).y < (mreq (candidateContext n).y : ℝ) := by
  exact noCrossingAt_candidate_of_global hL hy hno

/--
Terminal Case B contradiction for a Lehmer composite, assuming the canonical
candidate context carries a supply/accounting package and the uniform
no-crossing statement is available.
-/
theorem caseB_contradiction_candidate_of_supplyPackage
    {n : ℕ}
    (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hno : NoCrossingBeyondYstar)
    (hsupply :
      ∃ A : WitnessAccounting (candidateContext n),
        HasSupplyBound (candidateContext n) A ∧ ClosedWitnessBound A) :
    False := by
  exact caseB_contradiction_of_largePivot
    (C := candidateContext n)
    (meetsPivotDemand_candidate hL)
    hsupply
    (largePivotRegime_candidate_of_le hL hy)
    hno

/--
Conditional exclusion form:
if the canonical candidate context admits a supply/accounting package and
uniform no-crossing holds, then a Lehmer composite cannot have pivot value at
least `Ystar`.
-/
theorem pivotVal_lt_Ystar_of_supplyPackage
    {n : ℕ}
    (hL : LehmerComposite n)
    (hno : NoCrossingBeyondYstar)
    (hsupply :
      ∃ A : WitnessAccounting (candidateContext n),
        HasSupplyBound (candidateContext n) A ∧ ClosedWitnessBound A) :
    pivotVal n < Ystar := by
  by_contra hnot
  have hy : Ystar ≤ pivotVal n := le_of_not_lt hnot
  exact caseB_contradiction_candidate_of_supplyPackage hL hy hno hsupply

end CaseB
end Lehmer