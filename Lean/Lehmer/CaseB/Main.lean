-- FILE: Lean/Lehmer/CaseB/Main.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.Defs : def thm
- Lehmer.Pivot.SupportInterface : def thm
- Lehmer.Pivot.CaseAContradiction : def thm
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Parameters : def thm
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.LocalCompleteness : def thm
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
- Lehmer.CaseB.CaseBTerminalBridge : def thm
- Lehmer.CaseB.CaseBContradiction : def thm
-/

import Lehmer.Basic.Defs
import Lehmer.Pivot.Defs
import Lehmer.Pivot.SupportInterface
import Lehmer.Pivot.CaseAContradiction
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.LocalCompleteness
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
import Lehmer.CaseB.CaseBTerminalBridge
import Lehmer.CaseB.CaseBContradiction

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot
open Dominance

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

theorem candidateContext_nonSaturated_of_descentEligible
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n)) :
    ContextNonSaturated (candidateContext n) := by
  exact nonSaturated_of_descentEligible_local hC

theorem candidateContext_nonempty_of_descentEligible
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n)) :
    (candidateContext n).S.Nonempty := by
  exact nonempty_of_descentEligible_local hC

theorem candidate_localGenericEntangled_boundary
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n)) :
    ContextPurelyGeneric (candidateContext n) ∨
      ∃ p : ℕ, EntangledPrime (candidateContext n).S p (candidateContext n).y := by
  exact purelyGeneric_or_exists_entangledPrime_of_descentEligible
    (candidateContext n) hC

theorem candidate_localGenericEntangled_boundary_explicit
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n)) :
    PurelyGenericSupport (primeSupport n) (pivotVal n) ∨
      ∃ p : ℕ, EntangledPrime (primeSupport n) p (pivotVal n) := by
  simpa [candidateContext_y, candidateContext_S, ContextPurelyGeneric, PurelyGenericSupport]
    using candidate_localGenericEntangled_boundary (n := n) hC

structure CandidateLocalBoundary (n : ℕ) where
  boundary :
    ContextPurelyGeneric (candidateContext n) ∨
      ∃ p : ℕ, EntangledPrime (candidateContext n).S p (candidateContext n).y

def candidateLocalBoundary_of_descentEligible
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n)) :
    CandidateLocalBoundary n :=
  { boundary := candidate_localGenericEntangled_boundary (n := n) hC }

theorem candidateLocalBoundary_of_descentEligible_spec
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n)) :
    ContextPurelyGeneric (candidateContext n) ∨
      ∃ p : ℕ, EntangledPrime (candidateContext n).S p (candidateContext n).y := by
  exact (candidateLocalBoundary_of_descentEligible hC).boundary

theorem candidate_exists_entangledPrime_of_not_purelyGeneric
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n))
    (hnot : ¬ ContextPurelyGeneric (candidateContext n)) :
    ∃ p : ℕ, EntangledPrime (candidateContext n).S p (candidateContext n).y := by
  rcases candidate_localGenericEntangled_boundary (n := n) hC with hpg | hent
  · exact False.elim (hnot hpg)
  · exact hent

theorem candidate_exists_entangledPrime_of_not_purelyGeneric_explicit
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n))
    (hnot : ¬ PurelyGenericSupport (primeSupport n) (pivotVal n)) :
    ∃ p : ℕ, EntangledPrime (primeSupport n) p (pivotVal n) := by
  simpa [candidateContext_y, candidateContext_S, ContextPurelyGeneric, PurelyGenericSupport]
    using candidate_exists_entangledPrime_of_not_purelyGeneric (n := n) hC hnot

theorem candidate_purelyGeneric_of_no_entangledPrime
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n))
    (hno :
      ¬ ∃ p : ℕ, EntangledPrime (candidateContext n).S p (candidateContext n).y) :
    ContextPurelyGeneric (candidateContext n) := by
  rcases candidate_localGenericEntangled_boundary (n := n) hC with hpg | hent
  · exact hpg
  · exact False.elim (hno hent)

theorem candidate_purelyGeneric_of_no_entangledPrime_explicit
    {n : ℕ}
    (hC : ContextDescentEligible (candidateContext n))
    (hno : ¬ ∃ p : ℕ, EntangledPrime (primeSupport n) p (pivotVal n)) :
    PurelyGenericSupport (primeSupport n) (pivotVal n) := by
  simpa [candidateContext_y, candidateContext_S, ContextPurelyGeneric, PurelyGenericSupport]
    using candidate_purelyGeneric_of_no_entangledPrime (n := n) hC hno

/--
The canonical candidate context satisfies the pivot-demand inequality.

At the current architecture stage, the pivot-side demand is the Case A-local
threshold `caseAMreq`, reused here only as the demand object consumed by the
Case B pivot-side contradiction.
-/
theorem meetsPivotDemand_candidate
    {n : ℕ} (hL : LehmerComposite n) :
    MeetsPivotDemand (candidateContext n) := by
  change caseAMreq (pivotVal n) ≤ supportCard (primeSupport n)
  simpa [omega_def] using
    (caseAMreq_le_omega_of_LehmerComposite hL)

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
    have hn : n ≠ 1 := by
      intro h1
      have h2 : (2 : ℕ) ≤ 1 := by
        simpa [h1] using hL.2.1
      omega
    simpa [pivotVal] using Nat.minFac_prime hn

/--
Pivot-side no-crossing specialized to the canonical candidate context.

This is the exact local inequality consumed by the current terminal
contradiction file.
-/
theorem candidate_Mc_lt_caseAMreq
    {n : ℕ}
    (hno : Mc (pivotVal n) < (caseAMreq (pivotVal n) : ℝ)) :
    Mc (candidateContext n).y < (caseAMreq (candidateContext n).y : ℝ) := by
  change Mc (pivotVal n) < (caseAMreq (pivotVal n) : ℝ)
  exact hno

/--
Terminal Case B contradiction for a Lehmer composite, assuming the canonical
candidate context carries a supply/accounting package and the pivot-side
no-crossing inequality is available at the canonical pivot.
-/
theorem caseB_contradiction_candidate_of_supplyPackage
    {n : ℕ}
    (hL : LehmerComposite n)
    (hy : Ystar ≤ pivotVal n)
    (hno : Mc (pivotVal n) < (caseAMreq (pivotVal n) : ℝ))
    (hsupply :
      ∃ A : WitnessAccounting (candidateContext n),
        HasSupplyBound (candidateContext n) A ∧ ClosedWitnessBound A) :
    False := by
  exact caseB_contradiction_of_largePivot
    (C := candidateContext n)
    (meetsPivotDemand_candidate hL)
    hsupply
    (largePivotRegime_candidate_of_le hL hy)
    (candidate_Mc_lt_caseAMreq hno)

/--
Conditional exclusion form:
if the canonical candidate context admits a supply/accounting package and
the pivot-side no-crossing inequality holds, then a Lehmer composite cannot
have pivot value at least `Ystar`.
-/
theorem pivotVal_lt_Ystar_of_supplyPackage
    {n : ℕ}
    (hL : LehmerComposite n)
    (hno : Mc (pivotVal n) < (caseAMreq (pivotVal n) : ℝ))
    (hsupply :
      ∃ A : WitnessAccounting (candidateContext n),
        HasSupplyBound (candidateContext n) A ∧ ClosedWitnessBound A) :
    pivotVal n < Ystar := by
  by_contra hnot
  have hy : Ystar ≤ pivotVal n := Nat.le_of_not_lt hnot
  exact caseB_contradiction_candidate_of_supplyPackage hL hy hno hsupply

/--
Global-candidate packaging of the enriched terminal bridge input for the
structural Case B contradiction.
-/
structure CandidateTerminalBridgeInput
    (B : ClosedBudgetFunctions) (n : ℕ) where
  supply : SupplyBridgePackage (candidateContext n)
  hy : Ystar ≤ pivotVal n
  hprime : Nat.Prime (pivotVal n)
  hpivot : caseAMreq (pivotVal n) ≤ supportCard (primeSupport n)
  hstruct : supportCard (primeSupport n) ≤ closedStructuralMajorant B (pivotVal n)

/--
Convert the global-candidate enriched bridge input to the local-context bridge
input consumed by the structural terminal contradiction layer.
-/
def candidateTerminalBridgeInput_to_context
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    CaseBTerminalBridgeInput B (candidateContext n) :=
  { supply := I.supply
    hy := by
      simpa [candidateContext_y] using I.hy
    hprime := by
      simpa [candidateContext_y] using I.hprime
    hpivot := by
      simpa [candidateContext_y, candidateContext_S] using I.hpivot
    hstruct := by
      simpa [candidateContext_y, candidateContext_S] using I.hstruct }

/--
The canonical structural terminal data attached to a candidate-level enriched
bridge input.
-/
def candidateTerminalData
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    CaseBTerminalData B :=
  caseBTerminalData_of_bridgeInput
    (candidateTerminalBridgeInput_to_context I)

@[simp] theorem candidateTerminalData_y
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    (candidateTerminalData I).y = pivotVal n := by
  simp [candidateTerminalData, candidateTerminalBridgeInput_to_context]

@[simp] theorem candidateTerminalData_S
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    (candidateTerminalData I).S = primeSupport n := by
  simp [candidateTerminalData, candidateTerminalBridgeInput_to_context]

/--
Structural Case B contradiction for a candidate global input, via the new
terminal bridge.
-/
theorem caseB_contradiction_candidate_of_supplyBridgePackage
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_terminalBridgeInput
    (candidateTerminalBridgeInput_to_context I)
    hno

/--
Conditional exclusion form via the structural terminal bridge:
if every proof of `Ystar ≤ pivotVal n` yields a candidate-level enriched bridge
input, then the pivot value must lie below `Ystar`.
-/
theorem pivotVal_lt_Ystar_of_supplyBridgePackage
    {B : ClosedBudgetFunctions} {n : ℕ}
    (hno : NoCrossingGlobalCertificate B)
    (hsupply :
      ∀ _ : Ystar ≤ pivotVal n,
        CandidateTerminalBridgeInput B n) :
    pivotVal n < Ystar := by
  by_contra hnot
  have hy : Ystar ≤ pivotVal n := Nat.le_of_not_lt hnot
  exact caseB_contradiction_candidate_of_supplyBridgePackage
    (hsupply hy)
    hno

/--
Packaged candidate-level contradiction data for the structural route.
-/
structure CandidateContradictionBridgePackage
    (B : ClosedBudgetFunctions) (n : ℕ) where
  input : CandidateTerminalBridgeInput B n
  hno : NoCrossingGlobalCertificate B

/--
Canonical packaged contradiction data from a candidate-level enriched bridge
input and a global no-crossing certificate.
-/
def candidateContradictionBridgePackage_of_input
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n)
    (hno : NoCrossingGlobalCertificate B) :
    CandidateContradictionBridgePackage B n :=
  { input := I
    hno := hno }

/--
Contradiction from the packaged candidate-level structural route.
-/
theorem false_of_candidateContradictionBridgePackage
    {B : ClosedBudgetFunctions} {n : ℕ}
    (P : CandidateContradictionBridgePackage B n) :
    False := by
  exact caseB_contradiction_candidate_of_supplyBridgePackage
    P.input
    P.hno

/--
The terminal context carried by a candidate-level enriched bridge input stays at
the candidate pivot level.
-/
theorem candidateTerminalBridgeInput_supply_level
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    I.supply.terminal.y = pivotVal n := by
  simpa [candidateContext_y] using I.supply.hlevel

/--
The terminal context carried by a candidate-level enriched bridge input is
locked.
-/
theorem candidateTerminalBridgeInput_supply_locked
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    SSLock I.supply.terminal :=
  I.supply.hlock

/--
The candidate-level enriched bridge input carries the local classified supply
bound on the canonical candidate context.
-/
theorem candidateTerminalBridgeInput_local_supply
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    HasSupplyBound (candidateContext n) I.supply.localAccounting :=
  I.supply.hlocalSupply

/--
The candidate-level enriched bridge input carries the honest cumulative supply
bound on the canonical candidate context.
-/
theorem candidateTerminalBridgeInput_cumulative_supply
    {B : ClosedBudgetFunctions} {n : ℕ}
    (I : CandidateTerminalBridgeInput B n) :
    HasCumulativeSupplyBound (candidateContext n) I.supply.cumulativeWitnessSet :=
  I.supply.hcumulativeSupply

end CaseB
end Lehmer