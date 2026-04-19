-- FILE: Lean/Lehmer/CaseB/CaseBTerminalBridge.lean

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.CaseAMreq
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.ClosedStructuralMajorant

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot
open Dominance

/-- Minimal terminal data consumed by the structural Case B contradiction. -/
structure CaseBTerminalData (B : ClosedBudgetFunctions) where
  y : ℕ
  S : Finset ℕ
  hy : Dominance.Ystar ≤ y
  hprime : Nat.Prime y
  hpivot : caseAMreq y ≤ S.card
  hsupport : S.card ≤ closedStructuralMajorant B y

/-- Enriched terminal bridge input from the stable strategy-1 output to the
structural terminal data consumed by strategy 2. -/
structure CaseBTerminalBridgeInput
    (B : ClosedBudgetFunctions) (C : Context) where
  supply : SupplyBridgePackage C
  hy : Dominance.Ystar ≤ C.y
  hprime : Nat.Prime C.y
  hpivot : caseAMreq C.y ≤ supportCard C.S
  hstruct : supportCard C.S ≤ closedStructuralMajorant B C.y

/-- Canonical conversion from enriched terminal bridge input to structural
terminal data. -/
def caseBTerminalData_of_bridgeInput
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    CaseBTerminalData B :=
  { y := C.y
    S := C.S
    hy := I.hy
    hprime := I.hprime
    hpivot := by
      simpa [supportCard] using I.hpivot
    hsupport := by
      simpa [supportCard] using I.hstruct }

@[simp] theorem caseBTerminalData_of_bridgeInput_y
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    (caseBTerminalData_of_bridgeInput I).y = C.y := rfl

@[simp] theorem caseBTerminalData_of_bridgeInput_S
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    (caseBTerminalData_of_bridgeInput I).S = C.S := rfl

/-- Explicit profile for the enriched terminal bridge. -/
structure CaseBTerminalBridgeProfile
    (B : ClosedBudgetFunctions) (C : Context) where
  supply : SupplyBridgePackage C
  hy : Dominance.Ystar ≤ C.y
  hprime : Nat.Prime C.y
  hpivot : caseAMreq C.y ≤ supportCard C.S
  hstruct : supportCard C.S ≤ closedStructuralMajorant B C.y
  terminalData : CaseBTerminalData B
  hterminalData :
    terminalData =
      caseBTerminalData_of_bridgeInput
        ({ supply := supply
           hy := hy
           hprime := hprime
           hpivot := hpivot
           hstruct := hstruct } : CaseBTerminalBridgeInput B C)

/-- Canonical bridge profile from enriched terminal bridge input. -/
def caseBTerminalBridgeProfile_of_input
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    CaseBTerminalBridgeProfile B C :=
  { supply := I.supply
    hy := I.hy
    hprime := I.hprime
    hpivot := I.hpivot
    hstruct := I.hstruct
    terminalData := caseBTerminalData_of_bridgeInput I
    hterminalData := rfl }

/-- Legacy terminal bridge input from the older strategy-1 supply output to
the structural terminal data consumed by strategy 2. -/
structure CaseBTerminalLegacyBridgeInput
    (B : ClosedBudgetFunctions) (C : Context) where
  supply : SupplyPackage C
  hy : Dominance.Ystar ≤ C.y
  hprime : Nat.Prime C.y
  hpivot : caseAMreq C.y ≤ supportCard C.S
  hstruct : supportCard C.S ≤ closedStructuralMajorant B C.y

/-- Canonical conversion from legacy terminal bridge input to structural
terminal data. -/
def caseBTerminalData_of_legacyBridgeInput
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalLegacyBridgeInput B C) :
    CaseBTerminalData B :=
  { y := C.y
    S := C.S
    hy := I.hy
    hprime := I.hprime
    hpivot := by
      simpa [supportCard] using I.hpivot
    hsupport := by
      simpa [supportCard] using I.hstruct }

@[simp] theorem caseBTerminalData_of_legacyBridgeInput_y
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalLegacyBridgeInput B C) :
    (caseBTerminalData_of_legacyBridgeInput I).y = C.y := rfl

@[simp] theorem caseBTerminalData_of_legacyBridgeInput_S
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalLegacyBridgeInput B C) :
    (caseBTerminalData_of_legacyBridgeInput I).S = C.S := rfl

/-- Existence API for structural terminal data from enriched bridge input. -/
theorem exists_caseBTerminalData_of_bridgeInput
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    ∃ _ : CaseBTerminalData B, True := by
  exact ⟨caseBTerminalData_of_bridgeInput I, trivial⟩

/-- Existence API for structural terminal data from legacy bridge input. -/
theorem exists_caseBTerminalData_of_legacyBridgeInput
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalLegacyBridgeInput B C) :
    ∃ _ : CaseBTerminalData B, True := by
  exact ⟨caseBTerminalData_of_legacyBridgeInput I, trivial⟩

/-- Packaged enriched bridge just before the structural contradiction layer. -/
structure CaseBTerminalBridgePackage
    (B : ClosedBudgetFunctions) (C : Context) where
  input : CaseBTerminalBridgeInput B C
  terminalData : CaseBTerminalData B
  hterminal : terminalData = caseBTerminalData_of_bridgeInput input

/-- Canonical packaged enriched bridge. -/
def caseBTerminalBridgePackage_of_input
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    CaseBTerminalBridgePackage B C :=
  { input := I
    terminalData := caseBTerminalData_of_bridgeInput I
    hterminal := rfl }

/-- The stable strategy-1 bridge package preserves the starting level at the
terminal context. -/
theorem supplyBridgePackage_terminal_level
    {C : Context} (P : SupplyBridgePackage C) :
    P.terminal.y = C.y := P.hlevel

/-- The stable strategy-1 bridge package ends at a locked terminal context. -/
theorem supplyBridgePackage_terminal_locked
    {C : Context} (P : SupplyBridgePackage C) :
    SSLock P.terminal := P.hlock

/-- The stable strategy-1 bridge package carries the local classified supply
bound. -/
theorem supplyBridgePackage_local_supply
    {C : Context} (P : SupplyBridgePackage C) :
    HasSupplyBound C P.localAccounting := P.hlocalSupply

/-- The stable strategy-1 bridge package carries the honest cumulative supply
bound. -/
theorem supplyBridgePackage_cumulative_supply
    {C : Context} (P : SupplyBridgePackage C) :
    HasCumulativeSupplyBound C P.cumulativeWitnessSet := P.hcumulativeSupply

end CaseB
end Lehmer