-- FILE: Lean/Lehmer/CaseB/CaseBContradiction.lean

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.CaseAMreq
import Lehmer.CaseB.Dominance.ClosedStructuralMajorant
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.CaseB.Dominance.NoCrossingGlobal
import Lehmer.CaseB.CaseBTerminalBridge

namespace Lehmer
namespace CaseB

open Dominance
open Lehmer.Pivot

/-- Local terminal contradiction from a no-crossing statement at the terminal
level. -/
theorem false_of_terminalData_and_local_noCrossing
    {B : ClosedBudgetFunctions}
    (D : CaseBTerminalData B)
    (hlocal : NoCrossingAt B D.y) :
    False := by
  have hsupportR : (D.S.card : ℝ) ≤ M B D.y := by
    simpa [M] using
      (show (D.S.card : ℝ) ≤ (closedStructuralMajorant B D.y : ℝ) by
        exact_mod_cast D.hsupport)
  have hpivotR : (caseAMreq D.y : ℝ) ≤ (D.S.card : ℝ) := by
    exact_mod_cast D.hpivot
  have hmreq : M B D.y < (caseAMreq D.y : ℝ) := by
    simpa [NoCrossingAt_def] using hlocal
  have hlt : (D.S.card : ℝ) < (caseAMreq D.y : ℝ) := by
    exact lt_of_le_of_lt hsupportR hmreq
  exact (not_lt_of_ge hpivotR) hlt

/-- Global terminal contradiction from the global no-crossing certificate. -/
theorem false_of_terminalData
    {B : ClosedBudgetFunctions}
    (D : CaseBTerminalData B)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  have hlocal : NoCrossingAt B D.y :=
    noCrossingAt_of_global hno D.hy D.hprime
  exact false_of_terminalData_and_local_noCrossing D hlocal

/-- Non-structured terminal contradiction. -/
theorem false_of_bounds_and_noCrossing
    {B : ClosedBudgetFunctions} {y : ℕ} {S : Finset ℕ}
    (hy : Dominance.Ystar ≤ y)
    (hprime : Nat.Prime y)
    (hpivot : caseAMreq y ≤ S.card)
    (hsupport : S.card ≤ closedStructuralMajorant B y)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  let D : CaseBTerminalData B :=
    @CaseBTerminalData.mk B y S hy hprime hpivot hsupport
  exact false_of_terminalData D hno

/-- Contradiction from the enriched terminal bridge input. -/
theorem false_of_terminalBridgeInput
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_terminalData
    (caseBTerminalData_of_bridgeInput I)
    hno

/-- Contradiction from the packaged enriched terminal bridge. -/
theorem false_of_terminalBridgePackage
    {B : ClosedBudgetFunctions} {C : Context}
    (P : CaseBTerminalBridgePackage B C)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_terminalData P.terminalData hno

/-- Contradiction directly from the enriched strategy-1 supply bridge package. -/
theorem false_of_supplyBridgePackage
    {B : ClosedBudgetFunctions} {C : Context}
    (P : SupplyBridgePackage C)
    (hy : Dominance.Ystar ≤ C.y)
    (hprime : Nat.Prime C.y)
    (hpivot : caseAMreq C.y ≤ Lehmer.Basic.supportCard C.S)
    (hstruct : Lehmer.Basic.supportCard C.S ≤ closedStructuralMajorant B C.y)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  let I : CaseBTerminalBridgeInput B C :=
    @CaseBTerminalBridgeInput.mk B C P hy hprime hpivot hstruct
  exact false_of_terminalBridgeInput I hno

/-- Legacy contradiction directly from the older strategy-1 supply package. -/
theorem false_of_supplyPackage
    {B : ClosedBudgetFunctions} {C : Context}
    (P : SupplyPackage C)
    (hy : Dominance.Ystar ≤ C.y)
    (hprime : Nat.Prime C.y)
    (hpivot : caseAMreq C.y ≤ Lehmer.Basic.supportCard C.S)
    (hstruct : Lehmer.Basic.supportCard C.S ≤ closedStructuralMajorant B C.y)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  let I : CaseBTerminalLegacyBridgeInput B C :=
    @CaseBTerminalLegacyBridgeInput.mk B C P hy hprime hpivot hstruct
  exact false_of_terminalData
    (caseBTerminalData_of_legacyBridgeInput I)
    hno

/-- Packaged terminal contradiction data for the enriched bridge. -/
structure CaseBTerminalContradictionPackage
    (B : ClosedBudgetFunctions) (C : Context) where
  bridge : CaseBTerminalBridgeInput B C
  hno : NoCrossingGlobalCertificate B

/-- Canonical contradiction package from bridge input. -/
def caseBTerminalContradictionPackage_of_bridgeInput
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C)
    (hno : NoCrossingGlobalCertificate B) :
    CaseBTerminalContradictionPackage B C :=
  { bridge := I
    hno := hno }

/-- Contradiction from the packaged enriched bridge data. -/
theorem false_of_terminalContradictionPackage
    {B : ClosedBudgetFunctions} {C : Context}
    (P : CaseBTerminalContradictionPackage B C) :
    False := by
  exact false_of_terminalBridgeInput P.bridge P.hno

/-- Canonical contradiction package from an enriched strategy-1 supply bridge
package and the remaining terminal hypotheses. -/
def caseBTerminalContradictionPackage_of_supplyBridgePackage
    {B : ClosedBudgetFunctions} {C : Context}
    (P : SupplyBridgePackage C)
    (hy : Dominance.Ystar ≤ C.y)
    (hprime : Nat.Prime C.y)
    (hpivot : caseAMreq C.y ≤ Lehmer.Basic.supportCard C.S)
    (hstruct : Lehmer.Basic.supportCard C.S ≤ closedStructuralMajorant B C.y)
    (hno : NoCrossingGlobalCertificate B) :
    CaseBTerminalContradictionPackage B C :=
  { bridge := @CaseBTerminalBridgeInput.mk B C P hy hprime hpivot hstruct
    hno := hno }

/-- Package-based contradiction from the enriched strategy-1 supply bridge
package. -/
theorem false_of_supplyBridgePackage_via_package
    {B : ClosedBudgetFunctions} {C : Context}
    (P : SupplyBridgePackage C)
    (hy : Dominance.Ystar ≤ C.y)
    (hprime : Nat.Prime C.y)
    (hpivot : caseAMreq C.y ≤ Lehmer.Basic.supportCard C.S)
    (hstruct : Lehmer.Basic.supportCard C.S ≤ closedStructuralMajorant B C.y)
    (hno : NoCrossingGlobalCertificate B) :
    False := by
  exact false_of_terminalContradictionPackage
    (caseBTerminalContradictionPackage_of_supplyBridgePackage
      P hy hprime hpivot hstruct hno)

/-- The enriched bridge input preserves the starting level on the strategy-1
terminal side. -/
theorem terminalBridgeInput_supply_terminal_level
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    I.supply.terminal.y = C.y :=
  I.supply.hlevel

/-- The enriched bridge input ends at a locked strategy-1 terminal context. -/
theorem terminalBridgeInput_supply_terminal_locked
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    SSLock I.supply.terminal :=
  I.supply.hlock

/-- The enriched bridge input carries the local classified supply bound. -/
theorem terminalBridgeInput_supply_local
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    HasSupplyBound C I.supply.localAccounting :=
  I.supply.hlocalSupply

/-- The enriched bridge input carries the honest cumulative supply bound. -/
theorem terminalBridgeInput_supply_cumulative
    {B : ClosedBudgetFunctions} {C : Context}
    (I : CaseBTerminalBridgeInput B C) :
    HasCumulativeSupplyBound C I.supply.cumulativeWitnessSet :=
  I.supply.hcumulativeSupply

end CaseB
end Lehmer