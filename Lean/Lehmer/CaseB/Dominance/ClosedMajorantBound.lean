-- FILE: Lean/Lehmer/CaseB/Dominance/ClosedMajorantBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Parameters : def
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.MajorantMc : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.MajorantMc

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Closed witness-side majorant assumption.

This is the Lean-facing closed numerical inequality used to dominate the Case B
supply bound by the closed majorant `Mc`.  It packages exactly the quantity that
appears after expanding `M(y) = W(y) + Kmax,B(y)` in the current code base.
-/
def ClosedWitnessBound {C : Context} (A : WitnessAccounting C) : Prop :=
  (witnessBudget A : ℝ) + (KmaxB C.y : ℝ) ≤ Mc C.y

@[simp] theorem ClosedWitnessBound_def {C : Context} (A : WitnessAccounting C) :
    ClosedWitnessBound A =
      ((witnessBudget A : ℝ) + (KmaxB C.y : ℝ) ≤ Mc C.y) := rfl

/--
A closed witness-side majorant immediately yields the closed-majorant interface
for the current Case B supply bound.
-/
theorem hasClosedMajorantOfAccounting_of_closedWitnessBound
    {C : Context} (A : WitnessAccounting C)
    (hclosed : ClosedWitnessBound A) :
    HasClosedMajorantOfAccounting A := by
  rw [HasClosedMajorantOfAccounting_def]
  rw [MboundOfAccounting_cast_eq]
  exact hclosed

/--
Elimination form of the previous theorem.
-/
theorem closedMajorantOfAccounting_bound_of_closedWitnessBound
    {C : Context} (A : WitnessAccounting C)
    (hclosed : ClosedWitnessBound A) :
    ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y := by
  exact hasClosedMajorantOfAccounting_of_closedWitnessBound A hclosed

/--
Natural-number domination form of the closed witness-side majorant.
-/
theorem MboundOfAccounting_le_McNat_of_closedWitnessBound
    {C : Context} (A : WitnessAccounting C)
    (hclosed : ClosedWitnessBound A) :
    MboundOfAccounting A ≤ McNat C.y := by
  exact MboundOfAccounting_le_McNat_of_closedMajorant A
    (hasClosedMajorantOfAccounting_of_closedWitnessBound A hclosed)

/--
If a terminal Case B support satisfies the paper-style supply bound and the
corresponding witness accounting satisfies the closed witness-side majorant,
then the terminal support is bounded by the closed majorant `McNat`.
-/
theorem supportCard_le_McNat_of_supplyBound
    {C : Context} (A : WitnessAccounting C)
    (hsupply : HasSupplyBound C A)
    (hclosed : ClosedWitnessBound A) :
    supportCard C.S ≤ McNat C.y := by
  have hM : supportCard C.S ≤ MboundOfAccounting A := hsupply
  exact le_trans hM (MboundOfAccounting_le_McNat_of_closedWitnessBound A hclosed)

/--
Package form for a `SupplyPackage`.

This is the exact bridge from the saturation/supply layer to the dominance
layer: once the accounting side is closed numerically, the terminal support is
bounded by the closed majorant.
-/
theorem terminal_support_le_McNat_of_supplyPackage
    {C : Context} (P : SupplyPackage C)
    (hclosed : ClosedWitnessBound P.accounting) :
    supportCard P.terminal.S ≤ McNat C.y := by
  have hlevel : P.terminal.y = C.y := P.hlevel
  have hs : supportCard P.terminal.S ≤ McNat P.terminal.y := by
    exact supportCard_le_McNat_of_supplyBound P.accounting P.hsupply hclosed
  simpa [hlevel] using hs

/--
Real-valued form of the terminal closed-majorant bound for a `SupplyPackage`.
-/
theorem terminal_support_cast_le_Mc_of_supplyPackage
    {C : Context} (P : SupplyPackage C)
    (hclosed : ClosedWitnessBound P.accounting) :
    (supportCard P.terminal.S : ℝ) ≤ McNat C.y := by
  exact_mod_cast terminal_support_le_McNat_of_supplyPackage P hclosed

end CaseB
end Lehmer