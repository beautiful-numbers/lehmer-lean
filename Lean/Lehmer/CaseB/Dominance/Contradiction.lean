-- FILE: Lean/Lehmer/CaseB/Dominance/Contradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.MajorantMc : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : thm
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.Pivot.Mreq : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.MajorantMc
import Lehmer.CaseB.Dominance.ClosedMajorantBound
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.Pivot.Mreq

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot

/--
Case B pivot-demand predicate.

This is the Case B-side form of the pivot lower-bound demand:
the support size at level `y` is at least `mreq y`.
-/
def MeetsPivotDemand (C : Context) : Prop :=
  mreq C.y ≤ supportCard C.S

@[simp] theorem MeetsPivotDemand_def (C : Context) :
    MeetsPivotDemand C = (mreq C.y ≤ supportCard C.S) := rfl

/--
Case B large-pivot regime.

This is the thresholded prime regime in which the no-crossing statement is
applied.
-/
def LargePivotRegime (C : Context) : Prop :=
  Ystar ≤ C.y ∧ Nat.Prime C.y

@[simp] theorem LargePivotRegime_def (C : Context) :
    LargePivotRegime C = (Ystar ≤ C.y ∧ Nat.Prime C.y) := rfl

/--
Terminal Case B contradiction from the three ingredients:

- pivot demand: `mreq(y) ≤ ω`,
- supply bound: `ω ≤ M(y)`,
- closed majorant: `M(y) ≤ McNat(y)`,
- no-crossing: `McNat(y) < mreq(y)`.

This is the exact Case B contradiction pattern exported by the current Lean
architecture.
-/
theorem contradiction_of_supply_closedMajorant_noCrossing
    (C : Context) (A : WitnessAccounting C)
    (hdemand : MeetsPivotDemand C)
    (hsupply : HasSupplyBound C A)
    (hclosed : ClosedWitnessBound A)
    (hcross : NoCrossingAt C.y) :
    False := by
  have hM : supportCard C.S ≤ MboundOfAccounting A := hsupply
  have hMc : MboundOfAccounting A ≤ McNat C.y :=
    MboundOfAccounting_le_McNat_of_closedWitnessBound A hclosed
  have hcross' : McNat C.y < mreq C.y := hcross
  have hchain : supportCard C.S < mreq C.y := lt_of_le_of_lt (le_trans hM hMc) hcross'
  exact (not_lt_of_ge hdemand) hchain

/--
Large-pivot version of the terminal Case B contradiction using the uniform
no-crossing interface beyond `Y*`.
-/
theorem contradiction_of_supply_closedMajorant_largePivot
    (C : Context) (A : WitnessAccounting C)
    (hdemand : MeetsPivotDemand C)
    (hsupply : HasSupplyBound C A)
    (hclosed : ClosedWitnessBound A)
    (hlarge : LargePivotRegime C)
    (hno : NoCrossingBeyondYstar) :
    False := by
  have hcross : NoCrossingAt C.y := by
    exact hno C.y hlarge.1 hlarge.2
  exact contradiction_of_supply_closedMajorant_noCrossing C A hdemand hsupply hclosed hcross

/--
Support-cardinality form of the terminal contradiction.
-/
theorem supportCard_contradiction_of_supply_closedMajorant_noCrossing
    (C : Context) (A : WitnessAccounting C)
    (hdemand : mreq C.y ≤ supportCard C.S)
    (hsupply : supportCard C.S ≤ MboundOfAccounting A)
    (hclosed : ClosedWitnessBound A)
    (hcross : McNat C.y < mreq C.y) :
    False := by
  exact contradiction_of_supply_closedMajorant_noCrossing
    C A hdemand hsupply hclosed hcross

/--
Natural packaged form of the terminal Case B contradiction.
-/
structure CaseBContradictionData (C : Context) where
  accounting : WitnessAccounting C
  hdemand : MeetsPivotDemand C
  hsupply : HasSupplyBound C accounting
  hclosed : ClosedWitnessBound accounting
  hlarge : LargePivotRegime C

/--
A complete Case B contradiction package closes the context under the uniform
no-crossing interface.
-/
theorem contradiction_of_data
    (C : Context) (D : CaseBContradictionData C)
    (hno : NoCrossingBeyondYstar) :
    False := by
  exact contradiction_of_supply_closedMajorant_largePivot
    C D.accounting D.hdemand D.hsupply D.hclosed D.hlarge hno

end CaseB
end Lehmer