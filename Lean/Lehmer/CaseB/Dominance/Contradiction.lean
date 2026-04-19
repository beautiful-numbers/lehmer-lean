-- FILE: Lean/Lehmer/CaseB/Dominance/Contradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.MajorantMc : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : def thm
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.Pivot.CaseAMreq : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.MajorantMc
import Lehmer.CaseB.Dominance.ClosedMajorantBound
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.Pivot.CaseAMreq

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Pivot
open Dominance

/--
Case B pivot-demand predicate.

This is the Case B-side form of the pivot lower-bound demand:
the support size at level `y` is at least `caseAMreq y`.
-/
def MeetsPivotDemand (C : Context) : Prop :=
  caseAMreq C.y ≤ supportCard C.S

@[simp] theorem MeetsPivotDemand_def (C : Context) :
    MeetsPivotDemand C = (caseAMreq C.y ≤ supportCard C.S) := rfl

/--
Case B large-pivot regime.

This is the thresholded prime regime in which the no-crossing statement is
applied.
-/
def LargePivotRegime (C : Context) : Prop :=
  Dominance.Ystar ≤ C.y ∧ Nat.Prime C.y

@[simp] theorem LargePivotRegime_def (C : Context) :
    LargePivotRegime C = (Dominance.Ystar ≤ C.y ∧ Nat.Prime C.y) := rfl

/--
Terminal Case B contradiction from the four numerical ingredients:

- pivot demand: `caseAMreq(y) ≤ ω`,
- supply bound: `ω ≤ MboundOfAccounting`,
- closed majorant: `MboundOfAccounting ≤ Mc(y)`,
- no-crossing: `Mc(y) < caseAMreq(y)`.
-/
theorem contradiction_of_supply_closedMajorant_noCrossing
    (C : Context) (A : WitnessAccounting C)
    (hdemand : MeetsPivotDemand C)
    (hsupply : HasSupplyBound C A)
    (hclosed : ClosedWitnessBound A)
    (hcross : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  have hdemand_real : (caseAMreq C.y : ℝ) ≤ (supportCard C.S : ℝ) := by
    exact_mod_cast hdemand
  have hM : (supportCard C.S : ℝ) ≤ ((MboundOfAccounting A : ℕ) : ℝ) := by
    exact_mod_cast hsupply
  have hclosedM : ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y := by
    simpa [Mc] using
      (closedMajorantOfAccounting_bound_of_closedWitnessBound (A := A) hclosed)
  have hchain : (supportCard C.S : ℝ) < (caseAMreq C.y : ℝ) := by
    exact lt_of_le_of_lt (le_trans hM hclosedM) hcross
  exact (not_lt_of_ge hdemand_real) hchain

/--
Large-pivot version of the terminal Case B contradiction using the canonical
Mc-side no-crossing statement.
-/
theorem contradiction_of_supply_closedMajorant_largePivot
    (C : Context) (A : WitnessAccounting C)
    (hdemand : MeetsPivotDemand C)
    (hsupply : HasSupplyBound C A)
    (hclosed : ClosedWitnessBound A)
    (_hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact contradiction_of_supply_closedMajorant_noCrossing
    C A hdemand hsupply hclosed hno

/--
Paper-facing large-pivot contradiction.
-/
theorem caseB_contradiction_of_largePivot
    {C : Context}
    (hdemand : MeetsPivotDemand C)
    (hsupply : ∃ A : WitnessAccounting C, HasSupplyBound C A ∧ ClosedWitnessBound A)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  rcases hsupply with ⟨A, hA_supply, hA_closed⟩
  exact contradiction_of_supply_closedMajorant_largePivot
    C A hdemand hA_supply hA_closed hlarge hno

/--
Support-cardinality form of the terminal contradiction.
-/
theorem supportCard_contradiction_of_supply_closedMajorant_noCrossing
    (C : Context) (A : WitnessAccounting C)
    (hdemand : caseAMreq C.y ≤ supportCard C.S)
    (hsupply : supportCard C.S ≤ MboundOfAccounting A)
    (hclosed : ClosedWitnessBound A)
    (hcross : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  have hdemand_real : (caseAMreq C.y : ℝ) ≤ (supportCard C.S : ℝ) := by
    exact_mod_cast hdemand
  have hsupply_real : (supportCard C.S : ℝ) ≤ ((MboundOfAccounting A : ℕ) : ℝ) := by
    exact_mod_cast hsupply
  have hclosedM : ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y := by
    simpa [Mc] using
      (closedMajorantOfAccounting_bound_of_closedWitnessBound (A := A) hclosed)
  have hchain : (supportCard C.S : ℝ) < (caseAMreq C.y : ℝ) := by
    exact lt_of_le_of_lt (le_trans hsupply_real hclosedM) hcross
  exact (not_lt_of_ge hdemand_real) hchain

/--
Natural packaged form of the terminal Case B contradiction.
-/
structure CaseBContradictionData (C : Context) where
  accounting : WitnessAccounting C
  hdemand : MeetsPivotDemand C
  hsupply : HasSupplyBound C accounting
  hclosed : ClosedWitnessBound accounting
  hlarge : LargePivotRegime C
  hno : Mc C.y < (caseAMreq C.y : ℝ)

/--
A complete Case B contradiction package closes the context.
-/
theorem contradiction_of_data
    (C : Context) (D : CaseBContradictionData C) :
    False := by
  exact contradiction_of_supply_closedMajorant_largePivot
    C D.accounting D.hdemand D.hsupply D.hclosed D.hlarge D.hno

/--
Existential packaged form of the Case B contradiction.
-/
theorem contradiction_of_exists_data
    (C : Context)
    (hdemand : MeetsPivotDemand C)
    (hsupply : ∃ A : WitnessAccounting C, HasSupplyBound C A ∧ ClosedWitnessBound A)
    (hlarge : LargePivotRegime C)
    (hno : Mc C.y < (caseAMreq C.y : ℝ)) :
    False := by
  exact caseB_contradiction_of_largePivot hdemand hsupply hlarge hno

end CaseB
end Lehmer