-- FILE: Lean/Lehmer/CaseB/CaseBContradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Main : def thm
- Lehmer.CaseB.CaseBClass : def
- Lehmer.CaseB.TerminalBridge : def thm
- Lehmer.CaseB.CaseBExhaustive : thm
- Lehmer.CaseB.Dominance.Contradiction : thm
- Lehmer.CaseB.Dominance.NoCrossing : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Main
import Lehmer.CaseB.TerminalBridge
import Lehmer.CaseB.CaseBExhaustive
import Lehmer.CaseB.Dominance.Contradiction
import Lehmer.CaseB.Dominance.NoCrossing

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Terminal consumption of Case B local structural data.

The pivot demand and the large-pivot regime are derived directly from the
candidate and the Case B class, while the nontrivial supply package is
provided by `CaseBTerminalData`.
-/
theorem false_of_caseB_terminal_data
    {n : ℕ}
    (hL : LehmerComposite n)
    (hW : WindowB n)
    (hD : CaseBTerminalData n)
    (hno : NoCrossingBeyondYstar) :
    False := by
  rcases hD with ⟨A, hSupply, hClosed⟩
  have hdemand : MeetsPivotDemand (candidateContext n) :=
    meetsPivotDemand_candidate hL
  have hlarge : LargePivotRegime (candidateContext n) :=
    largePivotRegime_candidate_of_le hL hW
  exact contradiction_of_supply_closedMajorant_largePivot
    (candidateContext n) A hdemand hSupply hClosed hlarge hno

/--
Final contradiction for the full mathematical Case B class.
-/
theorem caseB_impossible
    {n : ℕ}
    (hL : LehmerComposite n)
    (hB : InCaseB n)
    (hno : NoCrossingBeyondYstar) :
    False := by
  exact false_of_caseB_terminal_data hL hB
    (windowB_exhaustive hL hB) hno

/--
Negated form of the terminal Case B contradiction.
-/
theorem not_inCaseB_of_LehmerComposite
    {n : ℕ}
    (hL : LehmerComposite n)
    (hno : NoCrossingBeyondYstar) :
    ¬ InCaseB n := by
  intro hB
  exact caseB_impossible hL hB hno

end CaseB
end Lehmer