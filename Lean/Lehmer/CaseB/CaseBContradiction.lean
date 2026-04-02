-- FILE: Lean/Lehmer/CaseB/CaseBContradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Main : def thm
- Lehmer.CaseB.CaseBClass : def
- Lehmer.CaseB.TerminalBridge : def thm
- Lehmer.CaseB.Dominance.Contradiction : thm
- Lehmer.CaseB.Dominance.NoCrossing : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Main
import Lehmer.CaseB.CaseBClass
import Lehmer.CaseB.TerminalBridge
import Lehmer.CaseB.Dominance.Contradiction
import Lehmer.CaseB.Dominance.NoCrossing

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Terminal consumption of Case B local structural data.

The pivot demand and the large-pivot regime are derived directly from the
candidate and the Case B class, while the nontrivial terminal structural data
is provided by `CaseBTerminalData`.
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
Final contradiction for the full mathematical Case B class, once the terminal
structural data has been supplied.

At the current architecture stage, this is the sound no-hole form: the former
automatic production through `CaseBExhaustive` has been removed, so the
terminal data must be provided explicitly.
-/
theorem caseB_impossible
    {n : ℕ}
    (hL : LehmerComposite n)
    (hB : InCaseB n)
    (hD : CaseBTerminalData n)
    (hno : NoCrossingBeyondYstar) :
    False := by
  exact false_of_caseB_terminal_data hL hB hD hno

/--
Negated form of the terminal Case B contradiction, once the terminal structural
data has been supplied.
-/
theorem not_inCaseB_of_LehmerComposite
    {n : ℕ}
    (hL : LehmerComposite n)
    (hD : CaseBTerminalData n)
    (hno : NoCrossingBeyondYstar) :
    ¬ InCaseB n := by
  intro hB
  exact caseB_impossible hL hB hD hno

end CaseB
end Lehmer