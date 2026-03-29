-- FILE: Lean/Lehmer/CaseB/TerminalBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Main : def thm
- Lehmer.CaseB.CaseBClass : def
- Lehmer.CaseB.TerminalExport : thm
- Lehmer.CaseB.Saturation.WitnessAccounting : def
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Main
import Lehmer.CaseB.CaseBClass
import Lehmer.CaseB.TerminalExport
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.ClosedMajorantBound

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Minimal terminal structural data exported by the principal Case B pipeline.

This is the minimal nontrivial output needed by the final Case B contradiction:
a witness-accounting object together with a closed structural supply package.
-/
def CaseBTerminalData (n : ℕ) : Prop :=
  ∃ A : WitnessAccounting (candidateContext n),
    HasSupplyBound (candidateContext n) A ∧
    ClosedWitnessBound A

@[simp] theorem CaseBTerminalData_def (n : ℕ) :
    CaseBTerminalData n =
      (∃ A : WitnessAccounting (candidateContext n),
        HasSupplyBound (candidateContext n) A ∧
        ClosedWitnessBound A) := rfl

/--
Canonical terminal structural export for the principal Case B pipeline.

This theorem is a pure bridge: it consumes the high-level candidate-side supply
package exported by `TerminalExport` and repackages it into the terminal data
format used by the final contradiction layer.
-/
theorem caseB_terminal_supply_data_of_candidate
    {n : ℕ}
    (hL : LehmerComposite n)
    (hB : InCaseB n) :
    CaseBTerminalData n := by
  rcases caseB_supplyPackage_candidate hL hB with ⟨P, hclosed⟩
  exact ⟨P.accounting, P.hsupply, hclosed⟩

end CaseB
end Lehmer