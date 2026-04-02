-- FILE: Lean/Lehmer/CaseB/TerminalBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Main : def thm
- Lehmer.CaseB.CaseBClass : def
- Lehmer.CaseB.Saturation.WitnessAccounting : def
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Main
import Lehmer.CaseB.CaseBClass
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

end CaseB
end Lehmer