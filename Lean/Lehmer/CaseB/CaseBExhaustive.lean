-- FILE: Lean/Lehmer/CaseB/CaseBExhaustive.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Main : def thm
- Lehmer.CaseB.CaseBClass : def
- Lehmer.CaseB.TerminalBridge : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Main
import Lehmer.CaseB.CaseBClass
import Lehmer.CaseB.TerminalBridge

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Exactness of the Case B audit window.

The audit-facing window `WindowB` is definitionally identical to the
mathematical Case B class `InCaseB`.
-/
theorem windowB_exact (n : ℕ) :
    WindowB n ↔ InCaseB n := by
  rfl

/--
Exhaustive terminal coverage of the exact Case B window.

Every Lehmer candidate lying in the exact Case B window canonically produces
the terminal structural data consumed by the final contradiction layer.
-/
theorem windowB_exhaustive
    {n : ℕ}
    (hL : LehmerComposite n)
    (hW : WindowB n) :
    CaseBTerminalData n := by
  simpa [WindowB] using
    caseB_terminal_supply_data_of_candidate hL hW

end CaseB
end Lehmer