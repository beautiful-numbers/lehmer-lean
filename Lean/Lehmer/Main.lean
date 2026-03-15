-- FILE: Lean/Lehmer/Main.lean
import Lehmer.Prelude

import Lehmer.Basic.Defs
import Lehmer.Basic.Totient
import Lehmer.Basic.OddSquarefree

import Lehmer.Support.IncrementRatio
import Lehmer.Support.IncrementIdentity
import Lehmer.Support.PotentialP
import Lehmer.Support.PotentialP2

import Lehmer.CaseB.Spec
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Main

import Lehmer.CaseC.Main

namespace Lehmer

/-!
# Lehmer.Main

Root import for the current MVP-4 stage of the Lehmer formalization.

This file currently assembles:
- the MVP-1 basic layer,
- the MVP-2 support and Case B descent skeleton,
- the MVP-3 Case C gap-to-closure skeleton,
- the MVP-4 Case C certificate format, checker, and soundness layer.

It is intended to grow gradually as additional modules become stable.
-/

end Lehmer