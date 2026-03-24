-- FILE: Lean/Lehmer/CaseC/Certificate/CompletenessLocal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.Certificate.CheckerLocal : def thm
- Lehmer.CaseC.Certificate.SoundnessLocal : def thm
-/

import Lehmer.Prelude
import Lehmer.CaseC.Certificate.CheckerLocal
import Lehmer.CaseC.Certificate.SoundnessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

/--
Main local completeness theorem:
if a record is semantically locally valid, then the local checker accepts it.
-/
theorem validLocalRecord_implies_checkRecordLocal_true
    (R : Record) (children : List Record)
    (h : ValidLocalRecord R children) :
    checkRecordLocal R children = true := by
  exact checkRecordLocal_true_of_shape_and_local R children h.1 h.2

/--
The canonical terminal/no-child local instance is accepted by the local checker.
-/
theorem checkRecordLocal_true_of_valid_terminal_nil
    (i : ℕ) (g : Guard) (p : Priority) (j : Justification) (m : Measure) :
    checkRecordLocal
      { id := i
        data :=
          { kind := NodeKind.terminal
            guard := g
            priority := p
            children := []
            justification := j
            measure := m } }
      [] = true := by
  exact validLocalRecord_implies_checkRecordLocal_true _ _
    (validLocalRecord_terminal_nil i g p j m)

end Certificate
end CaseC
end Lehmer