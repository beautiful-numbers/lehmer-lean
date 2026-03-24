-- FILE: Lean/Lehmer/CaseC/Certificate/SoundnessLocal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.CheckerLocal : def thm
-/

import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.CheckerLocal

namespace Lehmer
namespace CaseC
namespace Certificate

/--
A semantic local-validity predicate for a record together with a supplied child list.

At the current stage, local validity is stated exactly at the checker-facing level:
- raw format well-formedness;
- local coverage.
-/
def ValidLocalRecord (R : Record) (children : List Record) : Prop :=
  WellFormedRecordFormat R ∧ LocallyCovered R children

@[simp] theorem ValidLocalRecord_def (R : Record) (children : List Record) :
    ValidLocalRecord R children =
      (WellFormedRecordFormat R ∧ LocallyCovered R children) := rfl

/--
If the boolean raw-format checker succeeds, then the record shape is valid.
-/
theorem checkRecordShape_sound
    (R : Record)
    (h : checkRecordShape R = true) :
    WellFormedRecordFormat R := by
  cases R with
  | mk rid data =>
      cases data with
      | mk kind guard priority children justification measure =>
          cases kind
          · -- terminal
            have hchildren : children = [] := by
              simpa [checkRecordShape, checkFormat] using h
            constructor
            · intro _
              exact hchildren
            · intro hsplit
              cases hsplit
          · -- gatepass
            constructor <;> intro hkind <;> cases hkind
          · -- split
            have hchildren : children ≠ [] := by
              simpa [checkRecordShape, checkFormat, List.isEmpty_eq_false_iff] using h
            constructor
            · intro hterm
              cases hterm
            · intro _
              exact hchildren
          · -- excluded
            constructor <;> intro hkind <;> cases hkind
          · -- residual
            constructor <;> intro hkind <;> cases hkind

/--
If the boolean child checker succeeds, then the supplied children are locally covered.
-/
theorem checkLocalChildren_sound
    (R : Record) (children : List Record)
    (h : checkLocalChildren R children = true) :
    LocallyCovered R children := by
  have hsplit :
      children.map recordId = recordChildren R ∧
      checkPrioritySorted children = true := by
    simpa [checkLocalChildren] using h
  have hprio : ChildrenRespectPriority R children := by
    exact childrenRespectPriority_of_ids_and_sorted R children hsplit.1
      (checkPrioritySorted_true_implies children hsplit.2)
  exact locallyCovered_of_match_and_priority R children hsplit.1 hprio

/--
Main local soundness theorem:
if the local checker returns `true`, then the record is semantically valid
with respect to the supplied child list.
-/
theorem checkRecordLocal_sound
    (R : Record) (children : List Record)
    (h : checkRecordLocal R children = true) :
    ValidLocalRecord R children := by
  have hsplit : checkRecordShape R = true ∧ checkLocalChildren R children = true := by
    simpa [checkRecordLocal] using h
  exact ⟨
    checkRecordShape_sound R hsplit.1,
    checkLocalChildren_sound R children hsplit.2
  ⟩

/--
A terminal record with no children is locally valid.
-/
theorem validLocalRecord_terminal_nil
    (i : ℕ) (g : Guard) (p : Priority) (j : Justification) (m : Measure) :
    ValidLocalRecord
      { id := i
        data :=
          { kind := NodeKind.terminal
            guard := g
            priority := p
            children := []
            justification := j
            measure := m } }
      [] := by
  refine ⟨?_, ?_⟩
  · exact wellFormed_terminal g p j m
  · exact locallyCovered_terminal_nil
      { id := i
        data :=
          { kind := NodeKind.terminal
            guard := g
            priority := p
            children := []
            justification := j
            measure := m } }
      rfl rfl

/--
The local checker is sound on the canonical terminal/no-child example.
-/
theorem checkRecordLocal_sound_terminal_nil
    (i : ℕ) (g : Guard) (p : Priority) (j : Justification) (m : Measure) :
    ValidLocalRecord
      { id := i
        data :=
          { kind := NodeKind.terminal
            guard := g
            priority := p
            children := []
            justification := j
            measure := m } }
      [] := by
  exact checkRecordLocal_sound _ _ (checkRecordLocal_terminal_nil _ _ _ _ _)

end Certificate
end CaseC
end Lehmer