-- FILE: Lean/Lehmer/CaseC/Certificate/SoundnessLocal.lean
import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.CheckerLocal

namespace Lehmer
namespace CaseC
namespace Certificate

/--
A semantic local-validity predicate for a record together with a supplied child list.

For MVP-4, local soundness is stated against:
- raw format well-formedness,
- local coverage,
- and the strengthened well-covered condition.
-/
def ValidLocalRecord (R : Record) (children : List Record) : Prop :=
  WellFormedRecordFormat R ∧ WellCovered R children

@[simp] theorem ValidLocalRecord_def (R : Record) (children : List Record) :
    ValidLocalRecord R children =
      (WellFormedRecordFormat R ∧ WellCovered R children) := rfl

/--
If the boolean raw-format checker succeeds, then the record shape is valid.

This is the local shape-soundness interface for MVP-4.
-/
theorem checkRecordShape_sound_placeholder
    (R : Record)
    (h : checkRecordShape R = true) :
    WellFormedRecordFormat R := by
  sorry

/--
If the boolean child checker succeeds, then the supplied children satisfy the
intended local coverage and priority discipline.

This is the local child-soundness interface for MVP-4.
-/
theorem checkLocalChildren_sound_placeholder
    (R : Record) (children : List Record)
    (h : checkLocalChildren R children = true) :
    WellCovered R children := by
  sorry

/--
Main local soundness theorem for the MVP-4 checker:
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
    checkRecordShape_sound_placeholder R hsplit.1,
    checkLocalChildren_sound_placeholder R children hsplit.2
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
  · exact wellCovered_terminal_nil
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