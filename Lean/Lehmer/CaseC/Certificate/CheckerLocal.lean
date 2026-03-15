-- FILE: Lean/Lehmer/CaseC/Certificate/CheckerLocal.lean
import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority
import Lehmer.CaseC.Certificate.Coverage

namespace Lehmer
namespace CaseC
namespace Certificate

/--
Boolean shape check for a raw node format.

For MVP-4 this checks only the coarse syntactic constraints:
- terminal nodes must have no children;
- split nodes must have at least one child;
- all other node kinds are accepted at the raw format level.
-/
def checkFormat (N : NodeFormat) : Bool :=
  match N.kind with
  | NodeKind.terminal => N.children.isEmpty
  | NodeKind.split => not N.children.isEmpty
  | _ => true

/--
Boolean local format check for a certificate record.
-/
def checkRecordShape (R : Record) : Bool :=
  checkFormat R.data

/--
Boolean check that a list of records is priority-sorted.
-/
def checkPrioritySorted : List Record → Bool
  | [] => true
  | [_] => true
  | R₁ :: R₂ :: Rs =>
      decide (R₁.data.priority ≤ R₂.data.priority) &&
      checkPrioritySorted (R₂ :: Rs)

/--
Boolean local priority/coverage check against a supplied child list.
-/
def checkLocalChildren (R : Record) (children : List Record) : Bool :=
  (children.map recordId == recordChildren R) && checkPrioritySorted children

/--
Boolean local checker for a record together with a supplied child list.
-/
def checkRecordLocal (R : Record) (children : List Record) : Bool :=
  checkRecordShape R && checkLocalChildren R children

@[simp] theorem checkRecordShape_def (R : Record) :
    checkRecordShape R = checkFormat R.data := rfl

@[simp] theorem checkPrioritySorted_nil :
    checkPrioritySorted [] = true := rfl

@[simp] theorem checkPrioritySorted_singleton (R : Record) :
    checkPrioritySorted [R] = true := rfl

@[simp] theorem checkPrioritySorted_cons_cons (R₁ R₂ : Record) (Rs : List Record) :
    checkPrioritySorted (R₁ :: R₂ :: Rs) =
      (decide (R₁.data.priority ≤ R₂.data.priority) &&
        checkPrioritySorted (R₂ :: Rs)) := rfl

@[simp] theorem checkLocalChildren_def (R : Record) (children : List Record) :
    checkLocalChildren R children =
      ((children.map recordId == recordChildren R) && checkPrioritySorted children) := rfl

@[simp] theorem checkRecordLocal_def (R : Record) (children : List Record) :
    checkRecordLocal R children = (checkRecordShape R && checkLocalChildren R children) := rfl

/--
If a list is priority-sorted propositionally, then the boolean checker returns true.
-/
theorem checkPrioritySorted_true_of_sorted : ∀ children : List Record,
    PrioritySorted children → checkPrioritySorted children = true
  | [], _ => by
      simp [PrioritySorted, checkPrioritySorted]
  | [_], _ => by
      simp [PrioritySorted, checkPrioritySorted]
  | R₁ :: R₂ :: Rs, h => by
      simp [PrioritySorted] at h
      rcases h with ⟨h12, htail⟩
      have h12' : decide (R₁.data.priority ≤ R₂.data.priority) = true := by
        exact decide_eq_true h12
      have htail' : checkPrioritySorted (R₂ :: Rs) = true := by
        exact checkPrioritySorted_true_of_sorted (R₂ :: Rs) htail
      simp [checkPrioritySorted, h12', htail']

/--
If the boolean priority check succeeds, then the list is priority-sorted.
-/
theorem checkPrioritySorted_true_implies : ∀ children : List Record,
    checkPrioritySorted children = true → PrioritySorted children
  | [], _ => by
      simp [PrioritySorted]
  | [_], _ => by
      simp [PrioritySorted]
  | R₁ :: R₂ :: Rs, h => by
      by_cases h12raw : R₁.data.priority ≤ R₂.data.priority
      · have htailBool : checkPrioritySorted (R₂ :: Rs) = true := by
          simp [checkPrioritySorted, h12raw] at h
          exact h
        have htail : PrioritySorted (R₂ :: Rs) := by
          exact checkPrioritySorted_true_implies (R₂ :: Rs) htailBool
        have h12 : PriorityLe R₁ R₂ := by
          simpa [PriorityLe, recordPriority_def] using h12raw
        exact ⟨h12, htail⟩
      · simp [checkPrioritySorted, h12raw] at h

/--
If the declared child ids match and the supplied child list is priority-sorted,
then the local child check succeeds.
-/
theorem checkLocalChildren_true_of_valid
    (R : Record) (children : List Record)
    (hIds : ChildrenMatchIds R children)
    (hPrio : PrioritySorted children) :
    checkLocalChildren R children = true := by
  unfold checkLocalChildren ChildrenMatchIds at *
  rw [hIds]
  have hprio' : checkPrioritySorted children = true := by
    exact checkPrioritySorted_true_of_sorted children hPrio
  simp [hprio']

/--
Format correctness for terminal nodes with empty children.
-/
theorem checkFormat_terminal_true
    (g : Guard) (p : Priority) (j : Justification) (m : Measure) :
    checkFormat
      { kind := NodeKind.terminal
        guard := g
        priority := p
        children := []
        justification := j
        measure := m } = true := by
  simp [checkFormat]

/--
Format correctness for split nodes with a nonempty child list.
-/
theorem checkFormat_split_true
    (g : Guard) (p : Priority) (c : List ℕ) (j : Justification) (m : Measure)
    (hc : c ≠ []) :
    checkFormat
      { kind := NodeKind.split
        guard := g
        priority := p
        children := c
        justification := j
        measure := m } = true := by
  simp [checkFormat, List.isEmpty_eq_false_iff, hc]

/--
A terminal record with no children passes the local checker.
-/
theorem checkRecordLocal_terminal_nil
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
  simp [checkRecordLocal, checkRecordShape, checkFormat, checkLocalChildren,
    checkPrioritySorted]

/--
Stable MVP-4 placeholder: a locally well-covered record should pass the local
checker.
-/
theorem checkRecordLocal_true_placeholder
    (R : Record) (children : List Record)
    (h : WellCovered R children) :
    checkRecordLocal R children = true := by
  rcases h with ⟨hLocal, _hPairwise⟩
  rcases hLocal with ⟨hIds, hChildren⟩
  have hLocalChildren : checkLocalChildren R children = true := by
    exact checkLocalChildren_true_of_valid R children hIds hChildren.2
  sorry

end Certificate
end CaseC
end Lehmer