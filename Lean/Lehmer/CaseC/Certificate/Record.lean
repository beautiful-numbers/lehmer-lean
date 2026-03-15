-- FILE: Lean/Lehmer/CaseC/Certificate/Record.lean
import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Format

namespace Lehmer
namespace CaseC
namespace Certificate

/--
A certificate record is a formatted node together with its own identifier.

For MVP-4, child references are stored as identifiers in the underlying
`NodeFormat`, so the record itself only needs to package an id with the raw
node data.
-/
structure Record where
  id : ℕ
  data : NodeFormat
  deriving Repr

/--
Accessor-style alias for the record identifier.
-/
abbrev recordId (R : Record) : ℕ :=
  R.id

/--
Accessor-style alias for the underlying node format.
-/
abbrev recordData (R : Record) : NodeFormat :=
  R.data

/--
Accessor-style alias for the record kind.
-/
abbrev recordKind (R : Record) : NodeKind :=
  R.data.kind

/--
Accessor-style alias for the record guard.
-/
abbrev recordGuard (R : Record) : Guard :=
  R.data.guard

/--
Accessor-style alias for the record priority.
-/
abbrev recordPriority (R : Record) : Priority :=
  R.data.priority

/--
Accessor-style alias for the child references of the record.
-/
abbrev recordChildren (R : Record) : List ℕ :=
  R.data.children

/--
Accessor-style alias for the local justification tag.
-/
abbrev recordJustification (R : Record) : Justification :=
  R.data.justification

/--
Accessor-style alias for the local descent measure.
-/
abbrev recordMeasure (R : Record) : Measure :=
  R.data.measure

@[simp] theorem recordId_def (R : Record) :
    recordId R = R.id := rfl

@[simp] theorem recordData_def (R : Record) :
    recordData R = R.data := rfl

@[simp] theorem recordKind_def (R : Record) :
    recordKind R = R.data.kind := rfl

@[simp] theorem recordGuard_def (R : Record) :
    recordGuard R = R.data.guard := rfl

@[simp] theorem recordPriority_def (R : Record) :
    recordPriority R = R.data.priority := rfl

@[simp] theorem recordChildren_def (R : Record) :
    recordChildren R = R.data.children := rfl

@[simp] theorem recordJustification_def (R : Record) :
    recordJustification R = R.data.justification := rfl

@[simp] theorem recordMeasure_def (R : Record) :
    recordMeasure R = R.data.measure := rfl

/--
The underlying format-level well-formedness of a record.
-/
def WellFormedRecordFormat (R : Record) : Prop :=
  WellFormedFormat R.data

@[simp] theorem WellFormedRecordFormat_def (R : Record) :
    WellFormedRecordFormat R = WellFormedFormat R.data := rfl

/--
A terminal record has no children in the intended certificate syntax.
-/
def IsTerminalRecord (R : Record) : Prop :=
  R.data.kind = NodeKind.terminal

/--
A split record is a branching record in the intended certificate syntax.
-/
def IsSplitRecord (R : Record) : Prop :=
  R.data.kind = NodeKind.split

@[simp] theorem IsTerminalRecord_def (R : Record) :
    IsTerminalRecord R = (R.data.kind = NodeKind.terminal) := rfl

@[simp] theorem IsSplitRecord_def (R : Record) :
    IsSplitRecord R = (R.data.kind = NodeKind.split) := rfl

/--
A record is locally shape-valid if its underlying format is well-formed.
-/
def ShapeValid (R : Record) : Prop :=
  WellFormedRecordFormat R

@[simp] theorem ShapeValid_def (R : Record) :
    ShapeValid R = WellFormedRecordFormat R := rfl

/--
A terminal record with empty children is shape-valid.
-/
theorem shapeValid_terminal
    (i : ℕ) (g : Guard) (p : Priority) (j : Justification) (m : Measure) :
    ShapeValid
      { id := i
        data :=
          { kind := NodeKind.terminal
            guard := g
            priority := p
            children := []
            justification := j
            measure := m } } := by
  exact wellFormed_terminal g p j m

/--
A split record with nonempty children satisfies the split-shape condition.
-/
theorem splitShape_record_of_children_nonempty
    (R : Record)
    (hkind : recordKind R = NodeKind.split)
    (hchildren : recordChildren R ≠ []) :
    IsSplitShape R.data := by
  exact splitShape_of_children_nonempty R.data hkind hchildren

/--
Two records are id-disjoint if they do not share the same identifier.
This lightweight relation is useful later when formulating global certificate
well-formedness.
-/
def IdDisjoint (R₁ R₂ : Record) : Prop :=
  R₁.id ≠ R₂.id

@[simp] theorem IdDisjoint_def (R₁ R₂ : Record) :
    IdDisjoint R₁ R₂ = (R₁.id ≠ R₂.id) := rfl

end Certificate
end CaseC
end Lehmer