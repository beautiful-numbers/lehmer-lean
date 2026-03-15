-- FILE: Lean/Lehmer/CaseC/Certificate/Format.lean
import Lehmer.Prelude

namespace Lehmer
namespace CaseC
namespace Certificate

/--
The syntactic kind of a certificate node in the Case C witness layer.

For MVP-4, this is kept intentionally lightweight: it records only the
high-level role played by a node in the certificate tree.
-/
inductive NodeKind where
  | terminal
  | gatepass
  | split
  | excluded
  | residual
  deriving DecidableEq, Repr

/--
A minimal guard / prefix descriptor attached to a certificate node.

At MVP-4, we model it as a list of natural numbers. Later refinements may
replace this with a richer state-prefix structure once the residual machine
is connected.
-/
abbrev Guard := List ℕ

/--
A minimal local justification payload.

For MVP-4 this is just a textual tag naming the local reason attached to the
node. Later files may refine this into a structured justification datatype.
-/
abbrev Justification := String

/--
A local descent measure attached to a certificate node.

For MVP-4 this is just a natural-number placeholder for the expected
decreasing quantity used by the checker.
-/
abbrev Measure := ℕ

/--
A priority label used to order child records.

For MVP-4 this is a natural number; smaller values can later be interpreted
as higher priority if needed by the checker semantics.
-/
abbrev Priority := ℕ

/--
The minimal raw format of a certificate node.

This is the core syntactic object used by the later record semantics,
coverage, and checker layers.
-/
structure NodeFormat where
  kind : NodeKind
  guard : Guard
  priority : Priority
  children : List ℕ
  justification : Justification
  measure : Measure
  deriving Repr

/--
Accessor-style alias for the node kind.
-/
abbrev nodeKind (N : NodeFormat) : NodeKind :=
  N.kind

/--
Accessor-style alias for the node guard.
-/
abbrev nodeGuard (N : NodeFormat) : Guard :=
  N.guard

/--
Accessor-style alias for the node priority.
-/
abbrev nodePriority (N : NodeFormat) : Priority :=
  N.priority

/--
Accessor-style alias for the node children.
-/
abbrev nodeChildren (N : NodeFormat) : List ℕ :=
  N.children

/--
Accessor-style alias for the node justification.
-/
abbrev nodeJustification (N : NodeFormat) : Justification :=
  N.justification

/--
Accessor-style alias for the node measure.
-/
abbrev nodeMeasure (N : NodeFormat) : Measure :=
  N.measure

@[simp] theorem nodeKind_def (N : NodeFormat) :
    nodeKind N = N.kind := rfl

@[simp] theorem nodeGuard_def (N : NodeFormat) :
    nodeGuard N = N.guard := rfl

@[simp] theorem nodePriority_def (N : NodeFormat) :
    nodePriority N = N.priority := rfl

@[simp] theorem nodeChildren_def (N : NodeFormat) :
    nodeChildren N = N.children := rfl

@[simp] theorem nodeJustification_def (N : NodeFormat) :
    nodeJustification N = N.justification := rfl

@[simp] theorem nodeMeasure_def (N : NodeFormat) :
    nodeMeasure N = N.measure := rfl

/--
Terminal nodes have no children in the intended certificate format.
This is kept as a semantic predicate rather than built into the structure.
-/
def IsTerminalShape (N : NodeFormat) : Prop :=
  N.kind = NodeKind.terminal → N.children = []

/--
Split nodes are intended to branch.
This is a minimal shape predicate used later by the checker.
-/
def IsSplitShape (N : NodeFormat) : Prop :=
  N.kind = NodeKind.split → N.children ≠ []

/--
A raw-format node is locally well-formed if its coarse syntactic shape agrees
with its kind.
-/
def WellFormedFormat (N : NodeFormat) : Prop :=
  IsTerminalShape N ∧ IsSplitShape N

@[simp] theorem IsTerminalShape_def (N : NodeFormat) :
    IsTerminalShape N = (N.kind = NodeKind.terminal → N.children = []) := rfl

@[simp] theorem IsSplitShape_def (N : NodeFormat) :
    IsSplitShape N = (N.kind = NodeKind.split → N.children ≠ []) := rfl

@[simp] theorem WellFormedFormat_def (N : NodeFormat) :
    WellFormedFormat N = (IsTerminalShape N ∧ IsSplitShape N) := rfl

/--
A terminal node with empty children is well-formed at the format level.
-/
theorem wellFormed_terminal
    (g : Guard) (p : Priority) (j : Justification) (m : Measure) :
    WellFormedFormat
      { kind := NodeKind.terminal
        guard := g
        priority := p
        children := []
        justification := j
        measure := m } := by
  constructor
  · intro hkind
    rfl
  · intro hkind
    cases hkind

/--
A split node with at least one child satisfies the split-shape condition.
-/
theorem splitShape_of_children_nonempty
    (N : NodeFormat)
    (hkind : N.kind = NodeKind.split)
    (hchildren : N.children ≠ []) :
    IsSplitShape N := by
  intro hkind'
  simpa [hkind] using hchildren

end Certificate
end CaseC
end Lehmer