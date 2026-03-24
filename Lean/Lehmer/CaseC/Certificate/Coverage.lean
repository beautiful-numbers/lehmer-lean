-- FILE: Lean/Lehmer/CaseC/Certificate/Coverage.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Priority : def thm
-/

import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority

namespace Lehmer
namespace CaseC
namespace Certificate

/--
A child record is declared by a parent record if its identifier appears in the
parent's child-reference list.
-/
def IsDeclaredChild (parent child : Record) : Prop :=
  recordId child ∈ recordChildren parent

@[simp] theorem IsDeclaredChild_def (parent child : Record) :
    IsDeclaredChild parent child = (recordId child ∈ recordChildren parent) := rfl

/--
A supplied list of child records matches the parent's declared child ids.
-/
def ChildrenMatchIds (parent : Record) (children : List Record) : Prop :=
  children.map recordId = recordChildren parent

@[simp] theorem ChildrenMatchIds_def (parent : Record) (children : List Record) :
    ChildrenMatchIds parent children =
      (children.map recordId = recordChildren parent) := rfl

/--
A minimal local coverage predicate for a parent record and a supplied child list.

For the current checker-facing layer, local coverage means:
- the supplied child list matches the declared child ids;
- the child list respects the local priority discipline.
-/
def LocallyCovered (parent : Record) (children : List Record) : Prop :=
  ChildrenMatchIds parent children ∧ ChildrenRespectPriority parent children

@[simp] theorem LocallyCovered_def (parent : Record) (children : List Record) :
    LocallyCovered parent children =
      (ChildrenMatchIds parent children ∧ ChildrenRespectPriority parent children) := rfl

/--
A terminal record is locally covered by the empty child list.
-/
theorem locallyCovered_terminal_nil
    (R : Record) (_hterm : IsTerminalRecord R) (hchildren : recordChildren R = []) :
    LocallyCovered R [] := by
  constructor
  · simpa [ChildrenMatchIds] using hchildren.symm
  · exact childrenRespectPriority_nil_of_no_children R hchildren

/--
If a supplied child list matches the declared child ids and already satisfies
the priority discipline, then the parent is locally covered by that list.
-/
theorem locallyCovered_of_match_and_priority
    (parent : Record) (children : List Record)
    (hIds : ChildrenMatchIds parent children)
    (hPrio : ChildrenRespectPriority parent children) :
    LocallyCovered parent children := by
  exact ⟨hIds, hPrio⟩

/--
A child list is pairwise id-disjoint if distinct positions carry distinct ids.

This is a stronger auxiliary notion that may be used later by global layers,
but it is not part of the current local checker target.
-/
def PairwiseIdDisjoint (children : List Record) : Prop :=
  children.Pairwise IdDisjoint

@[simp] theorem PairwiseIdDisjoint_nil :
    PairwiseIdDisjoint [] := by
  simp [PairwiseIdDisjoint]

@[simp] theorem PairwiseIdDisjoint_singleton (R : Record) :
    PairwiseIdDisjoint [R] := by
  simp [PairwiseIdDisjoint]

/--
A stronger local coverage predicate adding id-disjointness of the supplied
children.

This notion is intentionally kept auxiliary: it is stronger than what the
current local checker directly tests.
-/
def WellCovered (parent : Record) (children : List Record) : Prop :=
  LocallyCovered parent children ∧ PairwiseIdDisjoint children

@[simp] theorem WellCovered_def (parent : Record) (children : List Record) :
    WellCovered parent children =
      (LocallyCovered parent children ∧ PairwiseIdDisjoint children) := rfl

/--
The empty child list is pairwise id-disjoint.
-/
theorem pairwiseIdDisjoint_nil :
    PairwiseIdDisjoint ([] : List Record) := by
  simp [PairwiseIdDisjoint]

/--
A terminal record with no children is well-covered by the empty child list.
-/
theorem wellCovered_terminal_nil
    (R : Record) (hterm : IsTerminalRecord R) (hchildren : recordChildren R = []) :
    WellCovered R [] := by
  refine ⟨locallyCovered_terminal_nil R hterm hchildren, ?_⟩
  exact pairwiseIdDisjoint_nil

/--
If the child ids match, the child list is priority-sorted, and the child ids
are pairwise disjoint, then the stronger local coverage condition holds.
-/
theorem wellCovered_of_ids_priority_disjoint
    (parent : Record) (children : List Record)
    (hIds : children.map recordId = recordChildren parent)
    (hPrio : PrioritySorted children)
    (hDisjoint : PairwiseIdDisjoint children) :
    WellCovered parent children := by
  refine ⟨?_, hDisjoint⟩
  exact locallyCovered_of_match_and_priority parent children hIds
    (childrenRespectPriority_of_ids_and_sorted parent children hIds hPrio)

end Certificate
end CaseC
end Lehmer