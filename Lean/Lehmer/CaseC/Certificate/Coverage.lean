-- FILE: Lean/Lehmer/CaseC/Certificate/Coverage.lean
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

For MVP-4, local coverage means:
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
    (R : Record) (hterm : IsTerminalRecord R) (hchildren : recordChildren R = []) :
    LocallyCovered R [] := by
  constructor
  · simpa [ChildrenMatchIds, recordChildren_def] using hchildren.symm
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
This is a lightweight global sanity condition useful for later checker layers.
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
children. This is the form most convenient for the later global checker.
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
Stable MVP-4 placeholder: a syntactically valid child list produced by the
certificate layer should satisfy the intended local coverage condition.
-/
theorem wellCovered_placeholder
    (parent : Record) (children : List Record)
    (hIds : children.map recordId = recordChildren parent) :
    WellCovered parent children := by
  refine ⟨?_, ?_⟩
  · exact locallyCovered_of_match_and_priority parent children hIds
      (childrenRespectPriority_placeholder parent children hIds)
  · sorry

end Certificate
end CaseC
end Lehmer