-- FILE: Lean/Lehmer/CaseC/Certificate/Priority.lean
import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Record

namespace Lehmer
namespace CaseC
namespace Certificate

/--
A local priority relation on two records.

For MVP-4, smaller numeric priority means higher precedence.
-/
def PriorityLe (R₁ R₂ : Record) : Prop :=
  recordPriority R₁ ≤ recordPriority R₂

/--
Strict priority between two records.
-/
def PriorityLt (R₁ R₂ : Record) : Prop :=
  recordPriority R₁ < recordPriority R₂

@[simp] theorem PriorityLe_def (R₁ R₂ : Record) :
    PriorityLe R₁ R₂ = (recordPriority R₁ ≤ recordPriority R₂) := rfl

@[simp] theorem PriorityLt_def (R₁ R₂ : Record) :
    PriorityLt R₁ R₂ = (recordPriority R₁ < recordPriority R₂) := rfl

/--
A list of records is priority-sorted if priorities are nondecreasing.
This is the minimal global priority discipline used by the MVP-4 checker.
-/
def PrioritySorted : List Record → Prop
  | [] => True
  | [_] => True
  | R₁ :: R₂ :: Rs => PriorityLe R₁ R₂ ∧ PrioritySorted (R₂ :: Rs)

@[simp] theorem PrioritySorted_nil :
    PrioritySorted [] := by
  trivial

@[simp] theorem PrioritySorted_singleton (R : Record) :
    PrioritySorted [R] := by
  trivial

@[simp] theorem PrioritySorted_cons_cons {R₁ R₂ : Record} {Rs : List Record} :
    PrioritySorted (R₁ :: R₂ :: Rs) ↔
      PriorityLe R₁ R₂ ∧ PrioritySorted (R₂ :: Rs) := by
  rfl

/--
Every record is priority-compatible with itself.
-/
theorem priorityLe_refl (R : Record) :
    PriorityLe R R := by
  exact le_rfl

/--
Strict priority implies non-strict priority.
-/
theorem priorityLe_of_priorityLt {R₁ R₂ : Record}
    (h : PriorityLt R₁ R₂) :
    PriorityLe R₁ R₂ := by
  exact le_of_lt h

/--
If a head record has priority below the next one and the tail is sorted,
then the whole list is priority-sorted.
-/
theorem prioritySorted_of_head_tail {R₁ R₂ : Record} {Rs : List Record}
    (h12 : PriorityLe R₁ R₂)
    (hTail : PrioritySorted (R₂ :: Rs)) :
    PrioritySorted (R₁ :: R₂ :: Rs) := by
  exact ⟨h12, hTail⟩

/--
A local record-level predicate saying that the children of a record are listed
in nondecreasing priority order, relative to a supplied list of child records.
-/
def ChildrenRespectPriority (R : Record) (children : List Record) : Prop :=
  children.map recordId = recordChildren R ∧ PrioritySorted children

@[simp] theorem ChildrenRespectPriority_def (R : Record) (children : List Record) :
    ChildrenRespectPriority R children =
      (children.map recordId = recordChildren R ∧ PrioritySorted children) := rfl

/--
If a record has no children, then its child-priority condition is trivially
satisfied by the empty child list.
-/
theorem childrenRespectPriority_nil_of_no_children
    (R : Record) (h : recordChildren R = []) :
    ChildrenRespectPriority R [] := by
  constructor
  · simpa [recordChildren_def] using h.symm
  · simp

/--
Stable MVP-4 placeholder: a syntactically valid child list produced by the
certificate format should respect the declared priority discipline.
-/
theorem childrenRespectPriority_placeholder
    (R : Record) (children : List Record)
    (hIds : children.map recordId = recordChildren R) :
    ChildrenRespectPriority R children := by
  refine ⟨hIds, ?_⟩
  sorry

end Certificate
end CaseC
end Lehmer