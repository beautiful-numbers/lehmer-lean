-- FILE: Lean/Lehmer/Pipeline/GlobalSplit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pivot.Defs : def thm
- Lehmer.Pivot.CaseAContradiction : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pivot.Defs
import Lehmer.Pivot.CaseAContradiction

namespace Lehmer
namespace Pipeline

open Lehmer.Basic

/--
Global branches of the pipeline-level classification.

This remains the normative taxonomic split used by the pipeline layer.
In the long-term architecture, each branch must consume a mathematically
defined branch predicate coming from the corresponding proof layer.
-/
inductive GlobalBranch
  | caseA
  | caseB
  | intermediate
  | caseC
  deriving DecidableEq, Repr

/--
Pipeline-facing pivot alias.

Unlike the MVP version, this is no longer an opaque pipeline-only object:
it is the canonical pivot imported from the pivot layer.
-/
def pivotOf (n : ℕ) : ℕ :=
  Lehmer.Pivot.pivotVal n

@[simp] theorem pivotOf_def (n : ℕ) :
    pivotOf n = Lehmer.Pivot.pivotVal n := rfl

/--
Global thresholds used by the range-based part of the pipeline split.

At this stage, B / intermediate / C still use the range taxonomy from the MVP
pipeline.  Only Case A has been upgraded to its mathematical pivot-contradiction
form.
-/
opaque YA : ℕ
opaque YC : ℕ
opaque YB : ℕ

/--
Standing threshold relations for the range-based part of the global split.
-/
axiom three_le_YA : 3 ≤ YA
axiom YA_le_YC : YA ≤ YC
axiom YC_le_YB : YC ≤ YB

/--
Legacy small-pivot range.

This is the old MVP "Case A range" kept explicitly as a separate notion so that
the range taxonomy for the remaining branches is not lost during the Case A
refactor.
-/
def InSmallPivotRange (n : ℕ) : Prop :=
  3 ≤ pivotOf n ∧ pivotOf n < YA

/--
Mathematical Case A branch.

This is no longer a pivot-range condition.  It is the actual pivot
contradiction imported from `Lehmer.Pivot.CaseAContradiction`.
-/
def InCaseA (n : ℕ) : Prop :=
  Lehmer.Pivot.InCaseA n

/--
A candidate lies in the global Case C branch when its pivot is in the second
range.
-/
def InCaseC (n : ℕ) : Prop :=
  YA ≤ pivotOf n ∧ pivotOf n < YC

/--
A candidate lies in the intermediate branch when its pivot is in the third
range.
-/
def InIntermediate (n : ℕ) : Prop :=
  YC ≤ pivotOf n ∧ pivotOf n < YB

/--
A candidate lies in the global Case B branch when its pivot is in the large
range.
-/
def InCaseB (n : ℕ) : Prop :=
  YB ≤ pivotOf n

@[simp] theorem InSmallPivotRange_def (n : ℕ) :
    InSmallPivotRange n = (3 ≤ pivotOf n ∧ pivotOf n < YA) := rfl

@[simp] theorem InCaseA_def (n : ℕ) :
    InCaseA n = Lehmer.Pivot.InCaseA n := rfl

@[simp] theorem InCaseC_def (n : ℕ) :
    InCaseC n = (YA ≤ pivotOf n ∧ pivotOf n < YC) := rfl

@[simp] theorem InIntermediate_def (n : ℕ) :
    InIntermediate n = (YC ≤ pivotOf n ∧ pivotOf n < YB) := rfl

@[simp] theorem InCaseB_def (n : ℕ) :
    InCaseB n = (YB ≤ pivotOf n) := rfl

/--
Audit-facing relation saying that a Lehmer candidate falls in a named global
branch.

Case A now uses its mathematical pivot contradiction.
-/
def FallsInGlobalBranch (n : ℕ) : GlobalBranch → Prop
  | .caseA => InCaseA n
  | .caseB => InCaseB n
  | .intermediate => InIntermediate n
  | .caseC => InCaseC n

@[simp] theorem FallsInGlobalBranch_caseA (n : ℕ) :
    FallsInGlobalBranch n GlobalBranch.caseA = InCaseA n := rfl

@[simp] theorem FallsInGlobalBranch_caseB (n : ℕ) :
    FallsInGlobalBranch n GlobalBranch.caseB = InCaseB n := rfl

@[simp] theorem FallsInGlobalBranch_intermediate (n : ℕ) :
    FallsInGlobalBranch n GlobalBranch.intermediate = InIntermediate n := rfl

@[simp] theorem FallsInGlobalBranch_caseC (n : ℕ) :
    FallsInGlobalBranch n GlobalBranch.caseC = InCaseC n := rfl

/--
Pipeline assumption: the canonical pivot attached to a Lehmer candidate is
always in the paper regime `3 ≤ y`.

This keeps the existing B / intermediate / C range split stable while Case A is
migrated to its mathematical closure form.
-/
axiom pivot_ge_three_of_LehmerComposite {n : ℕ} :
    LehmerComposite n → 3 ≤ pivotOf n

/--
Range trichotomy above the threshold `YA`.

This is the part of the old range split still used verbatim by Case C,
intermediate, and Case B.
-/
theorem pivot_range_trichotomy_from_YA {y : ℕ}
    (hy : YA ≤ y) :
    (YA ≤ y ∧ y < YC) ∨
    (YC ≤ y ∧ y < YB) ∨
    (YB ≤ y) := by
  by_cases hC : y < YC
  · exact Or.inl ⟨hy, hC⟩
  · have hYC : YC ≤ y := le_of_not_gt hC
    by_cases hB : y < YB
    · exact Or.inr <| Or.inl ⟨hYC, hB⟩
    · exact Or.inr <| Or.inr (le_of_not_gt hB)

/--
Legacy range quadrichotomy.

This is retained only as a range decomposition tool.  It is no longer the
definition of the mathematical Case A branch.
-/
theorem pivot_range_quadrichotomy {y : ℕ}
    (hy : 3 ≤ y) :
    (3 ≤ y ∧ y < YA) ∨
    (YA ≤ y ∧ y < YC) ∨
    (YC ≤ y ∧ y < YB) ∨
    (YB ≤ y) := by
  by_cases hA : y < YA
  · exact Or.inl ⟨hy, hA⟩
  · have hYA : YA ≤ y := le_of_not_gt hA
    rcases pivot_range_trichotomy_from_YA hYA with hC | hI | hB
    · exact Or.inr <| Or.inl hC
    · exact Or.inr <| Or.inr <| Or.inl hI
    · exact Or.inr <| Or.inr <| Or.inr hB

/--
Range-based coverage theorem for the old pivot interval split.

This theorem is intentionally kept separate from the new mathematical
`FallsInGlobalBranch ... caseA`, because Case A has been upgraded from a range
predicate to a genuine contradiction predicate.
-/
theorem global_range_split_exhaustive {n : ℕ}
    (h : LehmerComposite n) :
    InSmallPivotRange n ∨
    InCaseC n ∨
    InIntermediate n ∨
    InCaseB n := by
  have hy : 3 ≤ pivotOf n := pivot_ge_three_of_LehmerComposite h
  simpa [InSmallPivotRange, InCaseC, InIntermediate, InCaseB] using
    (pivot_range_quadrichotomy hy)

/--
Existential form of the range-only classification theorem.
-/
theorem every_LehmerComposite_is_range_classified {n : ℕ}
    (h : LehmerComposite n) :
    InSmallPivotRange n ∨
    InCaseC n ∨
    InIntermediate n ∨
    InCaseB n := by
  exact global_range_split_exhaustive h

/--
The legacy small-pivot range is disjoint from the Case C range.
-/
theorem smallPivotRange_not_caseC {n : ℕ}
    (hA : InSmallPivotRange n) :
    ¬ InCaseC n := by
  intro hC
  exact not_lt_of_ge hC.1 hA.2

/--
The legacy small-pivot range is disjoint from the intermediate range.
-/
theorem smallPivotRange_not_intermediate {n : ℕ}
    (hA : InSmallPivotRange n) :
    ¬ InIntermediate n := by
  intro hI
  have hAYC : YA ≤ YC := YA_le_YC
  exact not_lt_of_ge (le_trans hAYC hI.1) hA.2

/--
The legacy small-pivot range is disjoint from the Case B range.
-/
theorem smallPivotRange_not_caseB {n : ℕ}
    (hA : InSmallPivotRange n) :
    ¬ InCaseB n := by
  intro hB
  have hAYB : YA ≤ YB := le_trans YA_le_YC YC_le_YB
  exact not_lt_of_ge (le_trans hAYB hB) hA.2

/--
The Case C branch is disjoint from the intermediate branch.
-/
theorem caseC_not_intermediate {n : ℕ}
    (hC : InCaseC n) :
    ¬ InIntermediate n := by
  intro hI
  exact not_lt_of_ge hI.1 hC.2

/--
The Case C branch is disjoint from the Case B branch.
-/
theorem caseC_not_caseB {n : ℕ}
    (hC : InCaseC n) :
    ¬ InCaseB n := by
  intro hB
  have hCYB : YC ≤ YB := YC_le_YB
  exact not_lt_of_ge (le_trans hCYB hB) hC.2

/--
The intermediate branch is disjoint from the Case B branch.
-/
theorem intermediate_not_caseB {n : ℕ}
    (hI : InIntermediate n) :
    ¬ InCaseB n := by
  intro hB
  exact not_lt_of_ge hB hI.2

/--
Range-only formulation of the remaining range taxonomy exhaustivity.

This is the stable theorem for the untouched B / intermediate / C part of the
pipeline while Case A is being rebuilt mathematically.
-/
def RangeTaxonomyExhaustive : Prop :=
  ∀ n : ℕ, LehmerComposite n →
    InSmallPivotRange n ∨ InCaseC n ∨ InIntermediate n ∨ InCaseB n

@[simp] theorem RangeTaxonomyExhaustive_def :
    RangeTaxonomyExhaustive =
      (∀ n : ℕ, LehmerComposite n →
        InSmallPivotRange n ∨ InCaseC n ∨ InIntermediate n ∨ InCaseB n) := rfl

/--
Main range-only exhaustivity theorem for the still range-based part of the
pipeline taxonomy.
-/
theorem range_taxonomy_exhaustive :
    RangeTaxonomyExhaustive := by
  intro n h
  exact every_LehmerComposite_is_range_classified h

end Pipeline
end Lehmer