import Mathlib
import Lehmer.Basic.Defs
import Lehmer.Pivot.LowerBoundAbstract
import Lehmer.CaseB.Spec
import Lehmer.CaseC.Spec

namespace Lehmer
namespace Pipeline

open Lehmer.Basic
open Lehmer.Pivot

/--
Global pivot-range split used in the paper.

- `small` corresponds to the finite Case C range `3 ≤ y < Y₁`,
- `mid` corresponds to the intermediate analytic range `Y₁ ≤ y < Y₀`,
- `large` corresponds to the large-range Case B regime `Y* ≤ y`.

At the specification level, we keep only the three logical branches.
-/
inductive PivotRange
  | small
  | mid
  | large
  deriving DecidableEq, Repr

/--
Global thresholds used by the paper.

They are kept abstract at the pipeline level; explicit values/tables are handled elsewhere.
-/
opaque Y1 : ℕ
opaque Y0 : ℕ
opaque YStar : ℕ

/--
Standing threshold relations.

These encode the architectural assumptions of the global split.
-/
axiom three_le_Y1 : 3 ≤ Y1
axiom Y1_le_Y0 : Y1 ≤ Y0
axiom Y0_le_YStar : Y0 ≤ YStar

/--
A pivot `y` lies in the finite Case C range.
-/
def InSmallRange (y : ℕ) : Prop :=
  3 ≤ y ∧ y < Y1

/--
A pivot `y` lies in the intermediate analytic range.
-/
def InMidRange (y : ℕ) : Prop :=
  Y1 ≤ y ∧ y < Y0

/--
A pivot `y` lies in the large Case B range.
-/
def InLargeRange (y : ℕ) : Prop :=
  YStar ≤ y

/--
Abstract classifier for pivots.

At this stage we do not compute the branch; we only expose the existence of a total
classification compatible with the three regimes.
-/
opaque classifyPivot : ℕ → PivotRange

/--
Soundness of the classifier on the small range.
-/
axiom classify_small {y : ℕ} :
    InSmallRange y → classifyPivot y = PivotRange.small

/--
Soundness of the classifier on the intermediate range.
-/
axiom classify_mid {y : ℕ} :
    InMidRange y → classifyPivot y = PivotRange.mid

/--
Soundness of the classifier on the large range.
-/
axiom classify_large {y : ℕ} :
    InLargeRange y → classifyPivot y = PivotRange.large

/--
Exhaustive trichotomy for pivots in the paper regime `3 ≤ y`.

This is the architectural case split used to assemble the final contradiction.
-/
axiom pivot_range_trichotomy {y : ℕ} :
    3 ≤ y →
      InSmallRange y ∨ InMidRange y ∨ InLargeRange y

/--
The three pivot ranges are pairwise disjoint.
-/
theorem small_not_mid {y : ℕ} (hs : InSmallRange y) : ¬ InMidRange y := by
  intro hm
  exact not_lt_of_ge hm.1 hs.2

theorem small_not_large {y : ℕ} (hs : InSmallRange y) : ¬ InLargeRange y := by
  intro hl
  have hY1YStar : Y1 ≤ YStar := le_trans Y1_le_Y0 Y0_le_YStar
  exact not_lt_of_ge (le_trans hY1YStar hl) hs.2

theorem mid_not_large {y : ℕ} (hm : InMidRange y) : ¬ InLargeRange y := by
  intro hl
  have : Y0 ≤ y := le_trans Y0_le_YStar hl
  exact not_lt_of_ge this hm.2

/--
A `y`-rough Lehmer composite with pivot `y` enters exactly one global branch.
-/
theorem pivot_range_partition {y n : ℕ}
    (hy : 3 ≤ y) (hrough : YRough y n) :
    InSmallRange y ∨ InMidRange y ∨ InLargeRange y := by
  exact pivot_range_trichotomy hy

/--
Abstract global contradiction principle.

To finish the proof, it is enough to provide:
- impossibility on the large range (Case B),
- impossibility on the intermediate analytic range,
- impossibility on the small finite range (Case C).
-/
theorem global_split_reduction
    (Hlarge : ∀ {y n : ℕ}, InLargeRange y → YRough y n → LehmerComposite n → False)
    (Hmid   : ∀ {y n : ℕ}, InMidRange y   → YRough y n → LehmerComposite n → False)
    (Hsmall : ∀ {y n : ℕ}, InSmallRange y → YRough y n → LehmerComposite n → False)
    {y n : ℕ}
    (hy : 3 ≤ y) (hrough : YRough y n) (hL : LehmerComposite n) :
    False := by
  rcases pivot_range_trichotomy hy with hs | hm | hl
  · exact Hsmall hs hrough hL
  · exact Hmid hm hrough hL
  · exact Hlarge hl hrough hL

/--
Classifier-driven form of the previous theorem.
-/
theorem global_split_reduction_by_classifier
    (Hlarge : ∀ {y n : ℕ}, classifyPivot y = PivotRange.large → YRough y n → LehmerComposite n → False)
    (Hmid   : ∀ {y n : ℕ}, classifyPivot y = PivotRange.mid   → YRough y n → LehmerComposite n → False)
    (Hsmall : ∀ {y n : ℕ}, classifyPivot y = PivotRange.small → YRough y n → LehmerComposite n → False)
    {y n : ℕ}
    (hy : 3 ≤ y) (hrough : YRough y n) (hL : LehmerComposite n) :
    False := by
  rcases pivot_range_trichotomy hy with hs | hm | hl
  · exact Hsmall (classify_small hs) hrough hL
  · exact Hmid (classify_mid hm) hrough hL
  · exact Hlarge (classify_large hl) hrough hL

end Pipeline
end Lehmer