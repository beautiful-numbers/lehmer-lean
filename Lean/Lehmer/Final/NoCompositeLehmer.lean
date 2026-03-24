-- FILE: Lean/Lehmer/Final/NoCompositeLehmer.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Final.MainTheorem : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Final.MainTheorem

namespace Lehmer
namespace Final

open Lehmer.Basic

/--
Readable wrapper theorem: under terminal closure of the remaining range-based
pipeline branches, there is no composite integer satisfying Lehmer's
divisibility condition.

At the current refactor stage, Case A is already closed mathematically; the
exported final interface therefore asks for closure of the legacy small-pivot
range together with the untouched Case B / intermediate / Case C range branches.
-/
theorem no_composite_Lehmer_of_pipeline_closure
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InCaseB n → False)
    (hcloseI : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InIntermediate n → False)
    (hcloseC : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InCaseC n → False)
    {n : ℕ} :
    ¬ LehmerComposite n := by
  exact no_LehmerComposite_of_pipeline_closure
    hcloseSmallA hcloseB hcloseI hcloseC

/--
Pointwise contradiction form of the previous theorem.
-/
theorem LehmerComposite_implies_false_of_pipeline_closure
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InCaseB n → False)
    (hcloseI : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InIntermediate n → False)
    (hcloseC : ∀ {n : ℕ}, LehmerComposite n → Pipeline.InCaseC n → False)
    {n : ℕ} :
    LehmerComposite n → False := by
  intro hL
  exact no_composite_Lehmer_of_pipeline_closure
    hcloseSmallA hcloseB hcloseI hcloseC hL

end Final
end Lehmer