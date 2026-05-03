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
Exported no-composite-Lehmer interface.

This theorem records the final assembly form: the range split and the branch
closure endpoints combine to rule out every Lehmer composite.
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
