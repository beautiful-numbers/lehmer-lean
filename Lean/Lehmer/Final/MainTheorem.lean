-- FILE: Lean/Lehmer/Final/MainTheorem.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.Main : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.Main

namespace Lehmer
namespace Final

open Lehmer.Basic
open Lehmer.Pipeline

/--
Main theorem exported from the pipeline layer.

At the current transition stage of the refactor, the final contradiction is
exposed through the range-based terminal pipeline interface for the still
untouched branches, together with the already completed mathematical closure of
Case A.

Concretely, it is enough to know that:
- the legacy small-pivot range closes;
- the unchanged Case B range closes;
- the unchanged intermediate range closes;
- the unchanged Case C range closes.
-/
theorem main_theorem_of_pipeline_closure
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    (hcloseI : ∀ {n : ℕ}, LehmerComposite n → InIntermediate n → False)
    (hcloseC : ∀ {n : ℕ}, LehmerComposite n → InCaseC n → False)
    {n : ℕ} :
    LehmerComposite n → False := by
  intro hL
  let I_bridge : IntermediateBridgeData :=
    { terminal := fun hL_I hI => hcloseI hL_I hI }
  let C_bridge : CaseCBridgeData :=
    { handled := fun hL_C hC => False.elim (hcloseC hL_C hC) }
  exact pipeline_closes_all_cases_by_range_assumptions
    I_bridge C_bridge hcloseSmallA hcloseB hL

/--
Equivalent negated formulation of the final theorem.
-/
theorem no_LehmerComposite_of_pipeline_closure
    (hcloseSmallA : ∀ {n : ℕ}, LehmerComposite n → InSmallPivotRange n → False)
    (hcloseB : ∀ {n : ℕ}, LehmerComposite n → InCaseB n → False)
    (hcloseI : ∀ {n : ℕ}, LehmerComposite n → InIntermediate n → False)
    (hcloseC : ∀ {n : ℕ}, LehmerComposite n → InCaseC n → False)
    {n : ℕ} :
    ¬ LehmerComposite n := by
  intro hL
  exact main_theorem_of_pipeline_closure
    hcloseSmallA hcloseB hcloseI hcloseC hL

end Final
end Lehmer