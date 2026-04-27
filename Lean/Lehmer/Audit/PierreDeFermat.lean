-- FILE: Lean/Lehmer/Audit/PierreDeFermat.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Pipeline.GlobalSplit : def thm

FILE ROLE
Top-level global closure aggregator.

This file consumes the actual global pipeline range split:
- small pivot range
- Case C
- intermediate
- Case B

and turns it into a final contradiction statement.

Note:
the current pipeline split is range-based, not A/B/C-only.
So this file must aggregate the four real branches exported by
`Lehmer.Pipeline.GlobalSplit`.
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Audit

open Lehmer.Basic
open Lehmer.Pipeline

def PierreDeFermatStatement : Prop :=
  ∀ n : ℕ, LehmerComposite n → False

@[simp] theorem PierreDeFermatStatement_def :
    PierreDeFermatStatement =
      (∀ n : ℕ, LehmerComposite n → False) := rfl

/--
Pointwise global contradiction from the actual range split exported by
`Lehmer.Pipeline.GlobalSplit`.
-/
theorem pierreDeFermat_pointwise_of_range_closures
    {n : ℕ}
    (hL : LehmerComposite n)
    (hSmall : ∀ m : ℕ, InSmallPivotRange m → False)
    (hCaseC : ∀ m : ℕ, InCaseC m → False)
    (hIntermediate : ∀ m : ℕ, InIntermediate m → False)
    (hCaseB : ∀ m : ℕ, InCaseB m → False) :
    False := by
  rcases every_LehmerComposite_is_range_classified hL with hS | hC | hI | hB
  · exact hSmall n hS
  · exact hCaseC n hC
  · exact hIntermediate n hI
  · exact hCaseB n hB

/--
Final packaged theorem from the four actual global range closures.
-/
theorem pierreDeFermat_of_range_closures
    (hSmall : ∀ n : ℕ, InSmallPivotRange n → False)
    (hCaseC : ∀ n : ℕ, InCaseC n → False)
    (hIntermediate : ∀ n : ℕ, InIntermediate n → False)
    (hCaseB : ∀ n : ℕ, InCaseB n → False) :
    PierreDeFermatStatement := by
  intro n hL
  exact pierreDeFermat_pointwise_of_range_closures
    hL hSmall hCaseC hIntermediate hCaseB

/--
Readable reformulation.
-/
theorem no_LehmerComposite_of_range_closures
    (hSmall : ∀ n : ℕ, InSmallPivotRange n → False)
    (hCaseC : ∀ n : ℕ, InCaseC n → False)
    (hIntermediate : ∀ n : ℕ, InIntermediate n → False)
    (hCaseB : ∀ n : ℕ, InCaseB n → False) :
    ∀ n : ℕ, ¬ LehmerComposite n := by
  intro n hL
  exact pierreDeFermat_pointwise_of_range_closures
    hL hSmall hCaseC hIntermediate hCaseB

/--
Existential negation form.
-/
theorem no_counterexample_of_range_closures
    (hSmall : ∀ n : ℕ, InSmallPivotRange n → False)
    (hCaseC : ∀ n : ℕ, InCaseC n → False)
    (hIntermediate : ∀ n : ℕ, InIntermediate n → False)
    (hCaseB : ∀ n : ℕ, InCaseB n → False) :
    ¬ ∃ n : ℕ, LehmerComposite n := by
  intro h
  rcases h with ⟨n, hL⟩
  exact pierreDeFermat_pointwise_of_range_closures
    hL hSmall hCaseC hIntermediate hCaseB

end Audit
end Lehmer