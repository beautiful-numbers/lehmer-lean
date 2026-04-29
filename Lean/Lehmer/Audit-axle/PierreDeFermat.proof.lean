-- FILE: Lean/Lehmer/Audit-axle/PierreDeFermat.proof.lean
import Mathlib


theorem pierreDeFermat_pointwise_of_range_closures
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (every_LehmerComposite_is_range_classified :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n)
    {n : Nat}
    (hL : LehmerComposite n)
    (hSmall : forall m : Nat, InSmallPivotRange m -> False)
    (hCaseC : forall m : Nat, InCaseC m -> False)
    (hIntermediate : forall m : Nat, InIntermediate m -> False)
    (hCaseB : forall m : Nat, InCaseB m -> False) :
    False := by
  cases every_LehmerComposite_is_range_classified hL with
  | inl hS =>
      exact hSmall n hS
  | inr hRest =>
      cases hRest with
      | inl hC =>
          exact hCaseC n hC
      | inr hRest2 =>
          cases hRest2 with
          | inl hI =>
              exact hIntermediate n hI
          | inr hB =>
              exact hCaseB n hB

theorem no_counterexample_of_range_closures
    (LehmerComposite : Nat -> Prop)
    (InSmallPivotRange : Nat -> Prop)
    (InCaseC : Nat -> Prop)
    (InIntermediate : Nat -> Prop)
    (InCaseB : Nat -> Prop)
    (every_LehmerComposite_is_range_classified :
      forall {n : Nat},
        LehmerComposite n ->
          InSmallPivotRange n \/ InCaseC n \/ InIntermediate n \/ InCaseB n)
    (hSmall : forall n : Nat, InSmallPivotRange n -> False)
    (hCaseC : forall n : Nat, InCaseC n -> False)
    (hIntermediate : forall n : Nat, InIntermediate n -> False)
    (hCaseB : forall n : Nat, InCaseB n -> False) :
    Not (Exists fun n : Nat => LehmerComposite n) := by
  intro h
  cases h with
  | intro n hL =>
      exact pierreDeFermat_pointwise_of_range_closures
        LehmerComposite
        InSmallPivotRange
        InCaseC
        InIntermediate
        InCaseB
        every_LehmerComposite_is_range_classified
        hL
        hSmall
        hCaseC
        hIntermediate
        hCaseB
