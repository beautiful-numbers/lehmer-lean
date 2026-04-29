-- FILE: Lean/Lehmer/Audit-axle/PierreDeFermat.statement.lean
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
  sorry

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
  sorry