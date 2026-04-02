-- FILE: Lean/Lehmer/Pivot/AppendixA/IntervalDefs.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A interval definitions

This file introduces only the discrete interval objects used by the Appendix A
large-range pivot layer.

Important scope:
* purely definitional / arithmetic;
* no prime counting;
* no `UBm` estimates yet;
* no `mreq` statements yet.

The role of this file is to fix the discrete interval attached to the analytic
barrier in a form that later files can consume uniformly.
-/

/--
Discrete barrier length attached to `y`.

We package the large-range barrier using `Nat.ceil`, so later files can work
with a natural interval length.
-/
noncomputable def barrierLen (y : ℕ) : ℕ :=
  Nat.ceil (barrier (y : ℝ))

/--
Upper endpoint of the discrete Appendix A interval attached to `y`.

The interval is intended to have length `barrierLen y`, namely
`[y, xA y] = [y, y + barrierLen y - 1]`.
-/
noncomputable def xA (y : ℕ) : ℕ :=
  y + barrierLen y - 1

/--
Discrete Appendix A interval predicate.
-/
def InInterval (y t : ℕ) : Prop :=
  y ≤ t ∧ t ≤ xA y

@[simp] theorem barrierLen_def (y : ℕ) :
    barrierLen y = Nat.ceil (barrier (y : ℝ)) := rfl

@[simp] theorem xA_def (y : ℕ) :
    xA y = y + barrierLen y - 1 := rfl

@[simp] theorem InInterval_def (y t : ℕ) :
    InInterval y t = (y ≤ t ∧ t ≤ xA y) := rfl

/--
The left endpoint belongs to the interval as soon as the interval length is
positive.
-/
theorem left_mem_interval
    {y : ℕ}
    (hpos : 0 < barrierLen y) :
    InInterval y y := by
  constructor
  · exact le_rfl
  · dsimp [xA]
    have hy : y ≤ y + barrierLen y - 1 := by
      omega
    exact hy

/--
The right endpoint belongs to its own interval.
-/
theorem right_mem_interval (y : ℕ) :
    InInterval y (xA y) := by
  constructor
  · dsimp [xA]
    omega
  · exact le_rfl

/--
Any point in the discrete Appendix A interval lies above `y`.
-/
theorem left_le_of_mem_interval
    {y t : ℕ}
    (ht : InInterval y t) :
    y ≤ t := ht.1

/--
Any point in the discrete Appendix A interval lies below `xA y`.
-/
theorem le_right_of_mem_interval
    {y t : ℕ}
    (ht : InInterval y t) :
    t ≤ xA y := ht.2

/--
Monotone reformulation of interval membership.
-/
theorem mem_interval_iff
    {y t : ℕ} :
    InInterval y t ↔ y ≤ t ∧ t ≤ xA y := by
  rfl

/--
If the interval length is positive, then `y ≤ xA y`.
-/
theorem left_le_xA
    {y : ℕ}
    (hpos : 0 < barrierLen y) :
    y ≤ xA y := by
  exact (left_mem_interval hpos).2

/--
Arithmetic identity for the interval width.
-/
theorem xA_succ_eq_left_add_len
    (y : ℕ) :
    xA y + 1 = y + barrierLen y := by
  dsimp [xA]
  omega

/--
The interval `[y, xA y]` has cardinal width `barrierLen y` in the arithmetic
sense.
-/
theorem xA_eq_left_add_pred
    (y : ℕ) :
    xA y = y + barrierLen y - 1 := by
  rfl

/--
If `t < barrierLen y`, then `y + t` lies in the discrete Appendix A interval.
-/
theorem add_lt_barrierLen_mem_interval
    {y t : ℕ}
    (ht : t < barrierLen y) :
    InInterval y (y + t) := by
  constructor
  · exact Nat.le_add_right y t
  · dsimp [xA]
    omega

/--
Specialization of the previous lemma to the right endpoint index.
-/
theorem add_pred_barrierLen_eq_xA
    {y : ℕ}
    (hpos : 0 < barrierLen y) :
    y + (barrierLen y - 1) = xA y := by
  dsimp [xA]
  omega

end AppendixA
end Pivot
end Lehmer