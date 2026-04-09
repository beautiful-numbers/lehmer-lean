-- FILE: Lean/Lehmer/Pivot/AppendixA/BelowBarrier.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.Mreq : def thm
- Lehmer.Pivot.MreqAnalyticLowerBound : thm
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.Mreq
import Lehmer.Pivot.MreqAnalyticLowerBound
import Lehmer.Pivot.AppendixA.IntervalDefs

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A below-barrier control

This file is an internal Lean-facing facade for the Appendix A large-range
output.

Paper source:
- the public paper-facing output is the strict large-range lower bound
  `barrier (y : ℝ) < (mreq y : ℝ)` for primes `y ≥ Y0`;
- this file repackages that output into the discrete below-barrier control
  shape consumed by downstream Lean bridge files.

Accordingly, this file is not the public paper-facing theorem of Appendix A.
Its role is only to expose the internal discrete consequence:
* every `UBm y m` below the barrier length stays at or below `2`.
-/

/--
Strict below-barrier control.

This is the internal discrete consequence of the paper-facing large-range lower
bound on `mreq`.
-/
theorem ubm_le_two_below_barrierLen_strict
    {y : ℕ}
    (hy : Y0 ≤ y)
    (hp : Nat.Prime y) :
    ∀ m : ℕ, m < barrierLen y → UBm y m ≤ 2 := by
  intro m hm
  have hbar : barrier (y : ℝ) < (mreq y : ℝ) := by
    exact mreq_gt_barrier_of_ge_Y0 hy hp
  have hceil : barrierLen y ≤ mreq y := by
    rw [barrierLen_def]
    refine Nat.ceil_le.mpr ?_
    exact le_of_lt hbar
  have hmreq : m < mreq y := lt_of_lt_of_le hm hceil
  exact UBm_le_two_of_lt_mreq hmreq

/--
Inclusive below-barrier control.
-/
theorem ubm_le_two_below_barrierLen
    {y : ℕ}
    (hy : Y0 ≤ y)
    (hp : Nat.Prime y) :
    ∀ m : ℕ, m ≤ barrierLen y → UBm y m ≤ 2 := by
  intro m hm
  by_cases hEq : m = barrierLen y
  · subst hEq
    have hbar : barrier (y : ℝ) < (mreq y : ℝ) := by
      exact mreq_gt_barrier_of_ge_Y0 hy hp
    have hceil : barrierLen y ≤ mreq y := by
      rw [barrierLen_def]
      refine Nat.ceil_le.mpr ?_
      exact le_of_lt hbar
    exact UBm_le_two_of_lt_mreq (lt_of_le_of_lt hceil (Nat.lt_succ_self _))
  · have hlt : m < barrierLen y := lt_of_le_of_ne hm hEq
    exact ubm_le_two_below_barrierLen_strict hy hp m hlt

/--
Local below-barrier proposition at pivot level `y`.
-/
def HasBelowBarrierUBmLeTwo (y : ℕ) : Prop :=
  ∀ m : ℕ, m < barrierLen y → UBm y m ≤ 2

@[simp] theorem HasBelowBarrierUBmLeTwo_def (y : ℕ) :
    HasBelowBarrierUBmLeTwo y =
      (∀ m : ℕ, m < barrierLen y → UBm y m ≤ 2) := by
  rfl

/--
Uniform local below-barrier control beyond `Y0`.
-/
theorem hasBelowBarrierUBmLeTwo_of_ge_Y0
    {y : ℕ}
    (hy : Y0 ≤ y)
    (hp : Nat.Prime y) :
    HasBelowBarrierUBmLeTwo y := by
  intro m hm
  exact ubm_le_two_below_barrierLen_strict hy hp m hm

/--
Bridge-shape export consumed by the analytic bridge layer.
-/
theorem belowBarrier_bridge_shape
    {y : ℕ}
    (hy : Y0 ≤ y)
    (hp : Nat.Prime y) :
    ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2 := by
  intro m hm
  simpa [barrierLen_def] using hasBelowBarrierUBmLeTwo_of_ge_Y0 hy hp m hm

/--
Conversely, any bridge-shape control yields the local below-barrier predicate.
-/
theorem HasBelowBarrierUBmLeTwo_of_bridge_shape
    {y : ℕ}
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    HasBelowBarrierUBmLeTwo y := by
  simpa [HasBelowBarrierUBmLeTwo_def, barrierLen_def] using hbelow

/--
Bundled below-barrier control data at pivot level `y`.
-/
structure BelowBarrierData where
  y : ℕ
  hy : Y0 ≤ y
  hp : Nat.Prime y
  hbelow : HasBelowBarrierUBmLeTwo y

namespace BelowBarrierData

/--
Pointwise extraction of the below-barrier bound.
-/
theorem UBm_le_two
    (D : BelowBarrierData)
    {m : ℕ} (hm : m < barrierLen D.y) :
    UBm D.y m ≤ 2 := by
  exact D.hbelow m hm

/--
Bridge-shape export for the analytic bridge layer.
-/
theorem bridge_shape
    (D : BelowBarrierData) :
    ∀ m : ℕ, m < Nat.ceil (barrier (D.y : ℝ)) → UBm D.y m ≤ 2 := by
  exact belowBarrier_bridge_shape D.hy D.hp

end BelowBarrierData

end AppendixA
end Pivot
end Lehmer