-- FILE: Lean/Lehmer/Pivot/AppendixA/BelowBarrierHyp.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.IntervalProductHyp : def thm
- Lehmer.Pivot.MreqAnalyticBridge : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.IntervalProductHyp
import Lehmer.Pivot.MreqAnalyticBridge

namespace Lehmer
namespace Pivot
namespace AppendixA

/-!
# Appendix A below-barrier hypothesis interface

This file packages the exact hypothesis shape needed for the pivot analytic
bridge:

* for every index `m` below the discretized barrier length `barrierLen y`,
  one has `UBm y m ≤ 2`.

Important scope:
* no proof of the below-barrier theorem yet;
* no crossing theorem yet;
* no direct `mreq` theorem yet.

This file only:
1. fixes the local hypothesis shape,
2. repackages it through the interval-product interface,
3. exposes the direct bridge target consumed later by
   `MreqAnalyticBridge.lean`.
-/

/--
Local below-barrier hypothesis at pivot level `y`.
-/
def HasBelowBarrierUBmLeTwo (y : ℕ) : Prop :=
  ∀ m : ℕ, m < barrierLen y → UBm y m ≤ 2

@[simp] theorem HasBelowBarrierUBmLeTwo_def (y : ℕ) :
    HasBelowBarrierUBmLeTwo y =
      (∀ m : ℕ, m < barrierLen y → UBm y m ≤ 2) := by
  rfl

/--
A local interval-product package at `(y,m)` yields the below-barrier bound for
that specific `m`, provided `m < barrierLen y`.
-/
theorem UBm_le_two_of_IntervalProductHypData
    {y m : ℕ}
    (_hm : m < barrierLen y)
    (D : IntervalProductHypData)
    (hy : D.y = y)
    (hm_eq : D.m = m) :
    UBm y m ≤ 2 := by
  subst hy
  subst hm_eq
  exact D.UBm_le_two

/--
Uniform below-barrier consequence from a family of local interval-product
packages.
-/
theorem HasBelowBarrierUBmLeTwo_of_intervalProductPackages
    {y : ℕ}
    (hpack :
      ∀ m : ℕ, m < barrierLen y →
        ∃ D : IntervalProductHypData, D.y = y ∧ D.m = m) :
    HasBelowBarrierUBmLeTwo y := by
  intro m hm
  rcases hpack m hm with ⟨D, rfl, rfl⟩
  exact D.UBm_le_two

/--
The below-barrier hypothesis in the exact shape consumed by
`MreqAnalyticBridge.lean`.
-/
theorem belowBarrier_bridge_shape
    {y : ℕ}
    (hbelow : HasBelowBarrierUBmLeTwo y) :
    ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2 := by
  simpa [HasBelowBarrierUBmLeTwo, barrierLen] using hbelow

/--
Conversely, the bridge-shape hypothesis implies the local below-barrier
hypothesis.
-/
theorem HasBelowBarrierUBmLeTwo_of_bridge_shape
    {y : ℕ}
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    HasBelowBarrierUBmLeTwo y := by
  simpa [HasBelowBarrierUBmLeTwo, barrierLen] using hbelow

/--
Bundled below-barrier interface at pivot level `y`.
-/
structure BelowBarrierHypData where
  y : ℕ
  hbelow : HasBelowBarrierUBmLeTwo y

namespace BelowBarrierHypData

/--
Pointwise extraction of the below-barrier bound.
-/
theorem UBm_le_two
    (D : BelowBarrierHypData)
    {m : ℕ} (hm : m < barrierLen D.y) :
    UBm D.y m ≤ 2 := by
  exact D.hbelow m hm

/--
Bridge-shape export consumed by `MreqAnalyticBridge.lean`.
-/
theorem bridge_shape
    (D : BelowBarrierHypData) :
    ∀ m : ℕ, m < Nat.ceil (barrier (D.y : ℝ)) → UBm D.y m ≤ 2 := by
  exact belowBarrier_bridge_shape D.hbelow

end BelowBarrierHypData

end AppendixA
end Pivot
end Lehmer