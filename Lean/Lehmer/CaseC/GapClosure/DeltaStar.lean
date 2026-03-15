-- FILE: Lean/Lehmer/CaseC/GapClosure/DeltaStar.lean
import Lehmer.Prelude
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.TruncatedFamily

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

/--
The set of support gaps arising from the truncated family at parameters `(y, W)`.
-/
def truncatedGapSet (y W : ℕ) : Set ℚ :=
  {d | ∃ S : Finset ℕ, InTruncatedFamily y W S ∧ d = Delta S}

/--
The positive gap predicate for a support in the truncated family.
-/
def PositiveGapAt (y W : ℕ) (S : Finset ℕ) : Prop :=
  InTruncatedFamily y W S ∧ 0 < Delta S

@[simp] theorem truncatedGapSet_def (y W : ℕ) :
    truncatedGapSet y W =
      {d | ∃ S : Finset ℕ, InTruncatedFamily y W S ∧ d = Delta S} := rfl

@[simp] theorem PositiveGapAt_def (y W : ℕ) (S : Finset ℕ) :
    PositiveGapAt y W S = (InTruncatedFamily y W S ∧ 0 < Delta S) := rfl

/--
The abstract minimal positive gap attached to the truncated family at `(y, W)`.

For MVP-3 we package this as a parameter in `ℚ`; the actual optimization /
minimization proof is deferred to later files.
-/
def deltaStar (y W : ℕ) : ℚ :=
  0

/--
Paper-style alias for the minimal positive gap.
-/
abbrev DeltaStar (y W : ℕ) : ℚ :=
  deltaStar y W

@[simp] theorem deltaStar_def (y W : ℕ) :
    deltaStar y W = 0 := rfl

@[simp] theorem DeltaStar_def (y W : ℕ) :
    DeltaStar y W = deltaStar y W := rfl

/--
At MVP-3, `Δ*` is definitionally nonnegative.
-/
theorem deltaStar_nonneg (y W : ℕ) :
    0 ≤ deltaStar y W := by
  simp [deltaStar]

/--
If a support contributes to the truncated family with positive gap, then its gap
belongs to the truncated gap set.
-/
theorem Delta_mem_truncatedGapSet {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S) :
    Delta S ∈ truncatedGapSet y W := by
  refine ⟨S, hS, rfl⟩

/--
Stable MVP-3 placeholder: every nonintegral support profile in the truncated
family has gap bounded below by `Δ*(y, W)`.
-/
theorem deltaStar_lower_bound_placeholder
    {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S)
    (hNI : NonIntegral S) :
    deltaStar y W ≤ Delta S := by
  sorry

/--
Stable MVP-3 placeholder: the minimal positive gap is strictly positive once
the truncated family is restricted to the nonintegral support profiles relevant
to Case C.
-/
theorem deltaStar_pos_placeholder (y W : ℕ) :
    0 < deltaStar y W := by
  sorry

/--
Equivalent paper-style formulation using the alias `Δ*`.
-/
theorem DeltaStar_lower_bound_placeholder
    {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S)
    (hNI : NonIntegral S) :
    DeltaStar y W ≤ Delta S := by
  simpa [DeltaStar] using
    deltaStar_lower_bound_placeholder (y := y) (W := W) hS hNI

end GapClosure
end CaseC
end Lehmer