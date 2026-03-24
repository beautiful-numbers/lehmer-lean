-- FILE: Lean/Lehmer/CaseC/GapClosure/DeltaStar.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.GapClosure.SupportProfiles : def
- Lehmer.CaseC.GapClosure.NonIntegrality : def
- Lehmer.CaseC.GapClosure.TruncatedFamily : def
-/

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

At this stage it is only a placeholder datum; positivity must be supplied
explicitly before using it in a denominator.
-/
def deltaStar (_y _W : ℕ) : ℚ :=
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
At this placeholder stage, `Δ*` is definitionally nonnegative.
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
Interface form: once a lower bound by `Δ*(y, W)` has been established for a
given nonintegral truncated-family support, it can be reused under the
canonical file-local name.
-/
theorem deltaStar_lower_bound_of_assumption
    {y W : ℕ} {S : Finset ℕ}
    (_hS : InTruncatedFamily y W S)
    (_hNI : NonIntegral S)
    (hbound : deltaStar y W ≤ Delta S) :
    deltaStar y W ≤ Delta S := by
  exact hbound

/--
Paper-style alias form of the previous interface lemma.
-/
theorem DeltaStar_lower_bound_of_assumption
    {y W : ℕ} {S : Finset ℕ}
    (_hS : InTruncatedFamily y W S)
    (_hNI : NonIntegral S)
    (hbound : deltaStar y W ≤ Delta S) :
    DeltaStar y W ≤ Delta S := by
  simpa [DeltaStar] using hbound

/--
Explicit positivity interface for `Δ*`.
-/
theorem deltaStar_pos_of_assumption
    (y W : ℕ)
    (hpos : 0 < deltaStar y W) :
    0 < deltaStar y W := by
  exact hpos

end GapClosure
end CaseC
end Lehmer