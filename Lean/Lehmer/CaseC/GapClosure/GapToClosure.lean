-- FILE: Lean/Lehmer/CaseC/GapClosure/GapToClosure.lean
import Lehmer.Prelude
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.TruncatedFamily
import Lehmer.CaseC.GapClosure.DeltaStar
import Lehmer.CaseC.GapClosure.KmaxGap
import Lehmer.CaseC.GapClosure.ClosureBoundN
import Lehmer.CaseC.GapClosure.Omegahat
import Lehmer.CaseC.GapClosure.Bootstrap

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

/--
A minimal Case C profile package at parameters `(y, W)`.

For MVP-3 this just records a support together with membership in the
truncated family and nonintegrality of its support profile.
-/
structure GapProfile (y W : ℕ) where
  S : Finset ℕ
  hTrunc : InTruncatedFamily y W S
  hNonInt : NonIntegral S

/--
The support profile attached to a gap profile.
-/
def profileIndex {y W : ℕ} (G : GapProfile y W) : ℚ :=
  supportIndex G.S

/--
The gap attached to a gap profile.
-/
def profileGap {y W : ℕ} (G : GapProfile y W) : ℚ :=
  Delta G.S

@[simp] theorem profileIndex_def {y W : ℕ} (G : GapProfile y W) :
    profileIndex G = supportIndex G.S := rfl

@[simp] theorem profileGap_def {y W : ℕ} (G : GapProfile y W) :
    profileGap G = Delta G.S := rfl

/--
The Case C gap-to-closure condition at parameters `(y, W)`.

It packages the three abstract ingredients of the MVP-3 pipeline:
a positive gap floor `Δ*`, an upper profile bound `KmaxGap`, and the
bootstrap consistency condition `Ω̂(y, W) < W`.
-/
def GapToClosureReady (y W : ℕ) : Prop :=
  0 < DeltaStar y W ∧ BootstrapConsistent y W

@[simp] theorem GapToClosureReady_def (y W : ℕ) :
    GapToClosureReady y W = (0 < DeltaStar y W ∧ BootstrapConsistent y W) := rfl

/--
Every gap profile has support gap bounded below by `Δ*(y, W)`.
-/
theorem profileGap_lower_bound {y W : ℕ} (G : GapProfile y W) :
    DeltaStar y W ≤ profileGap G := by
  simpa [profileGap] using
    DeltaStar_lower_bound_placeholder (y := y) (W := W) G.hTrunc G.hNonInt

/--
Every gap profile has support profile bounded above by `KmaxGap(y, W)`.
-/
theorem profileIndex_upper_bound {y W : ℕ} (G : GapProfile y W) :
    profileIndex G ≤ KmaxGap y W := by
  simpa [profileIndex] using
    supportIndex_le_KmaxGap_placeholder (y := y) (W := W) G.hTrunc

/--
At MVP-3, readiness follows from the abstract positivity of `Δ*`
and the bootstrap consistency placeholder.
-/
theorem gapToClosureReady_placeholder (y W : ℕ) :
    GapToClosureReady y W := by
  refine ⟨?_, ?_⟩
  · simpa [DeltaStar] using deltaStar_pos_placeholder y W
  · exact bootstrapConsistency_placeholder y W

/--
Main MVP-3 bridge:
once the gap and bootstrap side are ready, the closure bound `N(y, W)`
acts as the abstract finite bound produced by the gap-to-closure pipeline.
-/
theorem gapToClosure_bound_placeholder (y W : ℕ)
    (h : GapToClosureReady y W) :
    ∀ n : ℕ, n ≤ N y W := by
  simpa [N] using closureBoundN_controls_witness_placeholder y W

/--
Equivalent formulation specialized to the placeholder readiness theorem.
-/
theorem gapToClosure_bound (y W : ℕ) :
    ∀ n : ℕ, n ≤ N y W := by
  exact gapToClosure_bound_placeholder y W (gapToClosureReady_placeholder y W)

/--
Bootstrap consequence recorded in the final Case C gap skeleton.
-/
theorem gapToClosure_bootstrap (y W : ℕ) :
    Omegahat y W < W := by
  exact omegahat_lt_W_placeholder y W

/--
Combined MVP-3 output:
the Case C gap pipeline provides both a finite closure bound `N(y, W)`
and the bootstrap consistency inequality `Ω̂(y, W) < W`.
-/
theorem gapToClosure_skeleton (y W : ℕ) :
    (∀ n : ℕ, n ≤ N y W) ∧ Omegahat y W < W := by
  exact ⟨gapToClosure_bound y W, gapToClosure_bootstrap y W⟩

end GapClosure
end CaseC
end Lehmer