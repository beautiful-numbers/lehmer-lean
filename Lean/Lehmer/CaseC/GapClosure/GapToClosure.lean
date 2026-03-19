-- FILE: Lean/Lehmer/CaseC/GapClosure/GapToClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.GapClosure.Rigidity : thm
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.CaseC.GapClosure.TruncatedFamily : def thm
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
- Lehmer.CaseC.GapClosure.KmaxGap : def thm
- Lehmer.CaseC.GapClosure.ClosureBoundN : def thm
- Lehmer.CaseC.GapClosure.Omegahat : def thm
- Lehmer.CaseC.GapClosure.Bootstrap : def thm
-/

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

It packages the two abstract ingredients actually used in the current
skeleton: a positive gap floor `Δ*` and the bootstrap consistency
condition `Ω̂(y, W) < W`.
-/
def GapToClosureReady (y W : ℕ) : Prop :=
  0 < DeltaStar y W ∧ BootstrapConsistent y W

@[simp] theorem GapToClosureReady_def (y W : ℕ) :
    GapToClosureReady y W = (0 < DeltaStar y W ∧ BootstrapConsistent y W) := rfl

/--
Every gap profile has support gap bounded below by `Δ*(y, W)` once that lower
bound has been established for the given support.
-/
theorem profileGap_lower_bound_of_assumption {y W : ℕ} (G : GapProfile y W)
    (hbound : DeltaStar y W ≤ profileGap G) :
    DeltaStar y W ≤ profileGap G := by
  exact hbound

/--
Every gap profile has support profile bounded above by `KmaxGap(y, W)` once
that upper bound has been established for the given support.
-/
theorem profileIndex_upper_bound_of_assumption {y W : ℕ} (G : GapProfile y W)
    (hbound : profileIndex G ≤ KmaxGap y W) :
    profileIndex G ≤ KmaxGap y W := by
  exact hbound

/--
Interface form: readiness follows once positivity of `Δ*` and bootstrap
consistency are supplied explicitly.
-/
theorem gapToClosureReady_of_assumption (y W : ℕ)
    (hpos : 0 < DeltaStar y W)
    (hboot : BootstrapConsistent y W) :
    GapToClosureReady y W := by
  exact ⟨hpos, hboot⟩

/--
Main bridge interface:
once readiness and a witness bound by `N(y, W)` are supplied, the closure
bound can be reused under the canonical file-local name.
-/
theorem gapToClosure_bound_of_assumption (y W : ℕ)
    (_h : GapToClosureReady y W)
    (hbound : ∀ n : ℕ, n ≤ N y W) :
    ∀ n : ℕ, n ≤ N y W := by
  exact hbound

/--
Bootstrap consequence recorded in the final Case C gap skeleton.
-/
theorem gapToClosure_bootstrap_of_assumption (y W : ℕ)
    (hboot : BootstrapConsistent y W) :
    Omegahat y W < W := by
  exact hboot

/--
Combined output interface:
once the closure bound and bootstrap consistency are supplied, they can be
packaged together under the canonical gap-to-closure name.
-/
theorem gapToClosure_skeleton_of_assumption (y W : ℕ)
    (hbound : ∀ n : ℕ, n ≤ N y W)
    (hboot : Omegahat y W < W) :
    (∀ n : ℕ, n ≤ N y W) ∧ Omegahat y W < W := by
  exact ⟨hbound, hboot⟩

end GapClosure
end CaseC
end Lehmer