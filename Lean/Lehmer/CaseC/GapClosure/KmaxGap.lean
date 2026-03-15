-- FILE: Lean/Lehmer/CaseC/GapClosure/KmaxGap.lean
import Lehmer.Prelude
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.TruncatedFamily
import Lehmer.CaseC.GapClosure.DeltaStar

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

/--
An abstract upper bound for the support-profile values occurring in the
truncated family at parameters `(y, W)`.

For MVP-3 we keep this as a simple placeholder parameter in `ℚ`; the
actual optimization argument is deferred to later files.
-/
def kmaxGap (y W : ℕ) : ℚ :=
  y + W

/--
Paper-style alias for the Case C support-profile upper bound.
-/
abbrev KmaxGap (y W : ℕ) : ℚ :=
  kmaxGap y W

@[simp] theorem kmaxGap_def (y W : ℕ) :
    kmaxGap y W = y + W := rfl

@[simp] theorem KmaxGap_def (y W : ℕ) :
    KmaxGap y W = kmaxGap y W := rfl

/--
At MVP-3, the abstract upper bound is definitionally nonnegative.
-/
theorem kmaxGap_nonneg (y W : ℕ) :
    0 ≤ kmaxGap y W := by
  simp [kmaxGap]
  positivity

/--
Stable MVP-3 placeholder: every support profile in the truncated family is
bounded above by `KmaxGap(y, W)`.
-/
theorem supportIndex_le_kmaxGap_placeholder
    {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S) :
    supportIndex S ≤ kmaxGap y W := by
  sorry

/--
Equivalent paper-style formulation with the alias `KmaxGap`.
-/
theorem supportIndex_le_KmaxGap_placeholder
    {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S) :
    supportIndex S ≤ KmaxGap y W := by
  simpa [KmaxGap] using
    supportIndex_le_kmaxGap_placeholder (y := y) (W := W) hS

/--
Stable MVP-3 placeholder: every truncated-family gap is bounded above by
`KmaxGap(y, W)`.
-/
theorem Delta_le_kmaxGap_placeholder
    {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S) :
    Delta S ≤ kmaxGap y W := by
  sorry

/--
Equivalent paper-style formulation of the previous upper bound.
-/
theorem Delta_le_KmaxGap_placeholder
    {y W : ℕ} {S : Finset ℕ}
    (hS : InTruncatedFamily y W S) :
    Delta S ≤ KmaxGap y W := by
  simpa [KmaxGap] using
    Delta_le_kmaxGap_placeholder (y := y) (W := W) hS

/--
Stable MVP-3 placeholder: the ratio `KmaxGap / DeltaStar` is well-formed in
the positive-gap regime relevant to Case C.
-/
theorem kmaxGap_div_deltaStar_wellformed_placeholder
    (y W : ℕ) :
    deltaStar y W ≠ 0 := by
  have hpos := deltaStar_pos_placeholder y W
  linarith

end GapClosure
end CaseC
end Lehmer