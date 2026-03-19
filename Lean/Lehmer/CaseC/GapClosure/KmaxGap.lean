-- FILE: Lean/Lehmer/CaseC/GapClosure/KmaxGap.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.GapClosure.SupportProfiles : def
- Lehmer.CaseC.GapClosure.TruncatedFamily : def
- Lehmer.CaseC.GapClosure.DeltaStar : def thm
-/

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
Interface form: if one has established an upper bound by `kmaxGap`,
it can be used under the canonical file-local name.
-/
theorem supportIndex_le_kmaxGap_of_assumption
    {y W : ℕ} {S : Finset ℕ}
    (hbound : supportIndex S ≤ kmaxGap y W) :
    supportIndex S ≤ kmaxGap y W := by
  exact hbound

/--
Equivalent paper-style formulation with the alias `KmaxGap`.
-/
theorem supportIndex_le_KmaxGap_of_assumption
    {y W : ℕ} {S : Finset ℕ}
    (hbound : supportIndex S ≤ kmaxGap y W) :
    supportIndex S ≤ KmaxGap y W := by
  simpa [KmaxGap] using hbound

/--
Interface form for gap upper bounds by `kmaxGap`.
-/
theorem Delta_le_kmaxGap_of_assumption
    {y W : ℕ} {S : Finset ℕ}
    (hbound : Delta S ≤ kmaxGap y W) :
    Delta S ≤ kmaxGap y W := by
  exact hbound

/--
Equivalent paper-style formulation of the previous upper bound.
-/
theorem Delta_le_KmaxGap_of_assumption
    {y W : ℕ} {S : Finset ℕ}
    (hbound : Delta S ≤ kmaxGap y W) :
    Delta S ≤ KmaxGap y W := by
  simpa [KmaxGap] using hbound

/--
The ratio `KmaxGap / DeltaStar` is well-formed under the explicit
positive-gap hypothesis.
-/
theorem kmaxGap_div_deltaStar_wellformed_of_pos
    (y W : ℕ)
    (hpos : 0 < deltaStar y W) :
    deltaStar y W ≠ 0 := by
  linarith

end GapClosure
end CaseC
end Lehmer