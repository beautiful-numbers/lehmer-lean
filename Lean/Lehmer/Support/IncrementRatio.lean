-- FILE: Lean/Lehmer/Support/IncrementRatio.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs

namespace Lehmer
namespace Support

open Lehmer.Basic

/--
The support increment ratio attached to `p ∈ S`.

At the support level, this is the quotient
`L(S) / L(S \ {p})`, where `L = supportLcm`.
For MVP-2 we define it as a natural-number quotient; the exact
identity and divisibility properties are deferred to
`IncrementIdentity.lean`.
-/
def incrementRatio (S : Finset ℕ) (p : ℕ) : ℕ :=
  supportLcm S / supportLcm (S.erase p)

/--
Notation alias for the support increment ratio.
This matches the paper-style object `R_S(p)`.
-/
abbrev RS (S : Finset ℕ) (p : ℕ) : ℕ :=
  incrementRatio S p

@[simp] theorem incrementRatio_def (S : Finset ℕ) (p : ℕ) :
    incrementRatio S p = supportLcm S / supportLcm (S.erase p) := rfl

@[simp] theorem RS_def (S : Finset ℕ) (p : ℕ) :
    RS S p = supportLcm S / supportLcm (S.erase p) := rfl

/--
If `p ∉ S`, erasing `p` does nothing, so the denominator is unchanged.
-/
@[simp] theorem supportLcm_erase_of_not_mem {S : Finset ℕ} {p : ℕ}
    (hp : p ∉ S) :
    supportLcm (S.erase p) = supportLcm S := by
  simp [supportLcm, hp]

/--
If `p ∉ S`, the support increment ratio rewrites to the trivial self-quotient.
We keep this as a rewrite only at MVP-2, rather than forcing arithmetic
normalization in `ℕ`.
-/
@[simp] theorem incrementRatio_of_not_mem {S : Finset ℕ} {p : ℕ}
    (hp : p ∉ S) :
    incrementRatio S p = supportLcm S / supportLcm S := by
  rw [incrementRatio, supportLcm_erase_of_not_mem hp]

/--
Equivalent statement for the notation alias `RS`.
-/
@[simp] theorem RS_of_not_mem {S : Finset ℕ} {p : ℕ}
    (hp : p ∉ S) :
    RS S p = supportLcm S / supportLcm S := by
  rw [RS, incrementRatio_of_not_mem hp]

/--
If `p ∈ S`, the object `RS S p` is the natural support-level ratio
attached to the removal of `p`.

This theorem is just the specialized rewrite under the membership
hypothesis; the substantive arithmetic content comes later.
-/
theorem RS_eq_of_mem {S : Finset ℕ} {p : ℕ} (_hp : p ∈ S) :
    RS S p = supportLcm S / supportLcm (S.erase p) := by
  rfl

end Support
end Lehmer