-- FILE: Lean/Lehmer/Support/IncrementIdentity.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Support.IncrementRatio

namespace Lehmer
namespace Support

open Lehmer.Basic

/--
The support increment identity candidate attached to `p ∈ S`.

This is the paper-style closed form
`(p - 1) / gcd (p - 1) (L(S \\ {p}))`
for the support increment ratio `R_S(p)`.
For MVP-2 we package it as a definition first; the exact equality with
`incrementRatio` is recorded below as a stable placeholder.
-/
def incrementIdentityRhs (S : Finset ℕ) (p : ℕ) : ℕ :=
  (p - 1) / Nat.gcd (p - 1) (supportLcm (S.erase p))

/--
Paper-style notation-free rewrite of the increment identity right-hand side.
-/
@[simp] theorem incrementIdentityRhs_def (S : Finset ℕ) (p : ℕ) :
    incrementIdentityRhs S p =
      (p - 1) / Nat.gcd (p - 1) (supportLcm (S.erase p)) := rfl

/--
Alias showing the denominator that appears in the increment identity.
-/
def incrementIdentityDen (S : Finset ℕ) (p : ℕ) : ℕ :=
  Nat.gcd (p - 1) (supportLcm (S.erase p))

@[simp] theorem incrementIdentityDen_def (S : Finset ℕ) (p : ℕ) :
    incrementIdentityDen S p =
      Nat.gcd (p - 1) (supportLcm (S.erase p)) := rfl

/--
The denominator in the increment identity divides `p - 1`.
-/
theorem incrementIdentityDen_dvd_sub (S : Finset ℕ) (p : ℕ) :
    incrementIdentityDen S p ∣ (p - 1) := by
  dsimp [incrementIdentityDen]
  exact Nat.gcd_dvd_left (p - 1) (supportLcm (S.erase p))

/--
The increment-identity denominator also divides the support lcm after erasing `p`.
-/
theorem incrementIdentityDen_dvd_supportLcm_erase (S : Finset ℕ) (p : ℕ) :
    incrementIdentityDen S p ∣ supportLcm (S.erase p) := by
  dsimp [incrementIdentityDen]
  exact Nat.gcd_dvd_right (p - 1) (supportLcm (S.erase p))

/--
If `p ∉ S`, then the right-hand side specializes to the same closed form
with `erase` acting trivially.
-/
@[simp] theorem incrementIdentityRhs_of_not_mem {S : Finset ℕ} {p : ℕ}
    (hp : p ∉ S) :
    incrementIdentityRhs S p =
      (p - 1) / Nat.gcd (p - 1) (supportLcm S) := by
  simp [incrementIdentityRhs, supportLcm_erase_of_not_mem hp]

/--
Stable MVP-2 placeholder for the exact support increment identity

`R_S(p) = (p - 1) / gcd (p - 1) (L(S \\ {p}))`.

This is the core arithmetic bridge used later in Case B.
Its statement is expected to remain stable; the proof is deferred.
-/
theorem incrementRatio_eq_incrementIdentityRhs
    (S : Finset ℕ) (p : ℕ) (hp : p ∈ S) :
    incrementRatio S p = incrementIdentityRhs S p := by
  sorry

/--
Equivalent paper-style formulation using the alias `RS`.
-/
theorem RS_eq_incrementIdentityRhs
    (S : Finset ℕ) (p : ℕ) (hp : p ∈ S) :
    RS S p = (p - 1) / Nat.gcd (p - 1) (supportLcm (S.erase p)) := by
  simpa [RS, incrementIdentityRhs] using
    incrementRatio_eq_incrementIdentityRhs S p hp

end Support
end Lehmer