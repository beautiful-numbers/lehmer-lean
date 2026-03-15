-- FILE: Lean/Lehmer/Support/PotentialP.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs

namespace Lehmer
namespace Support

open Lehmer.Basic

/--
The basic support potential
`P(S) = log(L(S)) / log(n_S)`.

For MVP-2 we define it over `ℝ`. Analytic side conditions and refined
bounds are deferred to later files.
-/
noncomputable def potentialP (S : Finset ℕ) : ℝ :=
  Real.log (supportLcm S) / Real.log (supportProd S)

/--
Paper-style alias for the support potential.
-/
noncomputable abbrev P (S : Finset ℕ) : ℝ :=
  potentialP S

@[simp] theorem potentialP_def (S : Finset ℕ) :
    potentialP S = Real.log (supportLcm S) / Real.log (supportProd S) := rfl

@[simp] theorem P_def (S : Finset ℕ) :
    P S = Real.log (supportLcm S) / Real.log (supportProd S) := rfl

@[simp] theorem P_eq_potentialP (S : Finset ℕ) :
    P S = potentialP S := rfl

@[simp] theorem potentialP_empty :
    potentialP ∅ = Real.log (supportLcm ∅) / Real.log (supportProd ∅) := by
  rfl

@[simp] theorem potentialP_singleton (p : ℕ) :
    potentialP ({p} : Finset ℕ) =
      Real.log (supportLcm ({p} : Finset ℕ)) /
      Real.log (supportProd ({p} : Finset ℕ)) := by
  rfl

/--
Well-formedness placeholder: if the support product is not `1`, then the
denominator logarithm is not forced to be `0` by definition alone.

This is recorded as a stable interface lemma for later analytic use.
-/
theorem potentialP_wellformed_of_supportProd_ne_one
    {S : Finset ℕ} (hS : supportProd S ≠ 1) :
    Real.log (supportProd S) ≠ 0 := by
  sorry

theorem P_wellformed_of_supportProd_ne_one
    {S : Finset ℕ} (hS : supportProd S ≠ 1) :
    Real.log (supportProd S) ≠ 0 := by
  simpa [P, potentialP] using
    potentialP_wellformed_of_supportProd_ne_one hS

end Support
end Lehmer