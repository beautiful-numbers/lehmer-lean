-- FILE: Lean/Lehmer/Support/PotentialP.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.SupportProd

namespace Lehmer
namespace Support

open Lehmer.Basic

/--
The basic support potential
`P(S) = log(L(S)) / log(n_S)`.
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
If all members of the support are prime and the support is nonempty,
then the support product is not `1`.
-/
theorem supportProd_ne_one_of_all_prime_nonempty
    {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hne : S.Nonempty) :
    supportProd S ≠ 1 := by
  rcases hne with ⟨p, hp⟩
  have hpprime : Nat.Prime p := hprime p hp
  have hpdvd : p ∣ supportProd S := by
    exact dvd_supportProd hp
  intro hprod
  have : p ∣ 1 := by
    simpa [hprod] using hpdvd
  exact hpprime.not_dvd_one this

/--
Well-formedness of the denominator logarithm under the natural arithmetic
support assumptions used in the manuscript.
-/
theorem potentialP_wellformed_of_all_prime_nonempty
    {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hne : S.Nonempty) :
    Real.log (supportProd S) ≠ 0 := by
  have hpos_nat : 0 < supportProd S := by
    apply supportProd_pos
    intro p hp
    exact Nat.Prime.pos (hprime p hp)
  have hpos_real : 0 < (supportProd S : ℝ) := by
    exact_mod_cast hpos_nat
  have hne1 : supportProd S ≠ 1 := by
    exact supportProd_ne_one_of_all_prime_nonempty hprime hne
  intro hlog
  have hexp := congrArg Real.exp hlog
  have hone_real : (supportProd S : ℝ) = 1 := by
    simpa [Real.exp_log hpos_real] using hexp
  have hone_nat : supportProd S = 1 := by
    exact_mod_cast hone_real
  exact hne1 hone_nat

/--
Alias form of the previous well-formedness statement.
-/
theorem P_wellformed_of_all_prime_nonempty
    {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hne : S.Nonempty) :
    Real.log (supportProd S) ≠ 0 := by
  simpa [P, potentialP] using
    potentialP_wellformed_of_all_prime_nonempty hprime hne

end Support
end Lehmer