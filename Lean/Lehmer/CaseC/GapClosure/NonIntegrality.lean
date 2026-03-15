-- FILE: Lean/Lehmer/CaseC/GapClosure/NonIntegrality.lean
import Lehmer.Prelude
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.Basic.OddSquarefree

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

/--
A support profile is nonintegral if its support-level index is not a natural number.
-/
def NonIntegralProfile (S : Finset ℕ) : Prop :=
  ∀ k : ℕ, supportIndex S ≠ k

/--
Alias for the nonintegrality predicate.
-/
abbrev NonIntegral (S : Finset ℕ) : Prop :=
  NonIntegralProfile S

@[simp] theorem NonIntegralProfile_def (S : Finset ℕ) :
    NonIntegralProfile S = (∀ k : ℕ, supportIndex S ≠ k) := rfl

@[simp] theorem NonIntegral_def (S : Finset ℕ) :
    NonIntegral S = (∀ k : ℕ, supportIndex S ≠ k) := rfl

/--
The empty support profile is integral, hence not nonintegral.
-/
theorem not_NonIntegral_empty :
    ¬ NonIntegral (∅ : Finset ℕ) := by
  intro h
  have h0 := h 1
  simpa [NonIntegral, supportIndex] using h0

/--
A natural-number support profile is nonintegral when the underlying prime support
is nonintegral.
-/
def NatNonIntegralProfile (n : ℕ) : Prop :=
  NonIntegral (primeSupport n)

@[simp] theorem NatNonIntegralProfile_def (n : ℕ) :
    NatNonIntegralProfile n = NonIntegral (primeSupport n) := rfl

/--
Stable MVP-3 placeholder: odd squarefree supports carry nonintegral support
profiles in the sense required by the Case C gap pipeline.
-/
theorem nonintegral_of_odd_squarefree_support
    (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, Nat.Prime p)
    (hOdd : ∀ p ∈ S, Odd p) :
    NonIntegral S := by
  sorry

/--
Stable MVP-3 placeholder: the prime support of a Lehmer composite has a
nonintegral support profile.
-/
theorem nonintegral_primeSupport_of_LehmerComposite
    {n : ℕ} (h : LehmerComposite n) :
    NatNonIntegralProfile n := by
  sorry

/--
Stable MVP-3 placeholder: equivalently, the support profile attached to a
Lehmer composite is not a natural number.
-/
theorem supportProfileOfNat_nonintegral_of_LehmerComposite
    {n : ℕ} (h : LehmerComposite n) :
    ∀ k : ℕ, supportProfileOfNat n ≠ k := by
  intro k
  have hNI : NatNonIntegralProfile n := nonintegral_primeSupport_of_LehmerComposite h
  simpa [NatNonIntegralProfile, supportProfileOfNat] using hNI k

end GapClosure
end CaseC
end Lehmer