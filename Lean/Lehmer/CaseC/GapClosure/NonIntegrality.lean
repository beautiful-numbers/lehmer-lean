-- FILE: Lean/Lehmer/CaseC/GapClosure/NonIntegrality.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.Basic.OddSquarefree : thm
-/

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
  simp [supportIndex] at h0

/--
A natural-number support profile is nonintegral when the underlying prime support
is nonintegral.
-/
def NatNonIntegralProfile (n : ℕ) : Prop :=
  NonIntegral (primeSupport n)

@[simp] theorem NatNonIntegralProfile_def (n : ℕ) :
    NatNonIntegralProfile n = NonIntegral (primeSupport n) := rfl

/--
Interface form: once nonintegrality of an odd squarefree prime support has
been established, it can be reused under the canonical file-local name.
-/
theorem nonintegral_of_odd_squarefree_support_of_assumption
    (S : Finset ℕ)
    (_hPrime : ∀ p ∈ S, Nat.Prime p)
    (_hOdd : ∀ p ∈ S, Odd p)
    (hNI : NonIntegral S) :
    NonIntegral S := by
  exact hNI

/--
Interface form for the prime support of a Lehmer composite.
-/
theorem nonintegral_primeSupport_of_LehmerComposite_of_assumption
    {n : ℕ} (_h : LehmerComposite n)
    (hNI : NatNonIntegralProfile n) :
    NatNonIntegralProfile n := by
  exact hNI

/--
Equivalent support-profile form for a Lehmer composite.
-/
theorem supportProfileOfNat_nonintegral_of_LehmerComposite_of_assumption
    {n : ℕ} (_h : LehmerComposite n)
    (hNI : NatNonIntegralProfile n) :
    ∀ k : ℕ, supportProfileOfNat n ≠ k := by
  intro k hk
  have h' : supportIndex (primeSupport n) ≠ k := hNI k
  exact h' (by simpa [supportProfileOfNat] using hk)

end GapClosure
end CaseC
end Lehmer