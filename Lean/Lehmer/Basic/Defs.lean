import Mathlib

namespace Lehmer
namespace Basic

/--
A composite integer satisfying Lehmer's divisibility condition.
This is the basic object ruled out by the main theorem.
-/
def LehmerComposite (n : ℕ) : Prop :=
  ¬ Nat.Prime n ∧ 2 ≤ n ∧ Nat.totient n ∣ (n - 1)

/--
The multiplicative index `I(n) = n / φ(n)`, viewed in `ℚ`.
-/
def totientIndex (n : ℕ) : ℚ :=
  (n : ℚ) / (Nat.totient n : ℚ)

/--
The Lehmer quotient `K(n) = (n - 1) / φ(n)`, viewed in `ℚ`.
-/
def lehmerQuotient (n : ℕ) : ℚ :=
  ((n - 1 : ℕ) : ℚ) / (Nat.totient n : ℚ)

/--
The prime support of `n`, as the finite set of prime divisors of `n`.
-/
def primeSupport (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter Nat.Prime

/--
The product of the elements of a finite support.
This is the support-level analogue of `n`.
-/
def supportProd (S : Finset ℕ) : ℕ :=
  S.prod id

/--
The lcm of the shifted support `{p - 1 : p ∈ S}`.
This is the support-level analogue of the Lehmer divisor obstruction.
-/
def supportLcm (S : Finset ℕ) : ℕ :=
  Finset.lcm S (fun p => p - 1)

/--
The cardinality of a finite support.
This is the support-level analogue of `ω(n)`.
-/
def supportCard (S : Finset ℕ) : ℕ :=
  S.card

end Basic
end Lehmer