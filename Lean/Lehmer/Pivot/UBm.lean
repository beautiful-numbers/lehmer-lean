import Mathlib
import Lehmer.Basic.Defs

namespace Lehmer
namespace Pivot

/--
`primeGe y p` means that `p` is prime and lies above the pivot `y`.
This is the basic predicate used to describe the prime envelope in the pivot method.
-/
def PrimeGe (y p : ℕ) : Prop :=
  Nat.Prime p ∧ y ≤ p

/--
The finite set of the first `m` primes above the pivot `y`.

This is left abstract at the specification level for now.
A concrete implementation can be provided later, together with correctness theorems.
-/
opaque firstPrimesFrom (y m : ℕ) : Finset ℕ

/--
The upper-bound envelope
`UBm(y) = ∏_{i=1}^m p_{y,i}/(p_{y,i}-1)`,
represented as a rational product over the abstract finite set
`firstPrimesFrom y m`.
-/
def UBm (y m : ℕ) : ℚ :=
  ∏ p in firstPrimesFrom y m, ((p : ℚ) / ((p - 1 : ℕ) : ℚ))

/--
Cardinality specification for the abstract prime envelope.
-/
axiom card_firstPrimesFrom (y m : ℕ) :
    (firstPrimesFrom y m).card = m

/--
Every element of `firstPrimesFrom y m` is prime.
-/
axiom mem_firstPrimesFrom_prime {y m p : ℕ} :
    p ∈ firstPrimesFrom y m → Nat.Prime p

/--
Every element of `firstPrimesFrom y m` lies above the pivot `y`.
-/
axiom mem_firstPrimesFrom_ge {y m p : ℕ} :
    p ∈ firstPrimesFrom y m → y ≤ p

/--
Monotonicity in the envelope length.
This is part of the pivot-spec API and will be refined later.
-/
axiom UBm_mono_right {y : ℕ} :
    Monotone (UBm y)

/--
Positivity of the pivot envelope.
-/
axiom UBm_pos {y m : ℕ} :
    0 < UBm y m

/--
Nonnegativity of the pivot envelope.
-/
theorem UBm_nonneg (y m : ℕ) : 0 ≤ UBm y m := by
  exact le_of_lt (UBm_pos)

/--
The empty envelope is `1`.
-/
axiom UBm_zero (y : ℕ) :
    UBm y 0 = 1

/--
Every factor appearing in `UBm y m` is of the form `p/(p-1)` with `p` prime and `p ≥ y`.
This is a convenient packaged API lemma.
-/
theorem mem_UBm_factor {y m p : ℕ} (hp : p ∈ firstPrimesFrom y m) :
    Nat.Prime p ∧ y ≤ p := by
  exact ⟨mem_firstPrimesFrom_prime hp, mem_firstPrimesFrom_ge hp⟩

/--
The envelope only uses primes at least `2` whenever `y ≥ 2`.
-/
theorem mem_firstPrimesFrom_two_le {y m p : ℕ} (hy : 2 ≤ y)
    (hp : p ∈ firstPrimesFrom y m) : 2 ≤ p := by
  exact le_trans hy (mem_firstPrimesFrom_ge hp)

/--
If `y ≥ 2`, every factor denominator in `UBm y m` is nonzero.
-/
theorem denom_ne_zero_of_mem {y m p : ℕ} (hy : 2 ≤ y)
    (hp : p ∈ firstPrimesFrom y m) :
    (((p - 1 : ℕ) : ℚ)) ≠ 0 := by
  have hp2 : 2 ≤ p := mem_firstPrimesFrom_two_le hy hp
  norm_num
  exact_mod_cast (Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hp2))

end Pivot
end Lehmer