-- FILE: Lean/Lehmer/Basic/SupportProd.lean
import Mathlib
import Lehmer.Basic.Defs

namespace Lehmer
namespace Basic

@[simp] theorem supportProd_empty :
    supportProd (∅ : Finset ℕ) = 1 := by
  simp [supportProd]

@[simp] theorem supportProd_singleton (p : ℕ) :
    supportProd ({p} : Finset ℕ) = p := by
  simp [supportProd]

@[simp] theorem supportProd_insert {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) :
    supportProd (insert p S) = p * supportProd S := by
  simp [supportProd, hp]

/-- Every element of a support divides its support product. -/
theorem dvd_supportProd {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    p ∣ supportProd S := by
  exact Finset.dvd_prod_of_mem id hp

/-- The support product is positive if all members are positive. -/
theorem supportProd_pos {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) :
    0 < supportProd S := by
  classical
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp [supportProd]
  · intro a T ha ih hS
    rw [supportProd_insert ha]
    have ha' : 0 < a := hS a (Finset.mem_insert_self a T)
    have hT' : 0 < supportProd T := by
      apply ih
      intro p hp
      exact hS p (Finset.mem_insert_of_mem hp)
    exact Nat.mul_pos ha' hT'

/-- The support product is nonzero if all members are positive. -/
theorem supportProd_ne_zero {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) :
    supportProd S ≠ 0 := by
  exact Nat.ne_of_gt (supportProd_pos hS)

/-- If all members of the support are at least `1`, then the support product is at least `1`. -/
theorem one_le_supportProd {S : Finset ℕ}
    (hS : ∀ p ∈ S, 1 ≤ p) :
    1 ≤ supportProd S := by
  have hpos : ∀ p ∈ S, 0 < p := by
    intro p hp
    exact lt_of_lt_of_le (by decide : 0 < 1) (hS p hp)
  exact Nat.succ_le_of_lt (supportProd_pos hpos)

/-- A useful API lemma duplicating `dvd_supportProd`. -/
theorem dvd_supportProd_of_mem {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    p ∣ supportProd S := by
  exact dvd_supportProd hp

end Basic
end Lehmer