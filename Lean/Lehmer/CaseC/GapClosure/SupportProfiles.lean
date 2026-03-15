-- FILE: Lean/Lehmer/CaseC/GapClosure/SupportProfiles.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.Totient

namespace Lehmer
namespace CaseC
namespace GapClosure

open Lehmer.Basic

def supportIndex (S : Finset ℕ) : ℚ :=
  S.prod (fun p => (p : ℚ) / ((p - 1 : ℕ) : ℚ))

abbrev IS (S : Finset ℕ) : ℚ :=
  supportIndex S

@[simp] theorem supportIndex_def (S : Finset ℕ) :
    supportIndex S = S.prod (fun p => (p : ℚ) / ((p - 1 : ℕ) : ℚ)) := rfl

@[simp] theorem IS_def (S : Finset ℕ) :
    IS S = S.prod (fun p => (p : ℚ) / ((p - 1 : ℕ) : ℚ)) := rfl

@[simp] theorem supportIndex_empty :
    supportIndex ∅ = 1 := by
  simp [supportIndex]

@[simp] theorem supportIndex_singleton (p : ℕ) :
    supportIndex ({p} : Finset ℕ) = (p : ℚ) / ((p - 1 : ℕ) : ℚ) := by
  simp [supportIndex]

theorem supportIndex_insert {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) :
    supportIndex (insert p S) =
      ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) * supportIndex S := by
  rw [supportIndex, Finset.prod_insert hp, supportIndex]

theorem supportIndex_of_mem_erase {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    supportIndex S =
      ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) * supportIndex (S.erase p) := by
  have hp' : p ∉ S.erase p := by
    simp
  simpa [Finset.insert_erase hp] using
    (supportIndex_insert (S := S.erase p) (p := p) hp')

def supportGap (S : Finset ℕ) : ℚ :=
  supportIndex S - (Nat.floor (supportIndex S) : ℚ)

abbrev Delta (S : Finset ℕ) : ℚ :=
  supportGap S

@[simp] theorem supportGap_def (S : Finset ℕ) :
    supportGap S = supportIndex S - (Nat.floor (supportIndex S) : ℚ) := rfl

@[simp] theorem Delta_def (S : Finset ℕ) :
    Delta S = supportIndex S - (Nat.floor (supportIndex S) : ℚ) := rfl

@[simp] theorem supportGap_empty :
    supportGap ∅ = 0 := by
  simp [supportGap, supportIndex]

def supportProfileOfNat (n : ℕ) : ℚ :=
  supportIndex (primeSupport n)

@[simp] theorem supportProfileOfNat_def (n : ℕ) :
    supportProfileOfNat n = supportIndex (primeSupport n) := rfl

theorem supportProfileOfNat_eq_totientIndex_of_squarefree
    {n : ℕ} (_hSq : Squarefree n) :
    supportProfileOfNat n = totientIndex n := by
  sorry

theorem supportProfileOfNat_eq_totientIndex_of_LehmerComposite
    {n : ℕ} (h : LehmerComposite n) :
    supportProfileOfNat n = totientIndex n := by
  sorry

end GapClosure
end CaseC
end Lehmer