-- FILE: Lean/Lehmer/Pivot/CaseAContradiction.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Basic.LehmerBasic : thm
- Lehmer.Basic.Totient : def thm
- Lehmer.Pivot.Defs : def thm
- Lehmer.Pivot.SupportInterface : def thm
- Lehmer.Pivot.UBm : def thm
- Lehmer.Pivot.CaseAMreq : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Basic.LehmerBasic
import Lehmer.Basic.Totient
import Lehmer.Pivot.Defs
import Lehmer.Pivot.SupportInterface
import Lehmer.Pivot.UBm
import Lehmer.Pivot.CaseAMreq

namespace Lehmer
namespace Pivot

open Lehmer.Basic

/--
Mathematical Case A predicate.

At the pivot layer, Case A is the direct pivot contradiction:
the support size of `n` is strictly smaller than the Case A pivot demand
attached to the canonical pivot value `pivotVal n`.
-/
def InCaseA (n : ℕ) : Prop :=
  omega n < caseAMreq (pivotVal n)

@[simp] theorem InCaseA_def (n : ℕ) :
    InCaseA n = (omega n < caseAMreq (pivotVal n)) := rfl

/--
Equivalent unfolded form of the Case A predicate.
-/
theorem inCaseA_iff (n : ℕ) :
    InCaseA n ↔ omega n < caseAMreq (pivotVal n) := by
  rfl

/--
Canonical roughness lemma at the pivot value.

For a Lehmer composite, every prime divisor of `n` is at least its canonical
pivot `pivotVal n = Nat.minFac n`.
-/
theorem yrough_at_pivotVal_of_LehmerComposite {n : ℕ}
    (_hL : LehmerComposite n) :
    YRough (pivotVal n) n := by
  intro p hp hpd
  simpa [pivotVal] using Nat.minFac_le_of_dvd hp.two_le hpd

/--
Worst-case envelope bound at the canonical pivot value.
-/
theorem totientIndex_le_UBm_at_pivotVal_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    totientIndex n ≤ UBm (pivotVal n) (omega n) := by
  rw [totientIndex_eq_prod_primeSupport_of_squarefree hL.squarefree]
  simpa [omega_def] using
    (prod_primeSupport_le_UBm_of_yrough
      (y := pivotVal n)
      (n := n)
      (yrough_at_pivotVal_of_LehmerComposite hL))

/--
Canonical Case A lower bound at the pivot value.

For a Lehmer composite, the support size is at least the local Case A pivot
demand.
-/
theorem caseAMreq_le_omega_at_pivot_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    caseAMreq (pivotVal n) ≤ omega n := by
  have hI : (2 : ℚ) < totientIndex n :=
    Lehmer.Basic.totientIndex_gt_two_of_LehmerComposite hL
  have hUB : (2 : ℚ) < UBm (pivotVal n) (omega n) := by
    exact lt_of_lt_of_le hI (totientIndex_le_UBm_at_pivotVal_of_LehmerComposite hL)
  exact caseAMreq_le_of_UBm_gt_two hUB

/--
Core Case A contradiction.

A Lehmer composite cannot lie in mathematical Case A, because the canonical
pivot lower bound forces `caseAMreq (pivotVal n) ≤ omega n`.
-/
theorem caseA_impossible {n : ℕ}
    (hL : LehmerComposite n)
    (hA : InCaseA n) :
    False := by
  have hdemand : caseAMreq (pivotVal n) ≤ omega n :=
    caseAMreq_le_omega_at_pivot_of_LehmerComposite hL
  exact not_lt_of_ge hdemand hA

/--
Negated form of the Case A contradiction.
-/
theorem not_inCaseA_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ InCaseA n := by
  intro hA
  exact caseA_impossible hL hA

/--
Numerical non-strict consequence of the Case A contradiction:
for a Lehmer composite, the support size is at least the local Case A pivot
demand.
-/
theorem caseAMreq_le_omega_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    caseAMreq (pivotVal n) ≤ omega n := by
  exact caseAMreq_le_omega_at_pivot_of_LehmerComposite hL

/--
Repackaged contradiction in raw inequality form.
-/
theorem omega_not_lt_caseAMreq_at_pivot_of_LehmerComposite {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ (omega n < caseAMreq (pivotVal n)) := by
  exact not_inCaseA_of_LehmerComposite hL

end Pivot
end Lehmer