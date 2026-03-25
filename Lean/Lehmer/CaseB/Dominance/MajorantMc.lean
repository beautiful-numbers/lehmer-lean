-- FILE: Lean/Lehmer/CaseB/Dominance/MajorantMc.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Parameters : def
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SupplyBound

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Closed paper-style majorant.

We keep the paper shape, but at Lean level this file only introduces the
closed majorant and the exact interface that later dominance files must use.
-/
noncomputable def Mc (y : ℕ) : ℝ :=
  ((20 : ℝ) / 3) * (yB y) / Real.log (yB y) +
    3 * (Real.log (yB y)) ^ 4 + 2

@[simp] theorem Mc_def (y : ℕ) :
    Mc y =
      ((20 : ℝ) / 3) * (yB y) / Real.log (yB y) +
        3 * (Real.log (yB y)) ^ 4 + 2 := rfl

/--
Natural-number wrapper around the closed majorant.
-/
noncomputable def McNat (y : ℕ) : ℕ :=
  Nat.ceil (Mc y)

@[simp] theorem McNat_def (y : ℕ) :
    McNat y = Nat.ceil (Mc y) := rfl

/--
Expanded form of the current Case B supply bound.
-/
theorem Mbound_eq_w_plus_KmaxB (y w : ℕ) :
    Mbound y w = w + KmaxB y := by
  exact Mbound_eq y w

/--
Expanded real-cast form of the current Case B supply bound.
-/
theorem Mbound_cast_eq (y w : ℕ) :
    ((Mbound y w : ℕ) : ℝ) = (w : ℝ) + (KmaxB y : ℝ) := by
  simp [Mbound_eq]

/--
Accounting-specialized real-cast form of the current Case B supply bound.
-/
theorem MboundOfAccounting_cast_eq {C : Context} (A : WitnessAccounting C) :
    ((MboundOfAccounting A : ℕ) : ℝ) =
      (witnessBudget A : ℝ) + (KmaxB C.y : ℝ) := by
  simp [MboundOfAccounting_eq]

/--
The witness-budget term is bounded by the ambient support cardinality.
-/
theorem witnessBudget_cast_le_supportCard_cast {C : Context} (A : WitnessAccounting C) :
    (witnessBudget A : ℝ) ≤ (supportCard C.S : ℝ) := by
  exact_mod_cast witnessBudget_le_supportCard A

/--
Pipeline-facing closed-majorant target:
the current Case B supply bound is dominated by the closed majorant `Mc`.
-/
def HasClosedMajorant (y : ℕ) (w : ℕ) : Prop :=
  ((Mbound y w : ℕ) : ℝ) ≤ Mc y

@[simp] theorem HasClosedMajorant_def (y : ℕ) (w : ℕ) :
    HasClosedMajorant y w = (((Mbound y w : ℕ) : ℝ) ≤ Mc y) := rfl

/--
Accounting-specialized closed-majorant target.
-/
def HasClosedMajorantOfAccounting {C : Context} (A : WitnessAccounting C) : Prop :=
  ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y

@[simp] theorem HasClosedMajorantOfAccounting_def {C : Context} (A : WitnessAccounting C) :
    HasClosedMajorantOfAccounting A =
      (((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y) := rfl

/--
Direct constructor for the closed-majorant interface.
-/
theorem hasClosedMajorant_of_assumption (y w : ℕ)
    (h : ((Mbound y w : ℕ) : ℝ) ≤ Mc y) :
    HasClosedMajorant y w := by
  exact h

/--
Direct constructor for the accounting-specialized closed-majorant interface.
-/
theorem hasClosedMajorantOfAccounting_of_assumption {C : Context} (A : WitnessAccounting C)
    (h : ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y) :
    HasClosedMajorantOfAccounting A := by
  exact h

/--
Elimination form of the closed-majorant interface.
-/
theorem closedMajorant_bound (y w : ℕ)
    (h : HasClosedMajorant y w) :
    ((Mbound y w : ℕ) : ℝ) ≤ Mc y := by
  exact h

/--
Elimination form of the accounting-specialized closed-majorant interface.
-/
theorem closedMajorantOfAccounting_bound {C : Context} (A : WitnessAccounting C)
    (h : HasClosedMajorantOfAccounting A) :
    ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y := by
  exact h

/--
The closed majorant also dominates the natural supply bound once the
corresponding real-valued interface has been established.
-/
theorem Mbound_le_McNat_of_closedMajorant (y w : ℕ)
    (h : HasClosedMajorant y w) :
    Mbound y w ≤ McNat y := by
  rw [McNat_def]
  exact Nat.le_ceil h

/--
Accounting-specialized natural domination form.
-/
theorem MboundOfAccounting_le_McNat_of_closedMajorant {C : Context} (A : WitnessAccounting C)
    (h : HasClosedMajorantOfAccounting A) :
    MboundOfAccounting A ≤ McNat C.y := by
  rw [McNat_def]
  exact Nat.le_ceil h

end CaseB
end Lehmer