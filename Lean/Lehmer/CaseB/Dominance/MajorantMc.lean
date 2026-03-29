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

This file is the home of the *structural closed majorant* used in Case B.
It does **not** perform the final analytic comparison against the pivot demand.
Its role is only:

* define the real closed majorant `Mc`,
* define its terminal discretization `McNat := ceil(Mc)`,
* expose real-valued structural bridges from Case B supply bounds to `Mc`,
* expose terminal discrete bridges from Case B supply bounds to `McNat`.

The analytic no-crossing step belongs downstream.
-/
noncomputable def Mc (y : ℕ) : ℝ :=
  ((20 : ℝ) / 3) * (yB y) / Real.log (yB y) +
    3 * (Real.log (yB y)) ^ 4 + 2

@[simp] theorem Mc_def (y : ℕ) :
    Mc y =
      ((20 : ℝ) / 3) * (yB y) / Real.log (yB y) +
        3 * (Real.log (yB y)) ^ 4 + 2 := rfl

/--
Terminal natural-number discretization of the closed majorant.
This is a final wrapper and should not be used as the analytic comparison layer.
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
  simp [Mbound, Wbound]

/--
Accounting-specialized real-cast form of the current Case B supply bound.
-/
theorem MboundOfAccounting_cast_eq {C : Context} (A : WitnessAccounting C) :
    ((MboundOfAccounting A : ℕ) : ℝ) =
      (witnessBudget A : ℝ) + (KmaxB C.y : ℝ) := by
  simp [MboundOfAccounting, Mbound, Wbound]

/--
The witness-budget term is bounded by the ambient support cardinality.
-/
theorem witnessBudget_cast_le_supportCard_cast {C : Context} (A : WitnessAccounting C) :
    (witnessBudget A : ℝ) ≤ (supportCard C.S : ℝ) := by
  exact_mod_cast witnessBudget_le_supportCard A

/--
Pipeline-facing real closed-majorant target:
the current Case B supply bound is dominated by the real closed majorant `Mc`.
-/
def HasClosedMajorant (y : ℕ) (w : ℕ) : Prop :=
  ((Mbound y w : ℕ) : ℝ) ≤ Mc y

@[simp] theorem HasClosedMajorant_def (y : ℕ) (w : ℕ) :
    HasClosedMajorant y w = (((Mbound y w : ℕ) : ℝ) ≤ Mc y) := rfl

/--
Accounting-specialized real closed-majorant target.
-/
def HasClosedMajorantOfAccounting {C : Context} (A : WitnessAccounting C) : Prop :=
  ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y

@[simp] theorem HasClosedMajorantOfAccounting_def {C : Context} (A : WitnessAccounting C) :
    HasClosedMajorantOfAccounting A =
      (((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y) := rfl

/--
Direct constructor for the real closed-majorant interface.
-/
theorem hasClosedMajorant_of_assumption (y w : ℕ)
    (h : ((Mbound y w : ℕ) : ℝ) ≤ Mc y) :
    HasClosedMajorant y w := by
  exact h

/--
Direct constructor for the accounting-specialized real closed-majorant interface.
-/
theorem hasClosedMajorantOfAccounting_of_assumption {C : Context} (A : WitnessAccounting C)
    (h : ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y) :
    HasClosedMajorantOfAccounting A := by
  exact h

/--
Elimination form of the real closed-majorant interface.
-/
theorem closedMajorant_bound (y w : ℕ)
    (h : HasClosedMajorant y w) :
    ((Mbound y w : ℕ) : ℝ) ≤ Mc y := by
  exact h

/--
Elimination form of the accounting-specialized real closed-majorant interface.
-/
theorem closedMajorantOfAccounting_bound {C : Context} (A : WitnessAccounting C)
    (h : HasClosedMajorantOfAccounting A) :
    ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y := by
  exact h

/--
Pipeline-facing real bridge:
from the accounting interface, recover the real-valued structural domination
by `Mc`.

This is the theorem that downstream analytic files should use as entry point.
-/
theorem MboundOfAccounting_cast_le_Mc {C : Context} (A : WitnessAccounting C)
    (hclosed : HasClosedMajorantOfAccounting A) :
    ((MboundOfAccounting A : ℕ) : ℝ) ≤ Mc C.y := by
  exact closedMajorantOfAccounting_bound A hclosed

/--
Non-accounting real bridge:
from the real interface, recover the current Case B supply bound dominated by `Mc`.
-/
theorem Mbound_cast_le_Mc (y w : ℕ)
    (hclosed : HasClosedMajorant y w) :
    ((Mbound y w : ℕ) : ℝ) ≤ Mc y := by
  exact closedMajorant_bound y w hclosed

/--
The closed majorant also dominates the natural supply bound once the
corresponding real-valued interface has been established.

This is a terminal discretization step; it should not be used as the analytic
comparison layer.
-/
theorem Mbound_le_McNat_of_closedMajorant (y w : ℕ)
    (h : HasClosedMajorant y w) :
    Mbound y w ≤ McNat y := by
  rw [McNat_def]
  exact_mod_cast (closedMajorant_bound y w h).trans (Nat.le_ceil (Mc y))

/--
Accounting-specialized terminal discrete domination form.

This is the discrete endpoint corresponding to `MboundOfAccounting_cast_le_Mc`.
-/
theorem MboundOfAccounting_le_McNat_of_closedMajorant {C : Context} (A : WitnessAccounting C)
    (h : HasClosedMajorantOfAccounting A) :
    MboundOfAccounting A ≤ McNat C.y := by
  rw [McNat_def]
  exact_mod_cast (closedMajorantOfAccounting_bound A h).trans (Nat.le_ceil (Mc C.y))

end CaseB
end Lehmer