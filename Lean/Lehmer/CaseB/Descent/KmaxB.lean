-- FILE: Lean/Lehmer/CaseB/Descent/KmaxB.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Support.PotentialP2 : def param
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Parameters : def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Support.PotentialP2
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.P2Decrease

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Support

/--
The Case B descent budget.

This is the actual parameter package exported by `CaseB.Parameters`.
It replaces the old placeholder `KmaxB y := y`.
-/
noncomputable def KmaxB (y : ℕ) : ℕ :=
  kappaB y

@[simp] theorem KmaxB_def (y : ℕ) :
    KmaxB y = kappaB y := rfl

/--
Expanded paper-style form of the Case B descent budget.
-/
theorem KmaxB_eq_ceil_three_log_four (y : ℕ) :
    KmaxB y = Nat.ceil (3 * (Real.log (yB y))^4) := by
  rw [KmaxB]
  exact kappaB_eq_ceil_three_log_four y

/--
The descent budget is nonnegative.
-/
theorem KmaxB_nonneg (y : ℕ) :
    0 ≤ KmaxB y := by
  rw [KmaxB]
  exact kappaB_nonneg y

/--
The canonical length measure attached to a support at level `y`.

At the current Case B descent stage, we use the support cardinality as the
discrete descent-size proxy that strictly drops under controlled removal.
-/
def descentLength (S : Finset ℕ) (_y : ℕ) : ℕ :=
  supportCard S

@[simp] theorem descentLength_def (S : Finset ℕ) (y : ℕ) :
    descentLength S y = supportCard S := rfl

/--
Context-level version of the descent-length measure.
-/
def contextDescentLength (C : Context) : ℕ :=
  descentLength C.S C.y

@[simp] theorem contextDescentLength_def (C : Context) :
    contextDescentLength C = descentLength C.S C.y := rfl

/--
Under a removable controlled removal, the descent-length proxy drops by one.
-/
theorem descentLength_remove_of_removable {S : Finset ℕ} {p y : ℕ}
    (hp : Removable S p) :
    descentLength (remove S p) y = descentLength S y - 1 := by
  simpa [descentLength] using supportCard_remove_of_removable hp

/--
Context-level version of the previous length-drop statement.
-/
theorem contextDescentLength_next_of_removable (C : Context) {p : ℕ}
    (hp : Removable C.S p) :
    contextDescentLength (nextContext C p) = contextDescentLength C - 1 := by
  simpa [contextDescentLength, descentLength] using
    supportCard_remove_of_removable hp

/--
If the support cardinality is bounded by `KmaxB y`, then the descent-length
proxy is bounded by `KmaxB y`.
-/
theorem descentLength_le_KmaxB_of_bound
    (S : Finset ℕ) (y : ℕ)
    (hbound : supportCard S ≤ KmaxB y) :
    descentLength S y ≤ KmaxB y := by
  simpa [descentLength] using hbound

/--
Context-level version of the previous descent bound.
-/
theorem contextDescentLength_le_KmaxB_of_bound
    (C : Context)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    contextDescentLength C ≤ KmaxB C.y := by
  simpa [contextDescentLength, descentLength] using hbound

/--
Interface form of the conditional descent bound.
-/
theorem exists_descent_bound_of_assumption
    (C : Context)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    contextDescentLength C ≤ KmaxB C.y := by
  simpa [contextDescentLength, descentLength] using hbound

/--
Any canonical controlled-removal step strictly decreases the discrete
descent-length proxy.
-/
theorem descentLength_strict_decrease_of_removable
    (S : Finset ℕ) (p y : ℕ) (hp : Removable S p) :
    descentLength (remove S p) y < descentLength S y := by
  have hEq := descentLength_remove_of_removable (y := y) hp
  have hPos : 0 < descentLength S y := by
    rw [descentLength]
    exact Finset.card_pos.mpr ⟨p, hp⟩
  omega

/--
Context-level version of strict decrease of the discrete descent-length proxy.
-/
theorem contextDescentLength_strict_decrease_of_removable
    (C : Context) (p : ℕ) (hp : Removable C.S p) :
    contextDescentLength (nextContext C p) < contextDescentLength C := by
  have hEq := contextDescentLength_next_of_removable C hp
  have hPos : 0 < contextDescentLength C := by
    rw [contextDescentLength, descentLength]
    exact Finset.card_pos.mpr ⟨p, hp⟩
  omega

end CaseB
end Lehmer