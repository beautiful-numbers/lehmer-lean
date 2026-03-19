-- FILE: Lean/Lehmer/CaseC/GapClosure/Bootstrap.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseC.GapClosure.Omegahat : def thm
-/

import Lehmer.Prelude
import Lehmer.CaseC.GapClosure.Omegahat

namespace Lehmer
namespace CaseC
namespace GapClosure

/--
The bootstrap consistency condition for Case C at parameters `(y, W)`.

This is the abstract inequality `Ω̂(y, W) < W` that closes the gap-to-closure
pipeline before the residual state-machine layer.
-/
def BootstrapConsistent (y W : ℕ) : Prop :=
  Omegahat y W < W

@[simp] theorem BootstrapConsistent_def (y W : ℕ) :
    BootstrapConsistent y W = (Omegahat y W < W) := rfl

/--
A direct alias-free form of the bootstrap consistency condition.
-/
theorem bootstrapConsistent_iff (y W : ℕ) :
    BootstrapConsistent y W ↔ omegahat y W < W := by
  rfl

/--
If the bootstrap consistency condition holds, then the support-cardinality
bound `Ω̂(y, W)` is strictly below `W`.
-/
theorem omegahat_lt_of_bootstrapConsistent {y W : ℕ}
    (h : BootstrapConsistent y W) :
    Omegahat y W < W := by
  exact h

/--
Interface form: once bootstrap consistency has been established, it can be
reused under the canonical file-local name.
-/
theorem bootstrapConsistency_of_assumption (y W : ℕ)
    (h : BootstrapConsistent y W) :
    BootstrapConsistent y W := by
  exact h

/--
Equivalent paper-style form of the previous interface lemma.
-/
theorem omegahat_lt_W_of_assumption (y W : ℕ)
    (h : BootstrapConsistent y W) :
    Omegahat y W < W := by
  exact h

/--
A weak numerical consequence of bootstrap consistency.
-/
theorem omegahat_le_pred_of_bootstrapConsistent {y W : ℕ}
    (_hW : 0 < W) (h : BootstrapConsistent y W) :
    Omegahat y W ≤ W - 1 := by
  exact Nat.le_pred_of_lt h

end GapClosure
end CaseC
end Lehmer