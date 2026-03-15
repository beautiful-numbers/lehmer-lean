-- FILE: Lean/Lehmer/CaseB/Descent/ControlledRemoval.lean
import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.Support.IncrementRatio
import Lehmer.Support.PotentialP2
import Lehmer.CaseB.Spec

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Lehmer.Support

/--
A prime `p` is removable from `S` in the minimal MVP-2 sense
if it belongs to the support.
Further structural conditions can be added later without changing
the role of this predicate in the descent skeleton.
-/
def Removable (S : Finset ℕ) (p : ℕ) : Prop :=
  p ∈ S

/--
The successor support obtained by controlled removal of `p`.
-/
def remove (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  S.erase p

/--
Context-level successor obtained by removing `p` from the support.
-/
def nextContext (C : Context) (p : ℕ) : Context :=
  ⟨C.y, remove C.S p⟩

@[simp] theorem Removable_def (S : Finset ℕ) (p : ℕ) :
    Removable S p = (p ∈ S) := rfl

@[simp] theorem remove_def (S : Finset ℕ) (p : ℕ) :
    remove S p = S.erase p := rfl

@[simp] theorem nextContext_y (C : Context) (p : ℕ) :
    (nextContext C p).y = C.y := rfl

@[simp] theorem nextContext_S (C : Context) (p : ℕ) :
    (nextContext C p).S = C.S.erase p := rfl

/--
A controlled removal step from `S` along `p`.
For MVP-2 this is just membership together with the successor support.
-/
def ControlledRemoval (S : Finset ℕ) (p : ℕ) (T : Finset ℕ) : Prop :=
  Removable S p ∧ T = remove S p

/--
Context-level controlled removal step.
-/
def ContextControlledRemoval (C : Context) (p : ℕ) (C' : Context) : Prop :=
  Removable C.S p ∧ C' = nextContext C p

@[simp] theorem ControlledRemoval_def (S : Finset ℕ) (p : ℕ) (T : Finset ℕ) :
    ControlledRemoval S p T = (Removable S p ∧ T = remove S p) := rfl

@[simp] theorem ContextControlledRemoval_def (C : Context) (p : ℕ) (C' : Context) :
    ContextControlledRemoval C p C' = (Removable C.S p ∧ C' = nextContext C p) := rfl

/--
If `p` is removable from `S`, then the canonical controlled-removal target
is `S.erase p`.
-/
theorem controlledRemoval_canonical (S : Finset ℕ) (p : ℕ) (hp : Removable S p) :
    ControlledRemoval S p (remove S p) := by
  exact ⟨hp, rfl⟩

/--
Context version of the canonical controlled-removal step.
-/
theorem contextControlledRemoval_canonical (C : Context) (p : ℕ)
    (hp : Removable C.S p) :
    ContextControlledRemoval C p (nextContext C p) := by
  exact ⟨hp, rfl⟩

/--
An element is absent from the successor support after erasure.
-/
@[simp] theorem not_mem_remove_self {S : Finset ℕ} {p : ℕ} :
    p ∉ remove S p := by
  simpa [remove]

/--
The successor support is contained in the original support.
-/
theorem remove_subset (S : Finset ℕ) (p : ℕ) :
    remove S p ⊆ S := by
  intro q hq
  simpa [remove] using Finset.mem_of_mem_erase hq

/--
The support cardinality drops by one under a removable controlled removal.
-/
theorem supportCard_remove_of_removable {S : Finset ℕ} {p : ℕ}
    (hp : Removable S p) :
    supportCard (remove S p) = supportCard S - 1 := by
  simpa [Removable, remove, supportCard, hp] using Finset.card_erase_of_mem hp

/--
Expanded form of the second potential after controlled removal.
This is the local algebraic target shape for later descent lemmas.
-/
theorem P2_remove_expand (S : Finset ℕ) (p y : ℕ) :
    P2 (remove S p) y =
      potentialP (remove S p) - epsilonB y * (supportCard (remove S p) : ℝ) := by
  rfl

/--
Context-level expanded form of the potential after controlled removal.
-/
theorem potential_nextContext_expand (C : Context) (p : ℕ) :
    potential (nextContext C p) =
      potentialP (remove C.S p) - epsilonB C.y * (supportCard (remove C.S p) : ℝ) := by
  rfl

/--
Stable MVP-2 placeholder for the local gain statement attached to a
controlled removal.

This isolates the intended shape of the descent step before the full
proof of strict decrease is supplied in later files.
-/
theorem controlledRemoval_gain_placeholder
    (S : Finset ℕ) (p y : ℕ) (hp : Removable S p) :
    P2 (remove S p) y < P2 S y := by
  simpa [Removable, remove] using
    P2_strict_decrease_placeholder S p y hp

end CaseB
end Lehmer