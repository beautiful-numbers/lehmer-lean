-- FILE: Lean/Lehmer/CaseB/Descent/ControlledRemoval.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.Support.IncrementRatio : def
- Lehmer.Support.PotentialP2 : def param
- Lehmer.CaseB.Spec : struct spec def
-/

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
A prime `p` is removable from `S` exactly when it belongs to the current
support.

At the present Case B descent stage, controlled removal is the canonical
support-erasure step. No extra placeholder side-condition is introduced here.
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
A controlled removal step from `S` along `p` to `T`.

This is the exact canonical erasure step: `p` must belong to `S`, and the next
support is `S.erase p`.
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
A controlled-removal target is uniquely determined.
-/
theorem controlledRemoval_target_unique {S T₁ T₂ : Finset ℕ} {p : ℕ}
    (h₁ : ControlledRemoval S p T₁)
    (h₂ : ControlledRemoval S p T₂) :
    T₁ = T₂ := by
  rcases h₁ with ⟨_, rfl⟩
  rcases h₂ with ⟨_, rfl⟩
  rfl

/--
A context-level controlled-removal successor is uniquely determined.
-/
theorem contextControlledRemoval_target_unique {C C₁ C₂ : Context} {p : ℕ}
    (h₁ : ContextControlledRemoval C p C₁)
    (h₂ : ContextControlledRemoval C p C₂) :
    C₁ = C₂ := by
  rcases h₁ with ⟨_, rfl⟩
  rcases h₂ with ⟨_, rfl⟩
  rfl

/--
An element is absent from the successor support after erasure.
-/
@[simp] theorem not_mem_remove_self {S : Finset ℕ} {p : ℕ} :
    p ∉ remove S p := by
  simp [remove]

/--
The successor support is contained in the original support.
-/
theorem remove_subset (S : Finset ℕ) (p : ℕ) :
    remove S p ⊆ S := by
  intro q hq
  simpa [remove] using Finset.mem_of_mem_erase hq

/--
Every element of the successor support is different from the removed element.
-/
theorem mem_remove_implies_ne {S : Finset ℕ} {p q : ℕ}
    (hq : q ∈ remove S p) :
    q ≠ p := by
  simpa [remove] using (Finset.ne_of_mem_erase hq)

/--
Every element of the successor support already belonged to the original support.
-/
theorem mem_remove_implies_mem {S : Finset ℕ} {p q : ℕ}
    (hq : q ∈ remove S p) :
    q ∈ S := by
  simpa [remove] using (Finset.mem_of_mem_erase hq)

/--
If `q` belongs to `S` and is different from `p`, then `q` survives the
controlled removal of `p`.
-/
theorem mem_remove_of_mem_of_ne {S : Finset ℕ} {p q : ℕ}
    (hq : q ∈ S) (hqp : q ≠ p) :
    q ∈ remove S p := by
  simpa [remove] using Finset.mem_erase.mpr ⟨hqp, hq⟩

/--
The support cardinality drops by one under a removable controlled removal.
-/
theorem supportCard_remove_of_removable {S : Finset ℕ} {p : ℕ}
    (hp : Removable S p) :
    supportCard (remove S p) = supportCard S - 1 := by
  simpa [Removable, remove, supportCard, hp] using Finset.card_erase_of_mem hp

/--
The support cardinality strictly decreases under a removable controlled removal.
-/
theorem supportCard_remove_lt_of_removable {S : Finset ℕ} {p : ℕ}
    (hp : Removable S p) :
    supportCard (remove S p) < supportCard S := by
  have hEq := supportCard_remove_of_removable hp
  have hPos : 0 < supportCard S := by
    exact Finset.card_pos.mpr ⟨p, hp⟩
  omega

/--
Context-level form of strict decrease of support cardinality.
-/
theorem supportCard_nextContext_lt_of_removable (C : Context) {p : ℕ}
    (hp : Removable C.S p) :
    supportCard (nextContext C p).S < supportCard C.S := by
  simpa using supportCard_remove_lt_of_removable hp

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
A context-level controlled-removal step preserves the Case B level.
-/
theorem ContextControlledRemoval_preserves_level
    {C C' : Context} {p : ℕ}
    (hstep : ContextControlledRemoval C p C') :
    C'.y = C.y := by
  rcases hstep with ⟨_, rfl⟩
  rfl

/--
A context-level controlled-removal step realizes the canonical erased support.
-/
theorem ContextControlledRemoval_support_eq
    {C C' : Context} {p : ℕ}
    (hstep : ContextControlledRemoval C p C') :
    C'.S = remove C.S p := by
  rcases hstep with ⟨_, rfl⟩
  rfl

end CaseB
end Lehmer