-- FILE: Lean/Lehmer/CaseB/Saturation/WitnessAccounting.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
- Lehmer.CaseB.Saturation.GenericChains : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.GenericChains

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
A witness package attached to a Case B context.

At the current saturation-accounting stage, witnesses are represented as a
finite subset of the current support together with the explicit proof that the
subset is contained in the support.
-/
structure WitnessPack (C : Context) where
  W : Finset ℕ
  hsub : W ⊆ C.S

/--
Underlying witness set.
-/
abbrev witnesses (C : Context) (P : WitnessPack C) : Finset ℕ :=
  P.W

@[simp] theorem witnesses_def (C : Context) (P : WitnessPack C) :
    witnesses C P = P.W := rfl

/--
The empty witness package.
-/
def emptyWitnessPack (C : Context) : WitnessPack C where
  W := ∅
  hsub := by intro p hp; simpa using hp

@[simp] theorem emptyWitnessPack_witnesses (C : Context) :
    (emptyWitnessPack C).W = ∅ := rfl

/--
Singleton witness package from a support element.
-/
def singletonWitnessPack (C : Context) (p : ℕ) (hp : p ∈ C.S) : WitnessPack C where
  W := {p}
  hsub := by
    intro q hq
    simpa using (Finset.mem_singleton.mp hq).symm ▸ hp

@[simp] theorem singletonWitnessPack_mem (C : Context) (p : ℕ) (hp : p ∈ C.S) :
    p ∈ (singletonWitnessPack C p hp).W := by
  simp [singletonWitnessPack]

/--
Union of witness packages over the same context.
-/
def unionWitnessPack (C : Context) (P Q : WitnessPack C) : WitnessPack C where
  W := P.W ∪ Q.W
  hsub := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact P.hsub hp
    · exact Q.hsub hp

@[simp] theorem unionWitnessPack_witnesses (C : Context) (P Q : WitnessPack C) :
    (unionWitnessPack C P Q).W = P.W ∪ Q.W := rfl

/--
Every witness belongs to the ambient support.
-/
theorem mem_support_of_mem_witnesses {C : Context} (P : WitnessPack C)
    {p : ℕ} (hp : p ∈ P.W) :
    p ∈ C.S := by
  exact P.hsub hp

/--
Witness cardinality is bounded by support cardinality.
-/
theorem card_witnesses_le_supportCard {C : Context} (P : WitnessPack C) :
    supportCard P.W ≤ supportCard C.S := by
  simpa [supportCard] using Finset.card_le_card P.hsub

/--
A witness pack is nonempty if its witness set is nonempty.
-/
def WitnessNonempty {C : Context} (P : WitnessPack C) : Prop :=
  P.W.Nonempty

@[simp] theorem WitnessNonempty_def {C : Context} (P : WitnessPack C) :
    WitnessNonempty P = P.W.Nonempty := rfl

/--
A prime is witness-compatible with a context if it is a removable support
element.

This is the minimal support-side accounting notion needed before the later
lock/scarcity refinements are introduced.
-/
def WitnessCompatible (C : Context) (p : ℕ) : Prop :=
  Removable C.S p

@[simp] theorem WitnessCompatible_def (C : Context) (p : ℕ) :
    WitnessCompatible C p = Removable C.S p := rfl

/--
A witness prime is generic if it satisfies the generic-side gain criterion.
-/
def GenericWitness (C : Context) (p : ℕ) : Prop :=
  ContextGenericGain C p

/--
A witness prime is entangled if it satisfies the entangled-side gain criterion.
-/
def EntangledWitness (C : Context) (p : ℕ) : Prop :=
  ContextEntangledGain C p

@[simp] theorem GenericWitness_def (C : Context) (p : ℕ) :
    GenericWitness C p = ContextGenericGain C p := rfl

@[simp] theorem EntangledWitness_def (C : Context) (p : ℕ) :
    EntangledWitness C p = ContextEntangledGain C p := rfl

/--
A witness accounting datum records a witness set together with a pointwise
classification on that set.

At this stage we only require that every witness is support-compatible and is
classified either as generic or as entangled.
-/
structure WitnessAccounting (C : Context) where
  pack : WitnessPack C
  hclassified :
    ∀ p ∈ pack.W, WitnessCompatible C p ∧ (GenericWitness C p ∨ EntangledWitness C p)

/--
Underlying witness set of an accounting datum.
-/
abbrev witnessSet (C : Context) (A : WitnessAccounting C) : Finset ℕ :=
  A.pack.W

@[simp] theorem witnessSet_def (C : Context) (A : WitnessAccounting C) :
    witnessSet C A = A.pack.W := rfl

/--
The empty witness accounting datum.
-/
def emptyWitnessAccounting (C : Context) : WitnessAccounting C where
  pack := emptyWitnessPack C
  hclassified := by
    intro p hp
    simpa using hp

/--
Every witness in a witness accounting datum belongs to the support.
-/
theorem mem_support_of_mem_witnessSet {C : Context} (A : WitnessAccounting C)
    {p : ℕ} (hp : p ∈ witnessSet C A) :
    p ∈ C.S := by
  exact A.pack.hsub hp

/--
The witness set of an accounting datum is cardinality-bounded by the support.
-/
theorem card_witnessSet_le_supportCard {C : Context} (A : WitnessAccounting C) :
    supportCard (witnessSet C A) ≤ supportCard C.S := by
  exact card_witnesses_le_supportCard A.pack

/--
A singleton generic witness accounting datum.
-/
def singletonGenericWitnessAccounting (C : Context) (p : ℕ)
    (hp : Removable C.S p) (hgen : ContextGenericGain C p) :
    WitnessAccounting C where
  pack := singletonWitnessPack C p hp
  hclassified := by
    intro q hq
    have hq' : q = p := by simpa [singletonWitnessPack] using hq
    subst hq'
    exact ⟨hp, Or.inl hgen⟩

/--
A singleton entangled witness accounting datum.
-/
def singletonEntangledWitnessAccounting (C : Context) (p : ℕ)
    (hp : Removable C.S p) (hent : ContextEntangledGain C p) :
    WitnessAccounting C where
  pack := singletonWitnessPack C p hp
  hclassified := by
    intro q hq
    have hq' : q = p := by simpa [singletonWitnessPack] using hq
    subst hq'
    exact ⟨hp, Or.inr hent⟩

/--
A generic step in a generic chain yields a singleton witness accounting datum.
-/
def witnessAccountingOfGenericStep {C : Context} (s : GenericStepData C) :
    WitnessAccounting C :=
  singletonGenericWitnessAccounting C s.p
    (by
      rcases s.hstep with ⟨hp, _⟩
      exact hp)
    s.hgeneric

/--
A generic chain induces a witness accounting datum on its initial context by
recording the head prime of the chain when present, and the empty set when the
chain is trivial.

This is the minimal accounting interface needed before later files enrich the
counting argument across longer chains.
-/
def witnessAccountingOfGenericChain {C D : Context} (Γ : GenericChain C D) :
    WitnessAccounting C :=
  match Γ with
  | .nil _ => emptyWitnessAccounting C
  | .cons s _ => witnessAccountingOfGenericStep s

/--
The witness accounting of a trivial generic chain is empty.
-/
@[simp] theorem witnessAccountingOfGenericChain_nil (C : Context) :
    witnessAccountingOfGenericChain (GenericChain.nil C) = emptyWitnessAccounting C := rfl

/--
The witness accounting of a nontrivial generic chain contains the head prime.
-/
theorem head_mem_witnessAccountingOfGenericChain {C D : Context}
    (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    s.p ∈ witnessSet C (witnessAccountingOfGenericChain (GenericChain.cons s Γ)) := by
  simp [witnessAccountingOfGenericChain, witnessAccountingOfGenericStep,
    witnessSet, singletonWitnessPack]

/--
The head prime of a generic chain is support-compatible.
-/
theorem head_witnessCompatible_of_genericChain {C D : Context}
    (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    WitnessCompatible C s.p := by
  rcases s.hstep with ⟨hp, _⟩
  exact hp

/--
The head prime of a generic chain is generically classified.
-/
theorem head_genericWitness_of_genericChain {C D : Context}
    (s : GenericStepData C) (Γ : GenericChain s.C' D) :
    GenericWitness C s.p := by
  exact s.hgeneric

/--
The witness accounting induced by a generic chain is support-bounded.
-/
theorem card_witnessAccountingOfGenericChain_le_supportCard {C D : Context}
    (Γ : GenericChain C D) :
    supportCard (witnessSet C (witnessAccountingOfGenericChain Γ)) ≤ supportCard C.S := by
  exact card_witnessSet_le_supportCard (witnessAccountingOfGenericChain Γ)

/--
A generic chain to saturation induces a support-bounded witness accounting
datum on the initial context.
-/
def witnessAccountingOfGenericChainToSaturated {C : Context}
    (G : GenericChainToSaturated C) :
    WitnessAccounting C :=
  witnessAccountingOfGenericChain G.chain

/--
The witness accounting induced by a generic chain to saturation is
support-bounded.
-/
theorem card_witnessAccountingOfGenericChainToSaturated_le_supportCard
    {C : Context} (G : GenericChainToSaturated C) :
    supportCard (witnessSet C (witnessAccountingOfGenericChainToSaturated G)) ≤ supportCard C.S := by
  exact card_witnessAccountingOfGenericChain_le_supportCard G.chain

end CaseB
end Lehmer