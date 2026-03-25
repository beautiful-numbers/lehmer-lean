-- FILE: Lean/Lehmer/CaseB/Saturation/EntanglementScarcity.lean
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
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
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
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SSLock

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
The entangled witness set extracted from a witness accounting datum.

At the current stage, entanglement scarcity is formulated as a support-bounded
subfamily of the witness set consisting of the primes classified on the
entangled side of the generic/entangled dichotomy.
-/
def entangledWitnessSet {C : Context} (A : WitnessAccounting C) : Finset ℕ :=
  (witnessSet C A).filter (fun p => EntangledWitness C p)

@[simp] theorem entangledWitnessSet_def {C : Context} (A : WitnessAccounting C) :
    entangledWitnessSet A =
      (witnessSet C A).filter (fun p => EntangledWitness C p) := rfl

/--
Every entangled witness belongs to the ambient witness set.
-/
theorem mem_witnessSet_of_mem_entangledWitnessSet {C : Context}
    (A : WitnessAccounting C) {p : ℕ}
    (hp : p ∈ entangledWitnessSet A) :
    p ∈ witnessSet C A := by
  simpa [entangledWitnessSet] using (Finset.mem_filter.mp hp).1

/--
Every entangled witness belongs to the ambient support.
-/
theorem mem_support_of_mem_entangledWitnessSet {C : Context}
    (A : WitnessAccounting C) {p : ℕ}
    (hp : p ∈ entangledWitnessSet A) :
    p ∈ C.S := by
  exact mem_support_of_mem_witnessSet A (mem_witnessSet_of_mem_entangledWitnessSet A hp)

/--
Every element of the entangled witness set is entangled.
-/
theorem entangledWitness_of_mem_entangledWitnessSet {C : Context}
    (A : WitnessAccounting C) {p : ℕ}
    (hp : p ∈ entangledWitnessSet A) :
    EntangledWitness C p := by
  exact (Finset.mem_filter.mp hp).2

/--
The entangled witness set is support-bounded.
-/
theorem card_entangledWitnessSet_le_supportCard {C : Context}
    (A : WitnessAccounting C) :
    supportCard (entangledWitnessSet A) ≤ supportCard C.S := by
  have hsub :
      entangledWitnessSet A ⊆ witnessSet C A := by
    intro p hp
    exact mem_witnessSet_of_mem_entangledWitnessSet A hp
  have h1 : supportCard (entangledWitnessSet A) ≤ supportCard (witnessSet C A) := by
    simpa [supportCard] using Finset.card_le_card hsub
  exact le_trans h1 (card_witnessSet_le_supportCard A)

/--
Entanglement scarcity predicate.

This is the finite-support scarcity interface: entangled witnesses form a
support-bounded set.
-/
def EntanglementScarce (C : Context) (A : WitnessAccounting C) : Prop :=
  supportCard (entangledWitnessSet A) ≤ supportCard C.S

@[simp] theorem EntanglementScarce_def (C : Context) (A : WitnessAccounting C) :
    EntanglementScarce C A =
      (supportCard (entangledWitnessSet A) ≤ supportCard C.S) := rfl

/--
Entanglement scarcity holds for every witness accounting datum.
-/
theorem entanglementScarce_of_witnessAccounting {C : Context}
    (A : WitnessAccounting C) :
    EntanglementScarce C A := by
  exact card_entangledWitnessSet_le_supportCard A

/--
The empty witness accounting datum is entanglement-scarce.
-/
theorem entanglementScarce_empty (C : Context) :
    EntanglementScarce C (emptyWitnessAccounting C) := by
  exact entanglementScarce_of_witnessAccounting (emptyWitnessAccounting C)

/--
A generic singleton witness accounting datum has empty entangled witness set.
-/
theorem entangledWitnessSet_singletonGeneric_empty (C : Context) (p : ℕ)
    (hp : Removable C.S p) (hgen : ContextGenericGain C p) :
    entangledWitnessSet (singletonGenericWitnessAccounting C p hp hgen) = ∅ := by
  ext q
  constructor
  · intro hq
    have hmem : q = p := by
      have hq' : q ∈ witnessSet C (singletonGenericWitnessAccounting C p hp hgen) := by
        exact (Finset.mem_filter.mp hq).1
      simpa [witnessSet, singletonGenericWitnessAccounting, singletonWitnessPack] using hq'
    subst hmem
    have hent : EntangledWitness C p := by
      exact (Finset.mem_filter.mp hq).2
    have hclass :
        WitnessCompatible C p ∧ (GenericWitness C p ∨ EntangledWitness C p) := by
      simpa [witnessSet, singletonGenericWitnessAccounting, singletonWitnessPack] using
        (singletonGenericWitnessAccounting C p hp hgen).hclassified p (by simp)
    rcases hclass.2 with hgeneric | hent'
    · exact False.elim (by
        change ContextEntangledGain C p at hent
        change ContextGenericGain C p at hgeneric
        trivial)
    · exact False.elim (by
        change ContextEntangledGain C p at hent
        exact False.elim (by trivial))
  · intro hq
    simpa using hq

/--
A singleton entangled witness accounting datum has witness set equal to its
entangled witness set.
-/
theorem entangledWitnessSet_singletonEntangled_eq (C : Context) (p : ℕ)
    (hp : Removable C.S p) (hent : ContextEntangledGain C p) :
    entangledWitnessSet (singletonEntangledWitnessAccounting C p hp hent) =
      witnessSet C (singletonEntangledWitnessAccounting C p hp hent) := by
  ext q
  simp [entangledWitnessSet, witnessSet, singletonEntangledWitnessAccounting, singletonWitnessPack]
  constructor
  · intro hq
    exact hq.1
  · intro hq
    have hq' : q = p := by simpa using hq
    subst hq'
    exact ⟨by simp, hent⟩

/--
The entangled witness set attached to a generic-chain witness accounting datum
is support-bounded.
-/
theorem card_entangledWitnessSet_of_genericChain_le_supportCard
    {C D : Context} (Γ : GenericChain C D) :
    supportCard (entangledWitnessSet (witnessAccountingOfGenericChain Γ)) ≤ supportCard C.S := by
  exact card_entangledWitnessSet_le_supportCard (witnessAccountingOfGenericChain Γ)

/--
The entangled witness set attached to a generic chain to lock is support-bounded.
-/
theorem card_entangledWitnessSet_of_genericChainToSSLock_le_supportCard
    {C : Context} (G : GenericChainToSSLock C) :
    supportCard (entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)) ≤
      supportCard C.S := by
  exact card_entangledWitnessSet_le_supportCard (witnessAccountingOfGenericChainToSSLock G)

/--
Entanglement scarcity for witness accounting induced by a generic chain to lock.
-/
theorem entanglementScarce_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C) :
    EntanglementScarce C (witnessAccountingOfGenericChainToSSLock G) := by
  exact card_entangledWitnessSet_of_genericChainToSSLock_le_supportCard G

end CaseB
end Lehmer