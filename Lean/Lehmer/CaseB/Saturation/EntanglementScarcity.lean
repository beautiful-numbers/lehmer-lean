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
open Classical

/--
A witness is counted as entangled when the accounting datum classifies it on the
entangled side.

This remains a **local classified** notion attached to a `WitnessAccounting C`.
It is not meant to classify cumulatively all pivots of an entire generic chain
in the initial context `C`.
-/
def IsEntangledWitness {C : Context} (A : WitnessAccounting C) (p : ℕ) : Prop :=
  ∃ hp : p ∈ witnessSet C A, ∃ hent : EntangledWitness C p,
    (A.hclassified p hp).2 = Or.inr hent

/--
The entangled witness set extracted from a witness accounting datum.

This is a **local classified** extraction from `WitnessAccounting C`. It should
be distinguished from the honest cumulative chain-side object
`genericChainWitnessSet`, which only records cumulative support membership and
cardinality data, not a full reclassification of all pivots in the initial
context.
-/
noncomputable def entangledWitnessSet {C : Context} (A : WitnessAccounting C) : Finset ℕ := by
  classical
  exact (witnessSet C A).filter (fun p => IsEntangledWitness A p)

@[simp] theorem entangledWitnessSet_def {C : Context} (A : WitnessAccounting C) :
    entangledWitnessSet A =
      (witnessSet C A).filter (fun p => IsEntangledWitness A p) := by
  classical
  rfl

/--
Every entangled witness belongs to the ambient witness set.
-/
theorem mem_witnessSet_of_mem_entangledWitnessSet {C : Context}
    (A : WitnessAccounting C) {p : ℕ}
    (hp : p ∈ entangledWitnessSet A) :
    p ∈ witnessSet C A := by
  classical
  exact (Finset.mem_filter.mp hp).1

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
  classical
  rcases (Finset.mem_filter.mp hp).2 with ⟨hpW, hent, _⟩
  exact hent

/--
The entangled witness set is support-bounded.
-/
theorem card_entangledWitnessSet_le_supportCard {C : Context}
    (A : WitnessAccounting C) :
    supportCard (entangledWitnessSet A) ≤ supportCard C.S := by
  classical
  have hsub :
      entangledWitnessSet A ⊆ witnessSet C A := by
    intro p hp
    exact mem_witnessSet_of_mem_entangledWitnessSet A hp
  have h1 : supportCard (entangledWitnessSet A) ≤ supportCard (witnessSet C A) := by
    simpa [supportCard] using Finset.card_le_card hsub
  exact le_trans h1 (card_witnessSet_le_supportCard A)

/--
Entanglement scarcity predicate.

This remains the **local classified** scarcity interface attached to
`WitnessAccounting C`. For cumulative honest chain-side scarcity data, use the
profiles introduced below.
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
  classical
  ext q
  constructor
  · intro hq
    have hqW :
        q ∈ witnessSet C (singletonGenericWitnessAccounting C p hp hgen) := by
      exact mem_witnessSet_of_mem_entangledWitnessSet _ hq
    have hqeq : q = p := by
      simpa [witnessSet, singletonGenericWitnessAccounting, singletonWitnessPack] using hqW
    subst q
    rcases (Finset.mem_filter.mp hq).2 with ⟨hpW, hent, _hEq⟩
    exfalso
    exact contextGeneric_not_entangled hgen hent
  · intro hq
    simp at hq

/--
A singleton entangled witness accounting datum has witness set equal to its
entangled witness set.
-/
theorem entangledWitnessSet_singletonEntangled_eq (C : Context) (p : ℕ)
    (hp : Removable C.S p) (hent : ContextEntangledGain C p) :
    entangledWitnessSet (singletonEntangledWitnessAccounting C p hp hent) =
      witnessSet C (singletonEntangledWitnessAccounting C p hp hent) := by
  classical
  ext q
  constructor
  · intro hq
    exact mem_witnessSet_of_mem_entangledWitnessSet _ hq
  · intro hq
    have hqeq : q = p := by
      simp [witnessSet, singletonEntangledWitnessAccounting, singletonWitnessPack] at hq
      exact hq
    subst q
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simp [witnessSet, singletonEntangledWitnessAccounting, singletonWitnessPack]
    · refine ⟨?_, hent, rfl⟩
      · simp [witnessSet, singletonEntangledWitnessAccounting, singletonWitnessPack]

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

/--
Honest cumulative scarcity profile of a generic chain.

This is the cumulative witness-side object compatible with the separation
introduced in `WitnessAccounting.lean`: it remembers the cumulative witness set,
its support inclusion, and its cardinality bound, without pretending to
reclassify the whole chain in the initial context.
-/
structure GenericChainScarcityProfile (C : Context) where
  terminal : Context
  cumulativeWitnessSet : Finset ℕ
  hsub : cumulativeWitnessSet ⊆ C.S
  hcard : supportCard cumulativeWitnessSet ≤ supportCard C.S

/--
Canonical cumulative scarcity profile induced by a generic chain.
-/
def genericChainScarcityProfile_of_chain
    {C D : Context} (Γ : GenericChain C D) :
    GenericChainScarcityProfile C :=
  { terminal := D
    cumulativeWitnessSet := genericChainWitnessSet Γ
    hsub := genericChainWitnessSet_subset_support Γ
    hcard := card_genericChainWitnessSet_le_supportCard Γ }

/--
Terminal cumulative scarcity profile induced by a generic chain to saturation.
-/
structure GenericChainToSaturatedScarcityProfile (C : Context) where
  satChain : GenericChainToSaturated C
  cumulativeWitnessSet : Finset ℕ
  hsub : cumulativeWitnessSet ⊆ C.S
  hcard : supportCard cumulativeWitnessSet ≤ supportCard C.S

/--
Canonical terminal cumulative scarcity profile from a saturated generic chain.
-/
def genericChainToSaturatedScarcityProfile_of_chain
    {C : Context} (G : GenericChainToSaturated C) :
    GenericChainToSaturatedScarcityProfile C :=
  { satChain := G
    cumulativeWitnessSet := genericChainWitnessSet G.chain
    hsub := genericChainWitnessSet_subset_support G.chain
    hcard := card_genericChainWitnessSet_le_supportCard G.chain }

/--
Terminal cumulative scarcity profile induced by a generic chain to lock.
-/
structure GenericChainToSSLockScarcityProfile (C : Context) where
  lockChain : GenericChainToSSLock C
  cumulativeWitnessSet : Finset ℕ
  hsub : cumulativeWitnessSet ⊆ C.S
  hcard : supportCard cumulativeWitnessSet ≤ supportCard C.S

/--
Canonical terminal cumulative scarcity profile from a lock chain.
-/
def genericChainToSSLockScarcityProfile_of_chain
    {C : Context} (G : GenericChainToSSLock C) :
    GenericChainToSSLockScarcityProfile C :=
  { lockChain := G
    cumulativeWitnessSet := genericChainWitnessSet G.chain
    hsub := genericChainWitnessSet_subset_support G.chain
    hcard := card_genericChainWitnessSet_le_supportCard G.chain }

/--
Mixed bridge profile exposing both:
- the local entangled reading extracted from the minimal classified accounting,
- and the honest cumulative witness set of the whole generic chain.
-/
structure GenericChainEntanglementBridgeProfile (C : Context) where
  terminal : Context
  localAccounting : WitnessAccounting C
  entangledLocalSet : Finset ℕ
  cumulativeWitnessSet : Finset ℕ
  hlocalSub : entangledLocalSet ⊆ C.S
  hcumulativeSub : cumulativeWitnessSet ⊆ C.S
  hlocalCard : supportCard entangledLocalSet ≤ supportCard C.S
  hcumulativeCard : supportCard cumulativeWitnessSet ≤ supportCard C.S

/--
Canonical mixed entanglement bridge profile associated to a generic chain.
-/
noncomputable def genericChainEntanglementBridgeProfile_of_chain
    {C D : Context} (Γ : GenericChain C D) :
    GenericChainEntanglementBridgeProfile C :=
  { terminal := D
    localAccounting := witnessAccountingOfGenericChain Γ
    entangledLocalSet := entangledWitnessSet (witnessAccountingOfGenericChain Γ)
    cumulativeWitnessSet := genericChainWitnessSet Γ
    hlocalSub := by
      intro p hp
      exact mem_support_of_mem_entangledWitnessSet
        (witnessAccountingOfGenericChain Γ) hp
    hcumulativeSub := genericChainWitnessSet_subset_support Γ
    hlocalCard := card_entangledWitnessSet_le_supportCard
      (witnessAccountingOfGenericChain Γ)
    hcumulativeCard := card_genericChainWitnessSet_le_supportCard Γ }

/--
Support-boundedness of the cumulative witness set of a generic chain.
-/
theorem supportCard_cumulativeWitnessSet_of_genericChain_le_supportCard
    {C D : Context} (Γ : GenericChain C D) :
    supportCard (genericChainWitnessSet Γ) ≤ supportCard C.S := by
  exact card_genericChainWitnessSet_le_supportCard Γ

/--
Support-boundedness of the cumulative witness set of a generic chain to
saturation.
-/
theorem supportCard_cumulativeWitnessSet_of_genericChainToSaturated_le_supportCard
    {C : Context} (G : GenericChainToSaturated C) :
    supportCard (genericChainWitnessSet G.chain) ≤ supportCard C.S := by
  exact card_genericChainWitnessSet_le_supportCard G.chain

/--
Support-boundedness of the cumulative witness set of a generic chain to lock.
-/
theorem supportCard_cumulativeWitnessSet_of_genericChainToSSLock_le_supportCard
    {C : Context} (G : GenericChainToSSLock C) :
    supportCard (genericChainWitnessSet G.chain) ≤ supportCard C.S := by
  exact card_genericChainWitnessSet_le_supportCard G.chain

/--
Lock-side mixed entanglement bridge profile.
-/
structure SSLockEntanglementBridgeProfile (C : Context) where
  lockChain : GenericChainToSSLock C
  localAccounting : WitnessAccounting C
  entangledLocalSet : Finset ℕ
  cumulativeWitnessSet : Finset ℕ
  hlocalCard : supportCard entangledLocalSet ≤ supportCard C.S
  hcumulativeCard : supportCard cumulativeWitnessSet ≤ supportCard C.S

/--
Canonical lock-side mixed entanglement bridge profile.
-/
noncomputable def ssLockEntanglementBridgeProfile_of_chain
    {C : Context} (G : GenericChainToSSLock C) :
    SSLockEntanglementBridgeProfile C :=
  { lockChain := G
    localAccounting := witnessAccountingOfGenericChainToSSLock G
    entangledLocalSet := entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)
    cumulativeWitnessSet := genericChainWitnessSet G.chain
    hlocalCard := card_entangledWitnessSet_of_genericChainToSSLock_le_supportCard G
    hcumulativeCard := card_genericChainWitnessSet_le_supportCard G.chain }

end CaseB
end Lehmer