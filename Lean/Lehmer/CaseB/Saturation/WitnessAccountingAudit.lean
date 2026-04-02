-- FILE: Lean/Lehmer/CaseB/Saturation/WitnessAccountingAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Audit-facing alias for a witness package on a Case B context.

This is only a semantic wrapper name for audit readability.
It does not redefine the underlying main object.
-/
abbrev WitnessPackAudit (C : Context) := WitnessPack C

/--
Audit-facing alias for a witness accounting datum on a Case B context.

This is only a semantic wrapper name for audit readability.
It does not redefine the underlying main object.
-/
abbrev WitnessAccountingAudit (C : Context) := WitnessAccounting C

@[simp] theorem WitnessPackAudit_def (C : Context) :
    WitnessPackAudit C = WitnessPack C := rfl

@[simp] theorem WitnessAccountingAudit_def (C : Context) :
    WitnessAccountingAudit C = WitnessAccounting C := rfl

/--
Audit-facing alias for the witness set attached to a witness package.
-/
abbrev witnessesAudit (C : Context) (P : WitnessPackAudit C) : Finset ℕ :=
  witnesses C P

@[simp] theorem witnessesAudit_def (C : Context) (P : WitnessPackAudit C) :
    witnessesAudit C P = P.W := rfl

/--
Audit-facing alias for the witness set attached to a witness accounting datum.
-/
abbrev witnessSetAudit (C : Context) (A : WitnessAccountingAudit C) : Finset ℕ :=
  witnessSet C A

@[simp] theorem witnessSetAudit_def (C : Context) (A : WitnessAccountingAudit C) :
    witnessSetAudit C A = A.pack.W := rfl

/--
Support soundness for witness packages:
every witness stays inside the ambient support.
-/
theorem witnessesAudit_support_sound
    {C : Context} (P : WitnessPackAudit C) {p : ℕ}
    (hp : p ∈ witnessesAudit C P) :
    p ∈ C.S := by
  exact mem_support_of_mem_witnesses P hp

/--
Support soundness for witness accountings:
every recorded witness stays inside the ambient support.
-/
theorem witnessSetAudit_support_sound
    {C : Context} (A : WitnessAccountingAudit C) {p : ℕ}
    (hp : p ∈ witnessSetAudit C A) :
    p ∈ C.S := by
  exact mem_support_of_mem_witnessSet A hp

/--
Cardinal soundness for witness packages:
the witness-side cardinality is bounded by the support cardinality.
-/
theorem witnessesAudit_card_le_supportCard
    {C : Context} (P : WitnessPackAudit C) :
    supportCard (witnessesAudit C P) ≤ supportCard C.S := by
  simpa [witnessesAudit] using card_witnesses_le_supportCard P

/--
Cardinal soundness for witness accountings:
the witness-set cardinality is bounded by the support cardinality.
-/
theorem witnessAccountingAudit_card_le_supportCard
    {C : Context} (A : WitnessAccountingAudit C) :
    supportCard (witnessSetAudit C A) ≤ supportCard C.S := by
  simpa [witnessSetAudit] using card_witnessSet_le_supportCard A

/--
Pointwise classification soundness:
every witness in an audit-facing accounting datum is support-compatible and is
classified either as generic or as entangled.
-/
theorem witnessAccountingAudit_classified
    {C : Context} (A : WitnessAccountingAudit C) {p : ℕ}
    (hp : p ∈ witnessSetAudit C A) :
    WitnessCompatible C p ∧ (GenericWitness C p ∨ EntangledWitness C p) := by
  simpa [witnessSetAudit] using A.hclassified p hp

/--
Compatibility soundness:
every witness recorded by an audit-facing accounting datum is witness-compatible.
-/
theorem witnessAccountingAudit_compatible
    {C : Context} (A : WitnessAccountingAudit C) {p : ℕ}
    (hp : p ∈ witnessSetAudit C A) :
    WitnessCompatible C p := by
  exact (witnessAccountingAudit_classified A hp).1

/--
Alternative soundness:
every witness recorded by an audit-facing accounting datum is classified either
as generic or as entangled.
-/
theorem witnessAccountingAudit_generic_or_entangled
    {C : Context} (A : WitnessAccountingAudit C) {p : ℕ}
    (hp : p ∈ witnessSetAudit C A) :
    GenericWitness C p ∨ EntangledWitness C p := by
  exact (witnessAccountingAudit_classified A hp).2

/--
Homogeneity certificate for the audit-facing witness accounting grammar:
an audit witness accounting datum is exactly a witness pack together with a
pointwise compatibility-and-classification condition.
-/
theorem witnessAccountingAudit_grammar
    {C : Context} (A : WitnessAccountingAudit C) :
    ∃ P : WitnessPackAudit C,
      witnessSetAudit C A = witnessesAudit C P ∧
      ∀ p ∈ witnessesAudit C P,
        WitnessCompatible C p ∧ (GenericWitness C p ∨ EntangledWitness C p) := by
  refine ⟨A.pack, rfl, ?_⟩
  intro p hp
  simpa [witnessesAudit, witnessSetAudit] using A.hclassified p hp

/--
The empty audit-facing witness accounting has empty witness set.
-/
@[simp] theorem emptyWitnessAccountingAudit_witnessSet
    (C : Context) :
    witnessSetAudit C (emptyWitnessAccounting C) = ∅ := by
  rfl

/--
Support soundness for the witness accounting induced by a generic chain.
-/
theorem genericChain_witnessAccountingAudit_support_sound
    {C D : Context} (Γ : GenericChain C D) {p : ℕ}
    (hp : p ∈ witnessSetAudit C (witnessAccountingOfGenericChain Γ)) :
    p ∈ C.S := by
  exact witnessSetAudit_support_sound (witnessAccountingOfGenericChain Γ) hp

/--
Cardinal soundness for the witness accounting induced by a generic chain.
-/
theorem genericChain_witnessAccountingAudit_card_le_supportCard
    {C D : Context} (Γ : GenericChain C D) :
    supportCard (witnessSetAudit C (witnessAccountingOfGenericChain Γ)) ≤ supportCard C.S := by
  simpa [witnessSetAudit] using
    card_witnessAccountingOfGenericChain_le_supportCard Γ

/--
If a generic chain is nontrivial, its head prime is a valid witness in the
audit-facing witness accounting induced on the initial context.
-/
theorem genericChain_head_witnessAccountingAudit_sound
    {C D : Context} (s : GenericStepData C) (_Γ : GenericChain s.C' D) :
    s.p ∈ witnessSetAudit C (witnessAccountingOfGenericChain (GenericChain.cons s _Γ)) ∧
    WitnessCompatible C s.p ∧
    GenericWitness C s.p := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [witnessSetAudit] using
      head_mem_witnessAccountingOfGenericChain s _Γ
  · simpa using head_witnessCompatible_of_genericChain s _Γ
  · simpa using head_genericWitness_of_genericChain s _Γ

/--
Support soundness for the witness accounting induced by a generic chain to
saturation.
-/
theorem genericChainToSaturated_witnessAccountingAudit_support_sound
    {C : Context} (G : GenericChainToSaturated C) {p : ℕ}
    (hp : p ∈ witnessSetAudit C (witnessAccountingOfGenericChainToSaturated G)) :
    p ∈ C.S := by
  exact witnessSetAudit_support_sound
    (witnessAccountingOfGenericChainToSaturated G) hp

/--
Cardinal soundness for the witness accounting induced by a generic chain to
saturation.
-/
theorem genericChainToSaturated_witnessAccountingAudit_card_le_supportCard
    {C : Context} (G : GenericChainToSaturated C) :
    supportCard (witnessSetAudit C (witnessAccountingOfGenericChainToSaturated G)) ≤
      supportCard C.S := by
  simpa [witnessSetAudit] using
    card_witnessAccountingOfGenericChainToSaturated_le_supportCard G

end CaseB
end Lehmer