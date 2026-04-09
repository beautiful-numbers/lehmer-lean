-- FILE: Lean/Lehmer/CaseB/Saturation/SupplyBoundAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.WitnessAccountingAudit : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.WitnessAccountingAudit
import Lehmer.CaseB.Saturation.SupplyBound

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Audit-facing alias for the witness-side scarcity estimate.
-/
abbrev HasScarcityBoundAudit (C : Context) (A : WitnessAccountingAudit C) : Prop :=
  HasScarcityBound C A

/--
Audit-facing alias for the Case B supply bound.
-/
abbrev HasSupplyBoundAudit (C : Context) (A : WitnessAccountingAudit C) : Prop :=
  HasSupplyBound C A

/--
Audit-facing alias for the current Case B supply package.
-/
abbrev SupplyPackageAudit (C : Context) := SupplyPackage C

@[simp] theorem HasScarcityBoundAudit_def
    (C : Context) (A : WitnessAccountingAudit C) :
    HasScarcityBoundAudit C A = HasScarcityBound C A := rfl

@[simp] theorem HasSupplyBoundAudit_def
    (C : Context) (A : WitnessAccountingAudit C) :
    HasSupplyBoundAudit C A = HasSupplyBound C A := rfl

@[simp] theorem SupplyPackageAudit_def
    (C : Context) :
    SupplyPackageAudit C = SupplyPackage C := rfl

/--
Audit-facing expansion of the witness-side scarcity estimate.
-/
@[simp] theorem HasScarcityBoundAudit_iff
    (C : Context) (A : WitnessAccountingAudit C) :
    HasScarcityBoundAudit C A ↔
      witnessBudget A ≤ WboundOfAccounting A := by
  rfl

/--
Audit-facing expansion of the Case B supply bound.
-/
@[simp] theorem HasSupplyBoundAudit_iff
    (C : Context) (A : WitnessAccountingAudit C) :
    HasSupplyBoundAudit C A ↔
      supportCard C.S ≤ MboundOfAccounting A := by
  rfl

/--
Context soundness for audit-facing scarcity bounds:
the estimate is attached to the same ambient Case B context.
-/
theorem hasScarcityBoundAudit_context_sound
    (C : Context) (A : WitnessAccountingAudit C) :
    witnessBudget A ≤ WboundOfAccounting A := by
  simp

/--
Context soundness for audit-facing supply bounds:
the estimate is attached to the same ambient Case B context.
-/
theorem hasSupplyBoundAudit_context_sound
    (C : Context) (A : WitnessAccountingAudit C)
    (h : HasSupplyBoundAudit C A) :
    supportCard C.S ≤ MboundOfAccounting A := by
  simpa using h

/--
Witness-side soundness:
an audit-facing supply bound is indexed by a witness accounting datum whose
witness set stays inside the ambient support.
-/
theorem hasSupplyBoundAudit_witnessSet_support_sound
    {C : Context} (A : WitnessAccountingAudit C)
    (_h : HasSupplyBoundAudit C A) {p : ℕ}
    (hp : p ∈ witnessSetAudit C A) :
    p ∈ C.S := by
  exact witnessSetAudit_support_sound A hp

/--
Witness-side cardinal soundness:
the witness accounting attached to an audit-facing supply bound is support-bounded.
-/
theorem hasSupplyBoundAudit_witness_card_le_supportCard
    {C : Context} (A : WitnessAccountingAudit C)
    (_h : HasSupplyBoundAudit C A) :
    supportCard (witnessSetAudit C A) ≤ supportCard C.S := by
  exact witnessAccountingAudit_card_le_supportCard A

/--
Witness-side classification soundness:
every witness used by an audit-facing supply bound is support-compatible and
classified either as generic or as entangled.
-/
theorem hasSupplyBoundAudit_witness_classified
    {C : Context} (A : WitnessAccountingAudit C)
    (_h : HasSupplyBoundAudit C A) {p : ℕ}
    (hp : p ∈ witnessSetAudit C A) :
    WitnessCompatible C p ∧ (GenericWitness C p ∨ EntangledWitness C p) := by
  exact witnessAccountingAudit_classified A hp

/--
Audit-facing scarcity soundness:
every witness accounting datum satisfies the current abstract scarcity estimate.
-/
theorem witnessAccountingAudit_is_scarce
    (C : Context) (A : WitnessAccountingAudit C) :
    HasScarcityBoundAudit C A := by
  exact hasScarcityBound_of_accounting C A

/--
Audit-facing transport soundness:
an accounting-based saturated-support bound yields the corresponding `M`-bound.
-/
theorem supplyBoundAudit_transport_sound
    (C : Context) (A : WitnessAccountingAudit C)
    (hbound : supportCard C.S ≤ saturatedSupportBoundOfAccounting A) :
    supportCard C.S ≤ MboundOfAccounting A := by
  exact supportCard_le_Mbound_of_accounting C A hbound

/--
Audit-facing transport from scarcity and saturated-support control to the
supply-side terminal inequality.
-/
theorem hasSupplyBoundAudit_of_hasScarcityBoundAudit
    (C : Context) (A : WitnessAccountingAudit C)
    (hscarce : HasScarcityBoundAudit C A)
    (hbound : supportCard C.S ≤ saturatedSupportBoundOfAccounting A) :
    HasSupplyBoundAudit C A := by
  exact hasSupplyBound_of_hasScarcityBound C A hscarce hbound

/--
Audit-facing transport from the saturated-support bound to the supply bound.
-/
theorem saturatedSupportBoundAudit_implies_supplyBoundAudit
    (C : Context) (A : WitnessAccountingAudit C)
    (hbound : HasSaturatedSupportBound C A) :
    HasSupplyBoundAudit C A := by
  exact hasSupplyBound_of_saturatedSupportBound C A hbound

/--
A supply-side terminal inequality is immediately usable as a terminal
supply-side datum for the same context and witness accounting.
-/
theorem hasSupplyBoundAudit_terminal_usable
    (C : Context) (A : WitnessAccountingAudit C)
    (h : HasSupplyBoundAudit C A) :
    supportCard C.S ≤ MboundOfAccounting A := by
  simpa using h

/--
Homogeneous grammar for audit-facing supply bounds:
a supply-side audit datum is exactly a Case B context together with a witness
accounting datum and the canonical support-vs-`M` inequality.
-/
theorem hasSupplyBoundAudit_grammar
    {C : Context} (A : WitnessAccountingAudit C)
    (h : HasSupplyBoundAudit C A) :
    ∃ A' : WitnessAccountingAudit C,
      A' = A ∧ supportCard C.S ≤ MboundOfAccounting A' := by
  refine ⟨A, rfl, ?_⟩
  simpa using h

/--
A generic chain to lock yields an audit-facing supply bound on the initial
context once the induced accounting datum satisfies the saturated-support bound.
-/
theorem genericChain_supplyBoundAudit_sound
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    HasSupplyBoundAudit C (witnessAccountingOfGenericChainToSSLock G) := by
  exact supplyBound_of_genericChainToSSLock G hbound

/--
Expanded audit-facing inequality induced by a generic chain to lock.
-/
theorem genericChain_supplyBoundAudit_expanded
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    supportCard C.S ≤
      MboundOfAccounting (witnessAccountingOfGenericChainToSSLock G) := by
  exact supportCard_le_Mbound_of_genericChainToSSLock G hbound

/--
Audit-facing expansion of the accounting-specialized majorant induced by a
generic chain to lock.
-/
theorem genericChain_MboundAudit_eq
    {C : Context} (G : GenericChainToSSLock C) :
    MboundOfAccounting (witnessAccountingOfGenericChainToSSLock G) =
      witnessBudget (witnessAccountingOfGenericChainToSSLock G) + KmaxB C.y := by
  exact MboundOf_genericChainToSSLock_eq G

/--
A generic chain to lock yields an audit-facing supply package once the induced
accounting datum satisfies the saturated-support bound.
-/
theorem genericChain_supplyPackageAudit_sound
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    ∃ P : SupplyPackageAudit C,
      P.terminal = G.terminal ∧
      P.terminal.y = C.y ∧
      SSLock P.terminal := by
  refine ⟨supplyPackage_of_genericChainToSSLock G hbound, rfl, ?_, ?_⟩
  · simpa using GenericChain_preserves_level G.chain
  · simpa using G.hlock

/--
Every audit-facing supply package carries a witness accounting datum on the
initial context together with a supply bound for that same context.
-/
theorem supplyPackageAudit_sound
    {C : Context} (P : SupplyPackageAudit C) :
    HasSupplyBoundAudit C P.accounting := by
  exact P.hsupply

/--
Every audit-facing supply package is immediately terminally usable on the
supply side: it provides a terminal context, preserves the Case B level, carries
an `SSLock`, and supplies a witness-accounting-based support bound.
-/
theorem supplyPackageAudit_terminal_usable
    {C : Context} (P : SupplyPackageAudit C) :
    ∃ T : Context, ∃ A : WitnessAccountingAudit C,
      T = P.terminal ∧
      T.y = C.y ∧
      SSLock T ∧
      HasSupplyBoundAudit C A := by
  refine ⟨P.terminal, P.accounting, rfl, ?_, P.hlock, P.hsupply⟩
  simpa using P.hlevel

/--
Homogeneous grammar for audit-facing supply packages.
-/
theorem supplyPackageAudit_grammar
    {C : Context} (P : SupplyPackageAudit C) :
    ∃ T : Context, ∃ A : WitnessAccountingAudit C,
      T = P.terminal ∧
      T.y = C.y ∧
      SSLock T ∧
      HasSupplyBoundAudit C A := by
  exact supplyPackageAudit_terminal_usable P

end CaseB
end Lehmer