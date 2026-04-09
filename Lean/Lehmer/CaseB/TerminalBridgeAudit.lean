-- FILE: Lean/Lehmer/CaseB/TerminalBridgeAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.CaseBClass : def
- Lehmer.CaseB.Saturation.WitnessAccountingAudit : def thm
- Lehmer.CaseB.Saturation.SupplyBoundAudit : def thm
- Lehmer.CaseB.TerminalBridge : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.CaseBClass
import Lehmer.CaseB.Saturation.WitnessAccountingAudit
import Lehmer.CaseB.Saturation.SupplyBoundAudit
import Lehmer.CaseB.TerminalBridge

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Audit-facing alias for the minimal terminal structural data exported by the
principal Case B pipeline.
-/
abbrev CaseBTerminalDataAudit (n : ℕ) : Prop :=
  CaseBTerminalData n

@[simp] theorem CaseBTerminalDataAudit_def (n : ℕ) :
    CaseBTerminalDataAudit n = CaseBTerminalData n := rfl

/--
Audit-facing expansion of the minimal Case B terminal data.

A valid terminalization for a candidate `n` consists exactly of:
- a witness accounting datum on the canonical candidate context,
- a supply-side terminal bound on that same context,
- a closed witness-side bound.
-/
theorem caseBTerminalDataAudit_expand (n : ℕ) :
    CaseBTerminalDataAudit n ↔
      ∃ A : WitnessAccountingAudit (candidateContext n),
        HasSupplyBoundAudit (candidateContext n) A ∧
        ClosedWitnessBound A := by
  rfl

/--
Witness-side support soundness extracted from terminal data:
every terminal witness stays inside the support of the canonical candidate
context.
-/
theorem caseBTerminalDataAudit_witness_support_sound
    {n : ℕ}
    (_hT : CaseBTerminalDataAudit n)
    {p : ℕ}
    (hp : ∃ A : WitnessAccountingAudit (candidateContext n),
      p ∈ witnessSetAudit (candidateContext n) A ∧
      HasSupplyBoundAudit (candidateContext n) A ∧
      ClosedWitnessBound A) :
    p ∈ (candidateContext n).S := by
  rcases hp with ⟨A, hpA, _hSupply, _hClosed⟩
  exact witnessSetAudit_support_sound A hpA

/--
Witness-side cardinal soundness extracted from terminal data:
the witness-set cardinality is bounded by the support cardinality of the
canonical candidate context.
-/
theorem caseBTerminalDataAudit_witness_card_le_supportCard
    {n : ℕ}
    (hT : CaseBTerminalDataAudit n) :
    ∃ A : WitnessAccountingAudit (candidateContext n),
      supportCard (witnessSetAudit (candidateContext n) A) ≤
        supportCard (candidateContext n).S ∧
      HasSupplyBoundAudit (candidateContext n) A ∧
      ClosedWitnessBound A := by
  rcases hT with ⟨A, hSupply, hClosed⟩
  refine ⟨A, ?_, hSupply, hClosed⟩
  exact witnessAccountingAudit_card_le_supportCard A

/--
Witness-side classification soundness extracted from terminal data:
every recorded witness is support-compatible and classified either as generic or
as entangled.
-/
theorem caseBTerminalDataAudit_witness_classified
    {n : ℕ}
    (_hT : CaseBTerminalDataAudit n)
    {p : ℕ}
    (hp :
      ∃ A : WitnessAccountingAudit (candidateContext n),
        p ∈ witnessSetAudit (candidateContext n) A ∧
        HasSupplyBoundAudit (candidateContext n) A ∧
        ClosedWitnessBound A) :
    WitnessCompatible (candidateContext n) p ∧
      (GenericWitness (candidateContext n) p ∨
        EntangledWitness (candidateContext n) p) := by
  rcases hp with ⟨A, hpA, _hSupply, _hClosed⟩
  exact witnessAccountingAudit_classified A hpA

/--
Supply-side soundness extracted from terminal data:
the terminal supply bound is attached to the canonical candidate context.
-/
theorem caseBTerminalDataAudit_supply_sound
    {n : ℕ}
    (hT : CaseBTerminalDataAudit n) :
    ∃ A : WitnessAccountingAudit (candidateContext n),
      HasSupplyBoundAudit (candidateContext n) A ∧
      ClosedWitnessBound A := by
  simpa using hT

/--
Expanded supply-side terminal usability extracted from terminal data.
-/
theorem caseBTerminalDataAudit_supply_terminal_usable
    {n : ℕ}
    (hT : CaseBTerminalDataAudit n) :
    ∃ A : WitnessAccountingAudit (candidateContext n),
      supportCard (candidateContext n).S ≤ MboundOfAccounting A ∧
      ClosedWitnessBound A := by
  rcases hT with ⟨A, hSupply, hClosed⟩
  refine ⟨A, ?_, hClosed⟩
  exact hasSupplyBoundAudit_terminal_usable (candidateContext n) A hSupply

/--
Homogeneous grammar of Case B terminal data, audit-facing form.

A terminal datum for a candidate `n` is exactly:
- the canonical candidate context `candidateContext n`,
- a witness accounting datum on that context,
- a supply-side audit bound on that context,
- a closed witness-side bound.
-/
theorem caseBTerminalDataAudit_grammar
    (n : ℕ) :
    CaseBTerminalDataAudit n ↔
      ∃ A : WitnessAccountingAudit (candidateContext n),
        witnessSetAudit (candidateContext n) A = witnessSet (candidateContext n) A ∧
        HasSupplyBoundAudit (candidateContext n) A ∧
        ClosedWitnessBound A := by
  constructor
  · intro hT
    rcases hT with ⟨A, hSupply, hClosed⟩
    refine ⟨A, rfl, hSupply, hClosed⟩
  · intro h
    rcases h with ⟨A, _, hSupply, hClosed⟩
    exact ⟨A, hSupply, hClosed⟩

end CaseB
end Lehmer