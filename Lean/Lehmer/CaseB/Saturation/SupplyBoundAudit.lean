-- FILE: Lean/Lehmer/CaseB/Saturation/SupplyBoundAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.WitnessAccountingAudit : def thm
- Lehmer.CaseB.Saturation.EntanglementScarcity : def thm
- Lehmer.CaseB.Saturation.SaturatedSupportBound : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.WitnessAccountingAudit
import Lehmer.CaseB.Saturation.EntanglementScarcity
import Lehmer.CaseB.Saturation.SaturatedSupportBound
import Lehmer.CaseB.Saturation.SupplyBound

namespace Lehmer
namespace CaseB

open Lehmer.Basic

abbrev HasSupplyBoundAudit (C : Context) (A : WitnessAccounting C) : Prop :=
  HasSupplyBound C A

@[simp] theorem HasSupplyBoundAudit_def (C : Context) (A : WitnessAccounting C) :
    HasSupplyBoundAudit C A = HasSupplyBound C A := rfl

@[simp] theorem entangledWitnessSet_empty
    (C : Context) :
    entangledWitnessSet (emptyWitnessAccounting C) = ∅ := by
  ext p
  rw [entangledWitnessSet_def]
  simp [witnessSet_def, emptyWitnessAccounting, emptyWitnessPack]

@[simp] theorem witnessBudget_empty
    (C : Context) :
    witnessBudget (emptyWitnessAccounting C) = 0 := by
  rw [witnessBudget_def]
  rw [entangledWitnessSet_empty]
  simp [supportCard]

@[simp] theorem saturatedSupportBoundOfAccounting_empty
    (C : Context) :
    saturatedSupportBoundOfAccounting (emptyWitnessAccounting C) = KmaxB C.y := by
  rw [saturatedSupportBoundOfAccounting_eq]
  rw [entangledWitnessSet_empty]
  simp [supportCard]

@[simp] theorem MboundOfAccounting_empty
    (C : Context) :
    MboundOfAccounting (emptyWitnessAccounting C) = KmaxB C.y := by
  rw [MboundOfAccounting_eq]
  rw [witnessBudget_empty]
  simp

theorem hasSupplyBound_empty
    (C : Context)
    (hK : supportCard C.S ≤ KmaxB C.y) :
    HasSupplyBound C (emptyWitnessAccounting C) := by
  rw [HasSupplyBound_def]
  rw [MboundOfAccounting_empty]
  exact hK

theorem exists_empty_accounting_with_supplyBound
    (C : Context)
    (hK : supportCard C.S ≤ KmaxB C.y) :
    ∃ A : WitnessAccounting C, HasSupplyBound C A := by
  refine ⟨emptyWitnessAccounting C, ?_⟩
  exact hasSupplyBound_empty C hK

theorem hasSupplyBoundAudit_terminal_usable
    (C : Context)
    (A : WitnessAccounting C)
    (h : HasSupplyBoundAudit C A) :
    supportCard C.S ≤ MboundOfAccounting A := by
  exact h

end CaseB
end Lehmer