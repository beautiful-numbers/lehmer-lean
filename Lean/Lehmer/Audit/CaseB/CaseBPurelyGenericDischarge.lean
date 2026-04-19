-- FILE: Lean/Lehmer/Audit/CaseB/CaseBPurelyGenericDischarge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.LocalCompleteness : def thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
- Lehmer.CaseB.Saturation.GenericChains : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.LocalCompleteness
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.GenericChains
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

theorem purelyGeneric_of_AuditCaseBPurelyGenericBranch
    {C : Context} (hpg : AuditCaseBPurelyGenericBranch C) :
    ContextPurelyGeneric C := by
  exact hpg

theorem auditCaseBPurelyGenericBranch_of_boundary_and_no_entangled
    {C : Context}
    (hB : AuditCaseBLocalBoundaryData C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    AuditCaseBPurelyGenericBranch C := by
  exact AuditCaseBPurelyGenericBranch.of_boundary hB hno

theorem auditCaseBPurelyGenericBranch_of_state_and_no_entangled
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    AuditCaseBPurelyGenericBranch C := by
  exact auditCaseBPurelyGenericBranch_of_boundary_and_no_entangled
    (AuditCaseBLocalBoundaryData_of_nonSaturatedState hC) hno

def AuditCaseBDischargeApplies (C : Context) : Prop :=
  ContextPurelyGeneric C

@[simp] theorem AuditCaseBDischargeApplies_def (C : Context) :
    AuditCaseBDischargeApplies C = ContextPurelyGeneric C := rfl

theorem auditCaseBDischargeApplies_of_purelyGeneric
    {C : Context} (hpg : AuditCaseBPurelyGenericBranch C) :
    AuditCaseBDischargeApplies C := by
  exact hpg

theorem auditCaseBDischargeApplies_of_boundary_and_no_entangled
    {C : Context}
    (hB : AuditCaseBLocalBoundaryData C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    AuditCaseBDischargeApplies C := by
  exact AuditCaseBPurelyGenericBranch.of_boundary hB hno

theorem auditCaseBDischargeApplies_of_state_and_no_entangled
    {C : Context}
    (hC : AuditCaseBNonSaturatedState C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    AuditCaseBDischargeApplies C := by
  exact auditCaseBPurelyGenericBranch_of_state_and_no_entangled hC hno

structure AuditCaseBDischargeData (C : Context) where
  hdis : AuditCaseBDischargeApplies C

def auditCaseBDischargeData_of_purelyGeneric
    {C : Context} (hpg : AuditCaseBPurelyGenericBranch C) :
    AuditCaseBDischargeData C :=
  { hdis := hpg }

def auditCaseBDischargeData_of_boundary_and_no_entangled
    (C : Context)
    (hB : AuditCaseBLocalBoundaryData C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    AuditCaseBDischargeData C :=
  { hdis := auditCaseBDischargeApplies_of_boundary_and_no_entangled hB hno }

def auditCaseBDischargeData_of_state_and_no_entangled
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    AuditCaseBDischargeData C :=
  { hdis := auditCaseBDischargeApplies_of_state_and_no_entangled hC hno }

theorem AuditCaseBDischargeData.applies
    {C : Context} (D : AuditCaseBDischargeData C) :
    AuditCaseBDischargeApplies C := by
  exact D.hdis

theorem exists_AuditCaseBDischargeData_of_purelyGeneric
    (C : Context)
    (hpg : AuditCaseBPurelyGenericBranch C) :
    ∃ D : AuditCaseBDischargeData C, True := by
  exact ⟨auditCaseBDischargeData_of_purelyGeneric hpg, trivial⟩

theorem exists_AuditCaseBDischargeData_of_boundary_and_no_entangled
    (C : Context)
    (hB : AuditCaseBLocalBoundaryData C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    ∃ D : AuditCaseBDischargeData C, True := by
  exact ⟨auditCaseBDischargeData_of_boundary_and_no_entangled C hB hno, trivial⟩

theorem exists_AuditCaseBDischargeData_of_state_and_no_entangled
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hno : ¬ ∃ p : ℕ, EntangledPrime C.S p C.y) :
    ∃ D : AuditCaseBDischargeData C, True := by
  exact ⟨auditCaseBDischargeData_of_state_and_no_entangled C hC hno, trivial⟩

end CaseB
end Lehmer