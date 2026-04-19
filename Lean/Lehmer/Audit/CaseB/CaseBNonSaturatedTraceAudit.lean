-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedTraceAudit.lean
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
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBPurelyGenericDischarge
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedExhaustiveTrace : Context → Type where
  | discharge (C : Context) (D : AuditCaseBDischargeData C) :
      CaseBNonSaturatedExhaustiveTrace C
  | entangled (C : Context) (E : AuditCaseBEntangledStepData C) :
      CaseBNonSaturatedExhaustiveTrace C

namespace CaseBNonSaturatedExhaustiveTrace

def start {C : Context} (_T : CaseBNonSaturatedExhaustiveTrace C) : Context :=
  C

@[simp] theorem start_eq {C : Context} (T : CaseBNonSaturatedExhaustiveTrace C) :
    T.start = C := rfl

def terminal {C : Context} :
    CaseBNonSaturatedExhaustiveTrace C → Context
  | discharge C _ => C
  | entangled C _ => C

def length {C : Context} :
    CaseBNonSaturatedExhaustiveTrace C → ℕ
  | discharge _ _ => 0
  | entangled _ _ => 0

@[simp] theorem terminal_discharge
    (C : Context) (D : AuditCaseBDischargeData C) :
    terminal (CaseBNonSaturatedExhaustiveTrace.discharge C D) = C := rfl

@[simp] theorem terminal_entangled
    (C : Context) (E : AuditCaseBEntangledStepData C) :
    terminal (CaseBNonSaturatedExhaustiveTrace.entangled C E) = C := rfl

@[simp] theorem length_discharge
    (C : Context) (D : AuditCaseBDischargeData C) :
    length (CaseBNonSaturatedExhaustiveTrace.discharge C D) = 0 := rfl

@[simp] theorem length_entangled
    (C : Context) (E : AuditCaseBEntangledStepData C) :
    length (CaseBNonSaturatedExhaustiveTrace.entangled C E) = 0 := rfl

theorem preserves_level
    {C : Context} (T : CaseBNonSaturatedExhaustiveTrace C) :
    (terminal T).y = C.y := by
  cases T <;> rfl

theorem terminal_contextDescentLength_le
    {C : Context} (T : CaseBNonSaturatedExhaustiveTrace C) :
    contextDescentLength (terminal T) ≤ contextDescentLength C := by
  cases T <;> exact le_rfl

theorem finite
    {C : Context} (T : CaseBNonSaturatedExhaustiveTrace C) :
    ∃ n : ℕ, length T = n := by
  exact ⟨length T, rfl⟩

end CaseBNonSaturatedExhaustiveTrace

noncomputable def caseBNonSaturatedExhaustiveTrace_of_outcome
    (C : Context)
    (hO : AuditCaseBExhaustiveLocalOutcome C) :
    CaseBNonSaturatedExhaustiveTrace C := by
  classical
  rcases hO with hD | hE
  · rcases hD with ⟨D, _⟩
    exact CaseBNonSaturatedExhaustiveTrace.discharge C D
  · rcases hE with ⟨E, _⟩
    exact CaseBNonSaturatedExhaustiveTrace.entangled C E

noncomputable def caseBNonSaturatedExhaustiveTrace_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedExhaustiveTrace C :=
  caseBNonSaturatedExhaustiveTrace_of_outcome C
    (AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC)

theorem exhaustiveTrace_is_discharge_or_entangled
    {C : Context} (T : CaseBNonSaturatedExhaustiveTrace C) :
    (∃ D : AuditCaseBDischargeData C, True) ∨
    (∃ E : AuditCaseBEntangledStepData C, True) := by
  cases T with
  | discharge C D =>
      exact Or.inl ⟨D, trivial⟩
  | entangled C E =>
      exact Or.inr ⟨E, trivial⟩

theorem exists_exhaustiveTrace_of_nonSaturatedState
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ T : CaseBNonSaturatedExhaustiveTrace C, True := by
  exact ⟨caseBNonSaturatedExhaustiveTrace_of_state C hC, trivial⟩

inductive CaseBNonSaturatedBackboneTrace : Context → Type where
  | nil (C : Context) :
      CaseBNonSaturatedBackboneTrace C
  | cons {C : Context}
      (B : AuditCaseBNonSaturatedBranch C)
      (T : CaseBNonSaturatedBackboneTrace B.backbone.C') :
      CaseBNonSaturatedBackboneTrace C

namespace CaseBNonSaturatedBackboneTrace

def start {C : Context} (_T : CaseBNonSaturatedBackboneTrace C) : Context :=
  C

@[simp] theorem start_eq {C : Context} (T : CaseBNonSaturatedBackboneTrace C) :
    T.start = C := rfl

def terminal {C : Context} :
    CaseBNonSaturatedBackboneTrace C → Context
  | nil C => C
  | cons _ T => terminal T

def length {C : Context} :
    CaseBNonSaturatedBackboneTrace C → ℕ
  | nil _ => 0
  | cons _ T => Nat.succ (length T)

@[simp] theorem terminal_nil (C : Context) :
    terminal (nil C) = C := rfl

@[simp] theorem terminal_cons
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (T : CaseBNonSaturatedBackboneTrace B.backbone.C') :
    terminal (cons B T) = terminal T := rfl

@[simp] theorem length_nil (C : Context) :
    length (nil C) = 0 := rfl

@[simp] theorem length_cons
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (T : CaseBNonSaturatedBackboneTrace B.backbone.C') :
    length (cons B T) = Nat.succ (length T) := rfl

theorem preserves_level
    {C : Context} (T : CaseBNonSaturatedBackboneTrace C) :
    (terminal T).y = C.y := by
  induction T with
  | nil C =>
      rfl
  | cons B T ih =>
      calc
        (terminal T).y = B.backbone.C'.y := ih
        _ = C.y := B.preserves_level

theorem terminal_contextDescentLength_le
    {C : Context} (T : CaseBNonSaturatedBackboneTrace C) :
    contextDescentLength (terminal T) ≤ contextDescentLength C := by
  induction T with
  | nil C =>
      exact le_rfl
  | cons B T ih =>
      exact le_trans ih (Nat.le_of_lt B.length_decrease)

theorem measure_decreases_cons
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (T : CaseBNonSaturatedBackboneTrace B.backbone.C') :
    contextDescentLength (terminal (cons B T)) < contextDescentLength C := by
  change contextDescentLength (terminal T) < contextDescentLength C
  exact lt_of_le_of_lt (terminal_contextDescentLength_le T) B.length_decrease

theorem wellFounded_by_contextDescentLength :
    WellFounded (fun C' C => contextDescentLength C' < contextDescentLength C) := by
  exact measure_wf contextDescentLength

theorem finite
    {C : Context} (T : CaseBNonSaturatedBackboneTrace C) :
    ∃ n : ℕ, length T = n := by
  exact ⟨length T, rfl⟩

end CaseBNonSaturatedBackboneTrace

def caseBNonSaturatedBackboneTrace_of_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    CaseBNonSaturatedBackboneTrace C :=
  CaseBNonSaturatedBackboneTrace.cons B
    (CaseBNonSaturatedBackboneTrace.nil B.backbone.C')

noncomputable def caseBNonSaturatedBackboneTrace_of_gainProgressData
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    CaseBNonSaturatedBackboneTrace C :=
  caseBNonSaturatedBackboneTrace_of_branch
    (auditCaseBNonSaturatedBranch_of_gainProgressData C hP)

noncomputable def caseBNonSaturatedBackboneTrace_of_state_and_gainProgress
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hP : AuditCaseBGainProgressData C) :
    CaseBNonSaturatedBackboneTrace C :=
  caseBNonSaturatedBackboneTrace_of_branch
    (auditCaseBNonSaturatedBranch_of_state_and_gainProgress C hC hP)

@[simp] theorem caseBNonSaturatedBackboneTrace_of_branch_terminal
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    CaseBNonSaturatedBackboneTrace.terminal
      (caseBNonSaturatedBackboneTrace_of_branch B) =
        B.backbone.C' := by
  rfl

@[simp] theorem caseBNonSaturatedBackboneTrace_of_branch_length
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    CaseBNonSaturatedBackboneTrace.length
      (caseBNonSaturatedBackboneTrace_of_branch B) = 1 := by
  rfl

theorem caseBNonSaturatedBackboneTrace_of_branch_measure_decreases
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    contextDescentLength
      (CaseBNonSaturatedBackboneTrace.terminal
        (caseBNonSaturatedBackboneTrace_of_branch B)) <
      contextDescentLength C := by
  simpa [caseBNonSaturatedBackboneTrace_of_branch] using
    CaseBNonSaturatedBackboneTrace.measure_decreases_cons
      B (CaseBNonSaturatedBackboneTrace.nil B.backbone.C')

theorem contextDescentLength_decreases_of_caseBNonSaturatedBackboneTrace_of_gainProgressData
    (C : Context)
    (hP : AuditCaseBGainProgressData C) :
    contextDescentLength
      (CaseBNonSaturatedBackboneTrace.terminal
        (caseBNonSaturatedBackboneTrace_of_gainProgressData C hP)) <
      contextDescentLength C := by
  exact caseBNonSaturatedBackboneTrace_of_branch_measure_decreases
    (auditCaseBNonSaturatedBranch_of_gainProgressData C hP)

theorem contextDescentLength_decreases_of_caseBNonSaturatedBackboneTrace_of_state_and_gainProgress
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C)
    (hP : AuditCaseBGainProgressData C) :
    contextDescentLength
      (CaseBNonSaturatedBackboneTrace.terminal
        (caseBNonSaturatedBackboneTrace_of_state_and_gainProgress C hC hP)) <
      contextDescentLength C := by
  exact caseBNonSaturatedBackboneTrace_of_branch_measure_decreases
    (auditCaseBNonSaturatedBranch_of_state_and_gainProgress C hC hP)

theorem caseBNonSaturatedBackboneTrace_of_branch_finite
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    ∃ n : ℕ,
      CaseBNonSaturatedBackboneTrace.length
        (caseBNonSaturatedBackboneTrace_of_branch B) = n := by
  exact ⟨1, rfl⟩

theorem caseBNonSaturatedBackboneTrace_of_branch_preserves_level
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C) :
    (CaseBNonSaturatedBackboneTrace.terminal
      (caseBNonSaturatedBackboneTrace_of_branch B)).y = C.y := by
  simpa [caseBNonSaturatedBackboneTrace_of_branch] using
    CaseBNonSaturatedBackboneTrace.preserves_level
      (caseBNonSaturatedBackboneTrace_of_branch B)

end CaseB
end Lehmer