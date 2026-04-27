-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGateFailTraceAudit.lean
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
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
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
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Classical

inductive CaseBGateFailExhaustiveTrace : Context → Type where
  | gateFail (C : Context) (G : AuditCaseBGateFailData C) :
      CaseBGateFailExhaustiveTrace C

namespace CaseBGateFailExhaustiveTrace

def start {C : Context} (_T : CaseBGateFailExhaustiveTrace C) : Context :=
  C

@[simp] theorem start_eq {C : Context} (_T : CaseBGateFailExhaustiveTrace C) :
    start _T = C := rfl

def terminal {C : Context} :
    CaseBGateFailExhaustiveTrace C → Context
  | gateFail C _ => C

def length {C : Context} :
    CaseBGateFailExhaustiveTrace C → ℕ
  | gateFail _ _ => 0

@[simp] theorem terminal_gateFail
    (C : Context) (G : AuditCaseBGateFailData C) :
    terminal (CaseBGateFailExhaustiveTrace.gateFail C G) = C := rfl

@[simp] theorem length_gateFail
    (C : Context) (G : AuditCaseBGateFailData C) :
    length (CaseBGateFailExhaustiveTrace.gateFail C G) = 0 := rfl

theorem preserves_level
    {C : Context} (T : CaseBGateFailExhaustiveTrace C) :
    (terminal T).y = C.y := by
  cases T
  rfl

theorem terminal_contextDescentLength_le
    {C : Context} (T : CaseBGateFailExhaustiveTrace C) :
    contextDescentLength (terminal T) ≤ contextDescentLength C := by
  cases T
  exact le_rfl

theorem finite
    {C : Context} (T : CaseBGateFailExhaustiveTrace C) :
    ∃ n : ℕ, length T = n := by
  exact ⟨length T, rfl⟩

end CaseBGateFailExhaustiveTrace

noncomputable def caseBGateFailExhaustiveTrace_of_data
    (C : Context)
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailExhaustiveTrace C :=
  CaseBGateFailExhaustiveTrace.gateFail C G

noncomputable def caseBGateFailExhaustiveTrace_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailExhaustiveTrace C :=
  caseBGateFailExhaustiveTrace_of_data C
    (auditCaseBGateFailData_of_state C hC)

theorem exhaustiveTrace_is_gateFail
    {C : Context} (T : CaseBGateFailExhaustiveTrace C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases T with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem exists_exhaustiveTrace_of_gateFailState
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailExhaustiveTrace C, True := by
  exact ⟨caseBGateFailExhaustiveTrace_of_state C hC, trivial⟩

inductive CaseBGateFailTerminalTrace : Context → Type where
  | nil (C : Context) :
      CaseBGateFailTerminalTrace C

namespace CaseBGateFailTerminalTrace

def start {C : Context} (_T : CaseBGateFailTerminalTrace C) : Context :=
  C

@[simp] theorem start_eq {C : Context} (_T : CaseBGateFailTerminalTrace C) :
    start _T = C := rfl

def terminal {C : Context} :
    CaseBGateFailTerminalTrace C → Context
  | nil C => C

def length {C : Context} :
    CaseBGateFailTerminalTrace C → ℕ
  | nil _ => 0

@[simp] theorem terminal_nil (C : Context) :
    terminal (nil C) = C := rfl

@[simp] theorem length_nil (C : Context) :
    length (nil C) = 0 := rfl

theorem preserves_level
    {C : Context} (T : CaseBGateFailTerminalTrace C) :
    (terminal T).y = C.y := by
  cases T
  rfl

theorem terminal_contextDescentLength_le
    {C : Context} (T : CaseBGateFailTerminalTrace C) :
    contextDescentLength (terminal T) ≤ contextDescentLength C := by
  cases T
  exact le_rfl

theorem finite
    {C : Context} (T : CaseBGateFailTerminalTrace C) :
    ∃ n : ℕ, length T = n := by
  exact ⟨length T, rfl⟩

end CaseBGateFailTerminalTrace

def caseBGateFailTerminalTrace_of_state
    (C : Context)
    (_hC : AuditCaseBGateFailState C) :
    CaseBGateFailTerminalTrace C :=
  CaseBGateFailTerminalTrace.nil C

@[simp] theorem caseBGateFailTerminalTrace_of_state_terminal
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailTerminalTrace.terminal
      (caseBGateFailTerminalTrace_of_state C hC) = C := by
  rfl

@[simp] theorem caseBGateFailTerminalTrace_of_state_length
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailTerminalTrace.length
      (caseBGateFailTerminalTrace_of_state C hC) = 0 := by
  rfl

theorem caseBGateFailTerminalTrace_of_state_preserves_level
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    (CaseBGateFailTerminalTrace.terminal
      (caseBGateFailTerminalTrace_of_state C hC)).y = C.y := by
  rfl

theorem caseBGateFailTerminalTrace_of_state_finite
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ n : ℕ,
      CaseBGateFailTerminalTrace.length
        (caseBGateFailTerminalTrace_of_state C hC) = n := by
  exact ⟨0, rfl⟩

end CaseB
end Lehmer