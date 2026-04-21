-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGatePassTraceAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic
open Classical

inductive CaseBGatePassExhaustiveTrace : Context → Type where
  | gatePass (C : Context) (G : AuditCaseBGatePassData C) :
      CaseBGatePassExhaustiveTrace C

namespace CaseBGatePassExhaustiveTrace

def start {C : Context} (_T : CaseBGatePassExhaustiveTrace C) : Context :=
  C

@[simp] theorem start_eq {C : Context} (_T : CaseBGatePassExhaustiveTrace C) :
    start _T = C := rfl

def terminal {C : Context} :
    CaseBGatePassExhaustiveTrace C → Context
  | gatePass C _ => C

def length {C : Context} :
    CaseBGatePassExhaustiveTrace C → ℕ
  | gatePass _ _ => 0

@[simp] theorem terminal_gatePass
    (C : Context) (G : AuditCaseBGatePassData C) :
    terminal (CaseBGatePassExhaustiveTrace.gatePass C G) = C := rfl

@[simp] theorem length_gatePass
    (C : Context) (G : AuditCaseBGatePassData C) :
    length (CaseBGatePassExhaustiveTrace.gatePass C G) = 0 := rfl

theorem preserves_level
    {C : Context} (T : CaseBGatePassExhaustiveTrace C) :
    (terminal T).y = C.y := by
  cases T <;> rfl

theorem terminal_contextDescentLength_le
    {C : Context} (T : CaseBGatePassExhaustiveTrace C) :
    contextDescentLength (terminal T) ≤ contextDescentLength C := by
  cases T <;> exact le_rfl

theorem finite
    {C : Context} (T : CaseBGatePassExhaustiveTrace C) :
    ∃ n : ℕ, length T = n := by
  exact ⟨length T, rfl⟩

end CaseBGatePassExhaustiveTrace

noncomputable def caseBGatePassExhaustiveTrace_of_state
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    CaseBGatePassExhaustiveTrace C := by
  classical
  let G : AuditCaseBGatePassData C :=
    Classical.choose (exists_gatePass_of_state C hC)
  exact CaseBGatePassExhaustiveTrace.gatePass C G

theorem exhaustiveTrace_is_gatePass
    {C : Context} (T : CaseBGatePassExhaustiveTrace C) :
    ∃ _ : AuditCaseBGatePassData C, True := by
  cases T with
  | gatePass G =>
      exact ⟨G, trivial⟩

theorem exists_exhaustiveTrace_of_gatePassState
    (C : Context)
    (hC : AuditCaseBGatePassState C) :
    ∃ _ : CaseBGatePassExhaustiveTrace C, True := by
  exact ⟨caseBGatePassExhaustiveTrace_of_state C hC, trivial⟩

end CaseB
end Lehmer