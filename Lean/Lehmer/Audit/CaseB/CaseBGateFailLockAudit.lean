-- FILE: Lean/Lehmer/Audit/CaseB/CaseBGateFailLockAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.GenericChains : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.GenericChains
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBGateFailTraceAudit
import Lehmer.Audit.CaseB.CaseBGateFailClassificationAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBGateFailLockTag (C : Context) : Type where
  | gateFail (G : AuditCaseBGateFailData C)

structure CaseBGateFailLockRouting (C : Context) where
  trace : CaseBGateFailExhaustiveTrace C
  classification : CaseBGateFailExhaustiveTraceClassification C
  tag : CaseBGateFailLockTag C

def caseBGateFailLockRouting_of_gateFail
    {C : Context}
    (G : AuditCaseBGateFailData C) :
    CaseBGateFailLockRouting C :=
  { trace := CaseBGateFailExhaustiveTrace.gateFail C G
    classification := caseBGateFailExhaustiveTraceClassification_of_data G
    tag := CaseBGateFailLockTag.gateFail G }

noncomputable def caseBGateFailLockRouting_of_classification
    (C : Context)
    (K : CaseBGateFailExhaustiveTraceClassification C) :
    CaseBGateFailLockRouting C := by
  cases K with
  | gateFail G =>
      exact caseBGateFailLockRouting_of_gateFail G

noncomputable def caseBGateFailLockRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailLockRouting C :=
  caseBGateFailLockRouting_of_gateFail
    (auditCaseBGateFailData_of_state C hC)

theorem CaseBGateFailLockRouting.is_gateFail
    {C : Context}
    (R : CaseBGateFailLockRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R.tag with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem caseBGateFailLockRouting_sound
    {C : Context}
    (R : CaseBGateFailLockRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  cases R.tag with
  | gateFail G =>
      exact ⟨G, trivial⟩

theorem CaseBGateFailLockRouting.trace_preserves_level
    {C : Context} (R : CaseBGateFailLockRouting C) :
    (CaseBGateFailExhaustiveTrace.terminal R.trace).y = C.y := by
  exact CaseBGateFailExhaustiveTrace.preserves_level R.trace

theorem CaseBGateFailLockRouting.trace_length_eq_zero
    {C : Context} (R : CaseBGateFailLockRouting C) :
    CaseBGateFailExhaustiveTrace.length R.trace = 0 := by
  cases R.trace
  rfl

theorem CaseBGateFailLockRouting.trace_terminal_eq_start
    {C : Context} (R : CaseBGateFailLockRouting C) :
    CaseBGateFailExhaustiveTrace.terminal R.trace = C := by
  cases R.trace
  rfl

theorem CaseBGateFailLockRouting.trace_terminal_contextDescentLength_le
    {C : Context} (R : CaseBGateFailLockRouting C) :
    contextDescentLength (CaseBGateFailExhaustiveTrace.terminal R.trace) ≤
      contextDescentLength C := by
  exact CaseBGateFailExhaustiveTrace.terminal_contextDescentLength_le R.trace

theorem CaseBGateFailLockRouting.classification_sound
    {C : Context} (R : CaseBGateFailLockRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailExhaustiveTraceClassification_sound R.classification

theorem CaseBGateFailLockRouting.trace_is_exhaustive
    {C : Context} (R : CaseBGateFailLockRouting C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact exhaustiveTrace_is_gateFail R.trace

theorem exists_caseBGateFailLockRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailLockRouting C, True := by
  exact ⟨caseBGateFailLockRouting_of_state C hC, trivial⟩

theorem exists_gateFail_lockRouting_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : AuditCaseBGateFailData C, True := by
  exact caseBGateFailLockRouting_sound
    (caseBGateFailLockRouting_of_state C hC)

structure CaseBGateFailLockAssembly (C : Context) where
  classification : CaseBGateFailExhaustiveTraceClassification C
  trace : CaseBGateFailTerminalTrace C
  htrace : trace = caseBGateFailTerminalTrace_of_state C classification.is_gateFail.choose.state
  terminal : Context
  hterminal : terminal = CaseBGateFailTerminalTrace.terminal trace
  hlock : SSLock terminal

noncomputable def caseBGateFailLockAssembly_of_state
    {C : Context}
    (hC : AuditCaseBGateFailState C) :
    CaseBGateFailLockAssembly C :=
  { classification := caseBGateFailExhaustiveTraceClassification_of_state C hC
    trace := caseBGateFailTerminalTrace_of_state C hC
    htrace := rfl
    terminal := C
    hterminal := rfl
    hlock := hC.1 }

theorem CaseBGateFailLockAssembly.terminal_eq_trace_terminal
    {C : Context} (A : CaseBGateFailLockAssembly C) :
    A.terminal = CaseBGateFailTerminalTrace.terminal A.trace := by
  exact A.hterminal

theorem CaseBGateFailLockAssembly.terminal_locked
    {C : Context} (A : CaseBGateFailLockAssembly C) :
    SSLock A.terminal := by
  exact A.hlock

theorem CaseBGateFailLockAssembly.trace_preserves_level
    {C : Context} (A : CaseBGateFailLockAssembly C) :
    (CaseBGateFailTerminalTrace.terminal A.trace).y = C.y := by
  exact CaseBGateFailTerminalTrace.preserves_level A.trace

theorem CaseBGateFailLockAssembly.trace_length_eq_zero
    {C : Context} (A : CaseBGateFailLockAssembly C) :
    CaseBGateFailTerminalTrace.length A.trace = 0 := by
  cases A.trace
  rfl

theorem exists_caseBGateFailLockAssembly_of_state
    (C : Context)
    (hC : AuditCaseBGateFailState C) :
    ∃ _ : CaseBGateFailLockAssembly C, True := by
  exact ⟨caseBGateFailLockAssembly_of_state hC, trivial⟩

end CaseB
end Lehmer