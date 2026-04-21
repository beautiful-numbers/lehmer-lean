-- FILE: Lean/Lehmer/Audit/CaseB/CaseBNonSaturatedLockAudit.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Saturation.GenericChains : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit : def thm
- Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Saturation.GenericChains
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.Audit.CaseB.CaseBNonSaturatedProgressAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedTraceAudit
import Lehmer.Audit.CaseB.CaseBNonSaturatedClassificationAudit

namespace Lehmer
namespace CaseB

open Lehmer.Basic

inductive CaseBNonSaturatedLockTag (C : Context) : Type where
  | discharge (D : AuditCaseBDischargeData C)
  | entangled (E : AuditCaseBEntangledStepData C)

structure CaseBNonSaturatedLockRouting (C : Context) where
  trace : CaseBNonSaturatedExhaustiveTrace C
  classification : CaseBNonSaturatedExhaustiveTraceClassification C
  tag : CaseBNonSaturatedLockTag C

def caseBNonSaturatedLockRouting_of_discharge
    {C : Context}
    (D : AuditCaseBDischargeData C) :
    CaseBNonSaturatedLockRouting C :=
  { trace := CaseBNonSaturatedExhaustiveTrace.discharge C D
    classification := caseBNonSaturatedExhaustiveTraceClassification_of_discharge D
    tag := CaseBNonSaturatedLockTag.discharge D }

def caseBNonSaturatedLockRouting_of_entangled
    {C : Context}
    (E : AuditCaseBEntangledStepData C) :
    CaseBNonSaturatedLockRouting C :=
  { trace := CaseBNonSaturatedExhaustiveTrace.entangled C E
    classification := caseBNonSaturatedExhaustiveTraceClassification_of_entangled E
    tag := CaseBNonSaturatedLockTag.entangled E }

noncomputable def caseBNonSaturatedLockRouting_of_classification
    (C : Context)
    (K : CaseBNonSaturatedExhaustiveTraceClassification C) :
    CaseBNonSaturatedLockRouting C := by
  cases K.tag with
  | discharge D =>
      exact caseBNonSaturatedLockRouting_of_discharge D
  | entangled E =>
      exact caseBNonSaturatedLockRouting_of_entangled E

noncomputable def caseBNonSaturatedLockRouting_of_outcome
    (C : Context)
    (hO : AuditCaseBExhaustiveLocalOutcome C) :
    CaseBNonSaturatedLockRouting C :=
  caseBNonSaturatedLockRouting_of_classification C
    (caseBNonSaturatedExhaustiveTraceClassification_of_outcome C hO)

noncomputable def caseBNonSaturatedLockRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    CaseBNonSaturatedLockRouting C :=
  caseBNonSaturatedLockRouting_of_outcome C
    (AuditCaseBExhaustiveLocalOutcome_of_nonSaturatedState hC)

theorem CaseBNonSaturatedLockRouting.is_discharge
    {C : Context}
    (R : CaseBNonSaturatedLockRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBEntangledStepData C, True) :
    ∃ _ : AuditCaseBDischargeData C, True := by
  cases R.tag with
  | discharge D =>
      exact ⟨D, trivial⟩
  | entangled E =>
      exact False.elim (hnot ⟨E, trivial⟩)

theorem CaseBNonSaturatedLockRouting.is_entangled
    {C : Context}
    (R : CaseBNonSaturatedLockRouting C)
    (hnot : ¬ ∃ _ : AuditCaseBDischargeData C, True) :
    ∃ _ : AuditCaseBEntangledStepData C, True := by
  cases R.tag with
  | discharge D =>
      exact False.elim (hnot ⟨D, trivial⟩)
  | entangled E =>
      exact ⟨E, trivial⟩

theorem caseBNonSaturatedLockRouting_sound
    {C : Context}
    (R : CaseBNonSaturatedLockRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  cases R.tag with
  | discharge D =>
      exact Or.inl ⟨D, trivial⟩
  | entangled E =>
      exact Or.inr ⟨E, trivial⟩

theorem CaseBNonSaturatedLockRouting.trace_preserves_level
    {C : Context} (R : CaseBNonSaturatedLockRouting C) :
    (CaseBNonSaturatedExhaustiveTrace.terminal R.trace).y = C.y := by
  exact CaseBNonSaturatedExhaustiveTrace.preserves_level R.trace

theorem CaseBNonSaturatedLockRouting.trace_length_eq_zero
    {C : Context} (R : CaseBNonSaturatedLockRouting C) :
    CaseBNonSaturatedExhaustiveTrace.length R.trace = 0 := by
  cases R.trace <;> rfl

theorem CaseBNonSaturatedLockRouting.trace_terminal_eq_start
    {C : Context} (R : CaseBNonSaturatedLockRouting C) :
    CaseBNonSaturatedExhaustiveTrace.terminal R.trace = C := by
  cases R.trace <;> rfl

theorem CaseBNonSaturatedLockRouting.trace_terminal_contextDescentLength_le
    {C : Context} (R : CaseBNonSaturatedLockRouting C) :
    contextDescentLength (CaseBNonSaturatedExhaustiveTrace.terminal R.trace) ≤
      contextDescentLength C := by
  exact CaseBNonSaturatedExhaustiveTrace.terminal_contextDescentLength_le R.trace

theorem CaseBNonSaturatedLockRouting.classification_sound
    {C : Context} (R : CaseBNonSaturatedLockRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedExhaustiveTraceClassification_sound R.classification

theorem CaseBNonSaturatedLockRouting.trace_is_exhaustive
    {C : Context} (R : CaseBNonSaturatedLockRouting C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact exhaustiveTrace_is_discharge_or_entangled R.trace

theorem exists_caseBNonSaturatedLockRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    ∃ _ : CaseBNonSaturatedLockRouting C, True := by
  exact ⟨caseBNonSaturatedLockRouting_of_state C hC, trivial⟩

theorem exists_discharge_or_entangled_lockRouting_of_state
    (C : Context)
    (hC : AuditCaseBNonSaturatedState C) :
    (∃ _ : AuditCaseBDischargeData C, True) ∨
    (∃ _ : AuditCaseBEntangledStepData C, True) := by
  exact caseBNonSaturatedLockRouting_sound
    (caseBNonSaturatedLockRouting_of_state C hC)

structure CaseBNonSaturatedLockAssembly (C : Context) where
  branch : AuditCaseBNonSaturatedBranch C
  trace : CaseBNonSaturatedBackboneTrace C
  htrace : trace = caseBNonSaturatedBackboneTrace_of_branch branch
  classification : CaseBNonSaturatedCanonicalTraceClassification C
  hclassification :
    classification =
      caseBNonSaturatedCanonicalTraceClassification_of_branch branch
  terminal : Context
  chain : GenericChain C terminal
  hterminal : terminal = CaseBNonSaturatedBackboneTrace.terminal trace
  hlock : SSLock terminal
  hbudget : GenericChainWithinBudget chain

def caseBNonSaturatedLockAssembly_of_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    CaseBNonSaturatedLockAssembly C :=
  { branch := B
    trace := caseBNonSaturatedBackboneTrace_of_branch B
    htrace := rfl
    classification := caseBNonSaturatedCanonicalTraceClassification_of_branch B
    hclassification := rfl
    terminal := terminal
    chain := chain
    hterminal := hterminal
    hlock := hlock
    hbudget := hbudget }

@[simp] theorem caseBNonSaturatedLockAssembly_of_branch_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    (caseBNonSaturatedLockAssembly_of_branch
      B terminal chain hterminal hlock hbudget).branch = B := rfl

@[simp] theorem caseBNonSaturatedLockAssembly_of_branch_trace
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    (caseBNonSaturatedLockAssembly_of_branch
      B terminal chain hterminal hlock hbudget).trace =
        caseBNonSaturatedBackboneTrace_of_branch B := rfl

@[simp] theorem caseBNonSaturatedLockAssembly_of_branch_classification
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    (caseBNonSaturatedLockAssembly_of_branch
      B terminal chain hterminal hlock hbudget).classification =
        caseBNonSaturatedCanonicalTraceClassification_of_branch B := rfl

theorem CaseBNonSaturatedLockAssembly.trace_eq_canonical
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    A.trace = caseBNonSaturatedBackboneTrace_of_branch A.branch := by
  exact A.htrace

theorem CaseBNonSaturatedLockAssembly.classification_eq_canonical
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    A.classification =
      caseBNonSaturatedCanonicalTraceClassification_of_branch A.branch := by
  exact A.hclassification

theorem CaseBNonSaturatedLockAssembly.terminal_eq_trace_terminal
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    A.terminal = CaseBNonSaturatedBackboneTrace.terminal A.trace := by
  exact A.hterminal

theorem CaseBNonSaturatedLockAssembly.hasClassification
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    ContextGainCriterion C A.branch.backbone.p := by
  simpa [A.hclassification] using A.classification.hclassified

theorem CaseBNonSaturatedLockAssembly.terminal_locked
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    SSLock A.terminal := by
  exact A.hlock

theorem CaseBNonSaturatedLockAssembly.withinBudget
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    GenericChainWithinBudget A.chain := by
  exact A.hbudget

theorem CaseBNonSaturatedLockAssembly.trace_preserves_level
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    (CaseBNonSaturatedBackboneTrace.terminal A.trace).y = C.y := by
  rw [A.htrace]
  exact caseBNonSaturatedBackboneTrace_of_branch_preserves_level A.branch

theorem CaseBNonSaturatedLockAssembly.trace_length_eq_one
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    CaseBNonSaturatedBackboneTrace.length A.trace = 1 := by
  rw [A.htrace]
  exact caseBNonSaturatedBackboneTrace_of_branch_length A.branch

theorem CaseBNonSaturatedLockAssembly.trace_length_decrease
    {C : Context} (A : CaseBNonSaturatedLockAssembly C) :
    contextDescentLength
      (CaseBNonSaturatedBackboneTrace.terminal A.trace) <
        contextDescentLength C := by
  rw [A.htrace]
  exact caseBNonSaturatedBackboneTrace_of_branch_measure_decreases A.branch

def genericChainToSSLock_of_auditLockAssembly
    {C : Context}
    (A : CaseBNonSaturatedLockAssembly C) :
    GenericChainToSSLock C :=
  { terminal := A.terminal
    chain := A.chain
    hbudget := A.hbudget
    hlock := A.hlock }

def genericChainToSSLock_of_auditCaseBNonSaturatedBranch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    GenericChainToSSLock C :=
  genericChainToSSLock_of_auditLockAssembly
    (caseBNonSaturatedLockAssembly_of_branch
      B terminal chain hterminal hlock hbudget)

@[simp] theorem genericChainToSSLock_of_auditLockAssembly_terminal
    {C : Context}
    (A : CaseBNonSaturatedLockAssembly C) :
    (genericChainToSSLock_of_auditLockAssembly A).terminal = A.terminal := rfl

@[simp] theorem genericChainToSSLock_of_auditLockAssembly_chain
    {C : Context}
    (A : CaseBNonSaturatedLockAssembly C) :
    (genericChainToSSLock_of_auditLockAssembly A).chain = A.chain := rfl

@[simp] theorem genericChainToSSLock_of_auditLockAssembly_lock
    {C : Context}
    (A : CaseBNonSaturatedLockAssembly C) :
    (genericChainToSSLock_of_auditLockAssembly A).hlock = A.hlock := rfl

@[simp] theorem genericChainToSSLock_of_auditLockAssembly_budget
    {C : Context}
    (A : CaseBNonSaturatedLockAssembly C) :
    (genericChainToSSLock_of_auditLockAssembly A).hbudget = A.hbudget := rfl

theorem genericChainToSSLock_of_auditCaseBNonSaturatedBranch_terminal
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    (genericChainToSSLock_of_auditCaseBNonSaturatedBranch
      B terminal chain hterminal hlock hbudget).terminal = terminal := rfl

theorem genericChainToSSLock_of_auditCaseBNonSaturatedBranch_locked
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    SSLock
      (genericChainToSSLock_of_auditCaseBNonSaturatedBranch
        B terminal chain hterminal hlock hbudget).terminal := by
  exact hlock

theorem genericChainToSSLock_of_auditCaseBNonSaturatedBranch_budget
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    GenericChainWithinBudget
      (genericChainToSSLock_of_auditCaseBNonSaturatedBranch
        B terminal chain hterminal hlock hbudget).chain := by
  exact hbudget

theorem exists_caseBNonSaturatedLockAssembly_of_branch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    ∃ _ : CaseBNonSaturatedLockAssembly C, True := by
  exact ⟨
    caseBNonSaturatedLockAssembly_of_branch
      B terminal chain hterminal hlock hbudget,
    trivial
  ⟩

theorem exists_genericChainToSSLock_of_auditCaseBNonSaturatedBranch
    {C : Context}
    (B : AuditCaseBNonSaturatedBranch C)
    (terminal : Context)
    (chain : GenericChain C terminal)
    (hterminal :
      terminal =
        CaseBNonSaturatedBackboneTrace.terminal
          (caseBNonSaturatedBackboneTrace_of_branch B))
    (hlock : SSLock terminal)
    (hbudget : GenericChainWithinBudget chain) :
    ∃ _ : GenericChainToSSLock C, True := by
  exact ⟨
    genericChainToSSLock_of_auditCaseBNonSaturatedBranch
      B terminal chain hterminal hlock hbudget,
    trivial
  ⟩

end CaseB
end Lehmer