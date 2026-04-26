-- FILE: Lean/Lehmer/Audit/CaseC/Params.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace Audit
namespace CaseC

structure AuditCaseCParamsData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  params : Lehmer.CaseC.Params

@[simp] theorem AuditCaseCParamsData.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) (P : Lehmer.CaseC.Params) :
    (AuditCaseCParamsData.mk hC P).inCaseC = hC := rfl

@[simp] theorem AuditCaseCParamsData.params_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) (P : Lehmer.CaseC.Params) :
    (AuditCaseCParamsData.mk hC P).params = P := rfl

def auditCaseCParamsOf {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Lehmer.CaseC.Params :=
  ⟨Lehmer.Pipeline.pivotOf n, Lehmer.Pipeline.pivotOf n⟩

@[simp] theorem auditCaseCParamsOf_level
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.level (auditCaseCParamsOf hC) = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCParamsOf_width
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.width (auditCaseCParamsOf hC) = Lehmer.Pipeline.pivotOf n := rfl

def auditCaseCParamsDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : AuditCaseCParamsData n :=
  AuditCaseCParamsData.mk hC (auditCaseCParamsOf hC)

@[simp] theorem auditCaseCParamsDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCParamsDataOf hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCParamsDataOf_params
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCParamsDataOf hC).params = auditCaseCParamsOf hC := rfl

theorem AuditCaseCParamsData.in_caseC
    {n : ℕ} (X : AuditCaseCParamsData n) :
    Lehmer.Pipeline.InCaseC n := by
  exact X.inCaseC

def AuditCaseCParamsData.level
    {n : ℕ} (X : AuditCaseCParamsData n) : ℕ :=
  Lehmer.CaseC.level X.params

@[simp] theorem AuditCaseCParamsData.level_def
    {n : ℕ} (X : AuditCaseCParamsData n) :
    X.level = Lehmer.CaseC.level X.params := rfl

def AuditCaseCParamsData.width
    {n : ℕ} (X : AuditCaseCParamsData n) : ℕ :=
  Lehmer.CaseC.width X.params

@[simp] theorem AuditCaseCParamsData.width_def
    {n : ℕ} (X : AuditCaseCParamsData n) :
    X.width = Lehmer.CaseC.width X.params := rfl

@[simp] theorem auditCaseCParamsDataOf_level
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCParamsDataOf hC).level = Lehmer.Pipeline.pivotOf n := by
  rfl

@[simp] theorem auditCaseCParamsDataOf_width
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCParamsDataOf hC).width = Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCParams_level_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ Lehmer.CaseC.level (auditCaseCParamsOf hC) := by
  exact hC.1

theorem auditCaseCParams_width_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ Lehmer.CaseC.width (auditCaseCParamsOf hC) := by
  exact hC.1

theorem auditCaseCParams_level_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.level (auditCaseCParamsOf hC) < Lehmer.Pipeline.YC := by
  exact hC.2

theorem auditCaseCParams_width_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.width (auditCaseCParamsOf hC) < Lehmer.Pipeline.YC := by
  exact hC.2

theorem AuditCaseCParamsData.level_ge_YA
    {n : ℕ} (X : AuditCaseCParamsData n) :
    Lehmer.Pipeline.YA ≤ X.level := by
  exact auditCaseCParams_level_ge_YA X.inCaseC

theorem AuditCaseCParamsData.width_ge_YA
    {n : ℕ} (X : AuditCaseCParamsData n) :
    Lehmer.Pipeline.YA ≤ X.width := by
  exact auditCaseCParams_width_ge_YA X.inCaseC

theorem AuditCaseCParamsData.level_lt_YC
    {n : ℕ} (X : AuditCaseCParamsData n) :
    X.level < Lehmer.Pipeline.YC := by
  exact auditCaseCParams_level_lt_YC X.inCaseC

theorem AuditCaseCParamsData.width_lt_YC
    {n : ℕ} (X : AuditCaseCParamsData n) :
    X.width < Lehmer.Pipeline.YC := by
  exact auditCaseCParams_width_lt_YC X.inCaseC

end CaseC
end Audit
end Lehmer