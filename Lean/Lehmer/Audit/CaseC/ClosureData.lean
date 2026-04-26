-- FILE: Lean/Lehmer/Audit/CaseC/ClosureData.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Audit.CaseC.Params : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Audit.CaseC.Params

namespace Lehmer
namespace Audit
namespace CaseC

structure AuditCaseCClosureData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  params : Lehmer.CaseC.Params
  closure : Lehmer.CaseC.ClosureData params
  params_eq : params = auditCaseCParamsOf inCaseC
  closure_eq :
    HEq closure
      ({ N := Lehmer.Pipeline.pivotOf n, omegaHat := Lehmer.Pipeline.pivotOf n } :
        Lehmer.CaseC.ClosureData (auditCaseCParamsOf inCaseC))

@[simp] theorem AuditCaseCClosureData.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (hP : P = auditCaseCParamsOf hC)
    (hD :
      HEq D
        ({ N := Lehmer.Pipeline.pivotOf n, omegaHat := Lehmer.Pipeline.pivotOf n } :
          Lehmer.CaseC.ClosureData (auditCaseCParamsOf hC))) :
    (AuditCaseCClosureData.mk hC P D hP hD).inCaseC = hC := rfl

@[simp] theorem AuditCaseCClosureData.params_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (hP : P = auditCaseCParamsOf hC)
    (hD :
      HEq D
        ({ N := Lehmer.Pipeline.pivotOf n, omegaHat := Lehmer.Pipeline.pivotOf n } :
          Lehmer.CaseC.ClosureData (auditCaseCParamsOf hC))) :
    (AuditCaseCClosureData.mk hC P D hP hD).params = P := rfl

@[simp] theorem AuditCaseCClosureData.closure_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (hP : P = auditCaseCParamsOf hC)
    (hD :
      HEq D
        ({ N := Lehmer.Pipeline.pivotOf n, omegaHat := Lehmer.Pipeline.pivotOf n } :
          Lehmer.CaseC.ClosureData (auditCaseCParamsOf hC))) :
    (AuditCaseCClosureData.mk hC P D hP hD).closure = D := rfl

def auditCaseCClosureDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.ClosureData (auditCaseCParamsOf hC) :=
  { N := Lehmer.Pipeline.pivotOf n, omegaHat := Lehmer.Pipeline.pivotOf n }

@[simp] theorem auditCaseCClosureDataOf_cap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.cap (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) =
      Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCClosureDataOf_omegaBound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.omegaBound (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) =
      Lehmer.Pipeline.pivotOf n := rfl

def auditCaseCClosureDataDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCClosureData n :=
  AuditCaseCClosureData.mk
    hC
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    rfl
    (by rfl)

@[simp] theorem auditCaseCClosureDataDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCClosureDataDataOf_params
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).params = auditCaseCParamsOf hC := rfl

@[simp] theorem auditCaseCClosureDataDataOf_closure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).closure = auditCaseCClosureDataOf hC := rfl

theorem AuditCaseCClosureData.in_caseC
    {n : ℕ} (X : AuditCaseCClosureData n) :
    Lehmer.Pipeline.InCaseC n := by
  exact X.inCaseC

def AuditCaseCClosureData.level
    {n : ℕ} (X : AuditCaseCClosureData n) : ℕ :=
  Lehmer.CaseC.level X.params

@[simp] theorem AuditCaseCClosureData.level_def
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.level = Lehmer.CaseC.level X.params := rfl

def AuditCaseCClosureData.width
    {n : ℕ} (X : AuditCaseCClosureData n) : ℕ :=
  Lehmer.CaseC.width X.params

@[simp] theorem AuditCaseCClosureData.width_def
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.width = Lehmer.CaseC.width X.params := rfl

def AuditCaseCClosureData.cap
    {n : ℕ} (X : AuditCaseCClosureData n) : ℕ :=
  Lehmer.CaseC.cap X.params X.closure

@[simp] theorem AuditCaseCClosureData.cap_def
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.cap = Lehmer.CaseC.cap X.params X.closure := rfl

def AuditCaseCClosureData.omegaBound
    {n : ℕ} (X : AuditCaseCClosureData n) : ℕ :=
  Lehmer.CaseC.omegaBound X.params X.closure

@[simp] theorem AuditCaseCClosureData.omegaBound_def
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.omegaBound = Lehmer.CaseC.omegaBound X.params X.closure := rfl

@[simp] theorem auditCaseCClosureDataDataOf_level
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).level = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCClosureDataDataOf_width
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).width = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCClosureDataDataOf_cap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).cap = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCClosureDataDataOf_omegaBound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).omegaBound = Lehmer.Pipeline.pivotOf n := rfl

theorem auditCaseCClosure_level_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ Lehmer.CaseC.level (auditCaseCParamsOf hC) := by
  exact hC.1

theorem auditCaseCClosure_width_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ Lehmer.CaseC.width (auditCaseCParamsOf hC) := by
  exact hC.1

theorem auditCaseCClosure_cap_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤
      Lehmer.CaseC.cap (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) := by
  exact hC.1

theorem auditCaseCClosure_omegaBound_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤
      Lehmer.CaseC.omegaBound (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) := by
  exact hC.1

theorem auditCaseCClosure_level_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.level (auditCaseCParamsOf hC) < Lehmer.Pipeline.YC := by
  exact hC.2

theorem auditCaseCClosure_width_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.width (auditCaseCParamsOf hC) < Lehmer.Pipeline.YC := by
  exact hC.2

theorem auditCaseCClosure_cap_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.cap (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) <
      Lehmer.Pipeline.YC := by
  exact hC.2

theorem auditCaseCClosure_omegaBound_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.omegaBound (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) <
      Lehmer.Pipeline.YC := by
  exact hC.2

theorem AuditCaseCClosureData.params_eq_audit
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.params = auditCaseCParamsOf X.inCaseC := by
  exact X.params_eq

theorem AuditCaseCClosureData.level_eq_pivot
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.level = Lehmer.Pipeline.pivotOf n := by
  rw [AuditCaseCClosureData.level_def, X.params_eq]
  rfl

theorem AuditCaseCClosureData.width_eq_pivot
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.width = Lehmer.Pipeline.pivotOf n := by
  rw [AuditCaseCClosureData.width_def, X.params_eq]
  rfl

theorem AuditCaseCClosureData.cap_eq_pivot
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.cap = Lehmer.Pipeline.pivotOf n := by
  cases X with
  | mk hC P D hP hD =>
      cases hP
      cases hD
      rfl

theorem AuditCaseCClosureData.omegaBound_eq_pivot
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.omegaBound = Lehmer.Pipeline.pivotOf n := by
  cases X with
  | mk hC P D hP hD =>
      cases hP
      cases hD
      rfl

theorem AuditCaseCClosureData.level_ge_YA
    {n : ℕ} (X : AuditCaseCClosureData n) :
    Lehmer.Pipeline.YA ≤ X.level := by
  rw [X.level_eq_pivot]
  exact X.inCaseC.1

theorem AuditCaseCClosureData.width_ge_YA
    {n : ℕ} (X : AuditCaseCClosureData n) :
    Lehmer.Pipeline.YA ≤ X.width := by
  rw [X.width_eq_pivot]
  exact X.inCaseC.1

theorem AuditCaseCClosureData.cap_ge_YA
    {n : ℕ} (X : AuditCaseCClosureData n) :
    Lehmer.Pipeline.YA ≤ X.cap := by
  rw [X.cap_eq_pivot]
  exact X.inCaseC.1

theorem AuditCaseCClosureData.omegaBound_ge_YA
    {n : ℕ} (X : AuditCaseCClosureData n) :
    Lehmer.Pipeline.YA ≤ X.omegaBound := by
  rw [X.omegaBound_eq_pivot]
  exact X.inCaseC.1

theorem AuditCaseCClosureData.level_lt_YC
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.level < Lehmer.Pipeline.YC := by
  rw [X.level_eq_pivot]
  exact X.inCaseC.2

theorem AuditCaseCClosureData.width_lt_YC
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.width < Lehmer.Pipeline.YC := by
  rw [X.width_eq_pivot]
  exact X.inCaseC.2

theorem AuditCaseCClosureData.cap_lt_YC
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.cap < Lehmer.Pipeline.YC := by
  rw [X.cap_eq_pivot]
  exact X.inCaseC.2

theorem AuditCaseCClosureData.omegaBound_lt_YC
    {n : ℕ} (X : AuditCaseCClosureData n) :
    X.omegaBound < Lehmer.Pipeline.YC := by
  rw [X.omegaBound_eq_pivot]
  exact X.inCaseC.2

def AuditCaseCClosureDataAvailable
    {n : ℕ} (_hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty (AuditCaseCClosureData n)

theorem auditCaseCClosureDataAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCClosureDataAvailable hC := by
  exact ⟨auditCaseCClosureDataDataOf hC⟩

theorem auditCaseCClosureData_params_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).params = auditCaseCParamsOf hC := rfl

theorem auditCaseCClosureData_closure_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCClosureDataDataOf hC).closure = auditCaseCClosureDataOf hC := rfl

theorem auditCaseCClosureData_cap_eq_pivot
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.cap
      (auditCaseCClosureDataDataOf hC).params
      (auditCaseCClosureDataDataOf hC).closure =
        Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCClosureData_omegaBound_eq_pivot
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.omegaBound
      (auditCaseCClosureDataDataOf hC).params
      (auditCaseCClosureDataDataOf hC).closure =
        Lehmer.Pipeline.pivotOf n := by
  rfl

end CaseC
end Audit
end Lehmer