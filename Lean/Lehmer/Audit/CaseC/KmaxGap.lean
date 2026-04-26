-- FILE: Lean/Lehmer/Audit/CaseC/KmaxGap.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.CaseC.GapClosure.KmaxGap : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Audit.CaseC.Params : def thm
- Lehmer.Audit.CaseC.ClosureData : def thm
- Lehmer.Audit.CaseC.NonIntegrality : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.KmaxGap
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Audit.CaseC.Params
import Lehmer.Audit.CaseC.ClosureData
import Lehmer.Audit.CaseC.NonIntegrality

namespace Lehmer
namespace Audit
namespace CaseC

structure AuditCaseCKmaxGapData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  params : Lehmer.CaseC.Params
  closure : Lehmer.CaseC.ClosureData params
  nonIntegrality :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage params closure
  kmaxGap :
    Lehmer.CaseC.GapClosure.KmaxGapPackage params closure

@[simp] theorem AuditCaseCKmaxGapData.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (N : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    (AuditCaseCKmaxGapData.mk hC P D N K).inCaseC = hC := rfl

@[simp] theorem AuditCaseCKmaxGapData.params_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (N : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    (AuditCaseCKmaxGapData.mk hC P D N K).params = P := rfl

@[simp] theorem AuditCaseCKmaxGapData.closure_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (N : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    (AuditCaseCKmaxGapData.mk hC P D N K).closure = D := rfl

@[simp] theorem AuditCaseCKmaxGapData.nonIntegrality_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (N : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    (AuditCaseCKmaxGapData.mk hC P D N K).nonIntegrality = N := rfl

@[simp] theorem AuditCaseCKmaxGapData.kmaxGap_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (N : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    (AuditCaseCKmaxGapData.mk hC P D N K).kmaxGap = K := rfl

def auditCaseCKmaxGapOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.KmaxGapPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  let N := auditCaseCNonIntegralityOf hC
  let G :=
    Lehmer.CaseC.GapClosure.mkPositiveGapData
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      N 1 (by decide)
  let K :=
    Lehmer.CaseC.GapClosure.mkKmaxData
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      1 (by decide)
  let C :=
    Lehmer.CaseC.GapClosure.mkClosureCapCandidate
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      1 (by decide)
  Lehmer.CaseC.GapClosure.mkKmaxGapPackage
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    G K C

def auditCaseCKmaxGapDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCKmaxGapData n :=
  AuditCaseCKmaxGapData.mk hC
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCNonIntegralityOf hC)
    (auditCaseCKmaxGapOf hC)

@[simp] theorem auditCaseCKmaxGapDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_params
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).params = auditCaseCParamsOf hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_closure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).closure = auditCaseCClosureDataOf hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_nonIntegrality
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).nonIntegrality = auditCaseCNonIntegralityOf hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_kmaxGap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).kmaxGap = auditCaseCKmaxGapOf hC := rfl

theorem AuditCaseCKmaxGapData.in_caseC
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.Pipeline.InCaseC n := by
  exact X.inCaseC

def AuditCaseCKmaxGapData.level
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℕ :=
  Lehmer.CaseC.level X.params

@[simp] theorem AuditCaseCKmaxGapData.level_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.level = Lehmer.CaseC.level X.params := rfl

def AuditCaseCKmaxGapData.width
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℕ :=
  Lehmer.CaseC.width X.params

@[simp] theorem AuditCaseCKmaxGapData.width_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.width = Lehmer.CaseC.width X.params := rfl

def AuditCaseCKmaxGapData.cap
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℕ :=
  Lehmer.CaseC.cap X.params X.closure

@[simp] theorem AuditCaseCKmaxGapData.cap_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.cap = Lehmer.CaseC.cap X.params X.closure := rfl

def AuditCaseCKmaxGapData.omegaBound
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℕ :=
  Lehmer.CaseC.omegaBound X.params X.closure

@[simp] theorem AuditCaseCKmaxGapData.omegaBound_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.omegaBound = Lehmer.CaseC.omegaBound X.params X.closure := rfl

def AuditCaseCKmaxGapData.nonIntegralityPackage
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage X.params X.closure :=
  X.nonIntegrality

@[simp] theorem AuditCaseCKmaxGapData.nonIntegralityPackage_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.nonIntegralityPackage = X.nonIntegrality := rfl

def AuditCaseCKmaxGapData.kmaxGapPackage
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.CaseC.GapClosure.KmaxGapPackage X.params X.closure :=
  X.kmaxGap

@[simp] theorem AuditCaseCKmaxGapData.kmaxGapPackage_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.kmaxGapPackage = X.kmaxGap := rfl

def AuditCaseCKmaxGapData.gapFamily
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.CaseC.GapClosure.SupportProfileFamily :=
  Lehmer.CaseC.GapClosure.kmaxGapFamily X.params X.closure X.kmaxGap

@[simp] theorem AuditCaseCKmaxGapData.gapFamily_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.gapFamily =
      Lehmer.CaseC.GapClosure.kmaxGapFamily X.params X.closure X.kmaxGap := rfl

def AuditCaseCKmaxGapData.gapValue
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℕ :=
  Lehmer.CaseC.GapClosure.kmaxGapValue X.params X.closure X.kmaxGap

@[simp] theorem AuditCaseCKmaxGapData.gapValue_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.gapValue =
      Lehmer.CaseC.GapClosure.kmaxGapValue X.params X.closure X.kmaxGap := rfl

def AuditCaseCKmaxGapData.kmaxValue
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℕ :=
  Lehmer.CaseC.GapClosure.kmaxGapKmaxValue X.params X.closure X.kmaxGap

@[simp] theorem AuditCaseCKmaxGapData.kmaxValue_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.kmaxValue =
      Lehmer.CaseC.GapClosure.kmaxGapKmaxValue X.params X.closure X.kmaxGap := rfl

def AuditCaseCKmaxGapData.closureCapValue
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℕ :=
  Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue X.params X.closure X.kmaxGap

@[simp] theorem AuditCaseCKmaxGapData.closureCapValue_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.closureCapValue =
      Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue X.params X.closure X.kmaxGap := rfl

theorem auditCaseCKmaxGap_level_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.level (auditCaseCParamsOf hC) = Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCKmaxGap_width_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.width (auditCaseCParamsOf hC) = Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCKmaxGap_cap_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.cap (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) =
      Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCKmaxGap_omegaBound_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.omegaBound (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) =
      Lehmer.Pipeline.pivotOf n := by
  rfl

@[simp] theorem auditCaseCKmaxGapDataOf_level
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).level = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_width
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).width = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_cap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).cap = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_omegaBound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).omegaBound = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_gapValue
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).gapValue = 1 := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_kmaxValue
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).kmaxValue = 1 := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_closureCapValue
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCKmaxGapDataOf hC).closureCapValue = 1 := rfl

theorem AuditCaseCKmaxGapData.level_ge_YA
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.Pipeline.YA ≤ X.level := by
  exact X.inCaseC.1

theorem AuditCaseCKmaxGapData.width_ge_YA
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.Pipeline.YA ≤ X.width := by
  exact X.inCaseC.1

theorem AuditCaseCKmaxGapData.cap_ge_YA
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.Pipeline.YA ≤ X.cap := by
  exact X.inCaseC.1

theorem AuditCaseCKmaxGapData.omegaBound_ge_YA
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    Lehmer.Pipeline.YA ≤ X.omegaBound := by
  exact X.inCaseC.1

theorem AuditCaseCKmaxGapData.level_lt_YC
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.level < Lehmer.Pipeline.YC := by
  exact X.inCaseC.2

theorem AuditCaseCKmaxGapData.width_lt_YC
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.width < Lehmer.Pipeline.YC := by
  exact X.inCaseC.2

theorem AuditCaseCKmaxGapData.cap_lt_YC
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.cap < Lehmer.Pipeline.YC := by
  exact X.inCaseC.2

theorem AuditCaseCKmaxGapData.omegaBound_lt_YC
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.omegaBound < Lehmer.Pipeline.YC := by
  exact X.inCaseC.2

structure CaseCKmaxGapAuditRouting
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  package :
    Lehmer.CaseC.GapClosure.KmaxGapPackage P D

@[simp] theorem CaseCKmaxGapAuditRouting.package_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    (CaseCKmaxGapAuditRouting.mk X).package = X := rfl

def CaseCKmaxGapAuditRouting.family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    Lehmer.CaseC.GapClosure.SupportProfileFamily :=
  Lehmer.CaseC.GapClosure.kmaxGapFamily P D R.package

@[simp] theorem CaseCKmaxGapAuditRouting.family_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    R.family = Lehmer.CaseC.GapClosure.kmaxGapFamily P D R.package := rfl

def CaseCKmaxGapAuditRouting.gapValue
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) : ℕ :=
  Lehmer.CaseC.GapClosure.kmaxGapValue P D R.package

@[simp] theorem CaseCKmaxGapAuditRouting.gapValue_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    R.gapValue = Lehmer.CaseC.GapClosure.kmaxGapValue P D R.package := rfl

def CaseCKmaxGapAuditRouting.kmaxValue
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) : ℕ :=
  Lehmer.CaseC.GapClosure.kmaxGapKmaxValue P D R.package

@[simp] theorem CaseCKmaxGapAuditRouting.kmaxValue_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    R.kmaxValue = Lehmer.CaseC.GapClosure.kmaxGapKmaxValue P D R.package := rfl

def CaseCKmaxGapAuditRouting.closureCapValue
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) : ℕ :=
  Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue P D R.package

@[simp] theorem CaseCKmaxGapAuditRouting.closureCapValue_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    R.closureCapValue =
      Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue P D R.package := rfl

def caseCKmaxGapAuditRouting_of_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    CaseCKmaxGapAuditRouting P D :=
  CaseCKmaxGapAuditRouting.mk X

@[simp] theorem caseCKmaxGapAuditRouting_of_package_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.KmaxGapPackage P D) :
    (caseCKmaxGapAuditRouting_of_package P D X).package = X := rfl

def caseCKmaxGapAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCKmaxGapAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  caseCKmaxGapAuditRouting_of_package
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCKmaxGapOf hC)

@[simp] theorem caseCKmaxGapAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCKmaxGapAuditRouting_of_inCaseC hC).package =
      auditCaseCKmaxGapOf hC := rfl

@[simp] theorem caseCKmaxGapAuditRouting_of_inCaseC_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCKmaxGapAuditRouting_of_inCaseC hC).family =
      Lehmer.CaseC.GapClosure.kmaxGapFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCKmaxGapOf hC) := rfl

@[simp] theorem caseCKmaxGapAuditRouting_of_inCaseC_gapValue
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCKmaxGapAuditRouting_of_inCaseC hC).gapValue = 1 := rfl

@[simp] theorem caseCKmaxGapAuditRouting_of_inCaseC_kmaxValue
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCKmaxGapAuditRouting_of_inCaseC hC).kmaxValue = 1 := rfl

@[simp] theorem caseCKmaxGapAuditRouting_of_inCaseC_closureCapValue
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCKmaxGapAuditRouting_of_inCaseC hC).closureCapValue = 1 := rfl

theorem caseCKmaxGapAuditRouting_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    ∃ X : Lehmer.CaseC.GapClosure.KmaxGapPackage P D, True := by
  exact ⟨R.package, trivial⟩

theorem exists_caseCKmaxGapAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ R : CaseCKmaxGapAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC), True := by
  exact ⟨caseCKmaxGapAuditRouting_of_inCaseC hC, trivial⟩

theorem CaseCKmaxGapAuditRouting.gapValue_pos
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    0 < R.gapValue := by
  exact Lehmer.CaseC.GapClosure.kmaxGapValue_pos P D R.package

theorem CaseCKmaxGapAuditRouting.kmaxValue_pos
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    0 < R.kmaxValue := by
  exact Lehmer.CaseC.GapClosure.kmaxGapKmaxValue_pos P D R.package

theorem CaseCKmaxGapAuditRouting.closureCapValue_pos
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    0 < R.closureCapValue := by
  exact Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue_pos P D R.package

theorem CaseCKmaxGapAuditRouting.mem_hasWitness
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    ∀ S,
      S ∈ R.family →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness P D S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_hasWitness P D R.package S hS

theorem CaseCKmaxGapAuditRouting.mem_rigid
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    ∀ S,
      S ∈ R.family →
      Lehmer.CaseC.GapClosure.RigidProfile P D S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_rigid P D R.package S hS

theorem caseCKmaxGapAuditRouting_of_inCaseC_gapValue_pos
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    0 < (caseCKmaxGapAuditRouting_of_inCaseC hC).gapValue := by
  exact CaseCKmaxGapAuditRouting.gapValue_pos
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC)

theorem caseCKmaxGapAuditRouting_of_inCaseC_kmaxValue_pos
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    0 < (caseCKmaxGapAuditRouting_of_inCaseC hC).kmaxValue := by
  exact CaseCKmaxGapAuditRouting.kmaxValue_pos
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC)

theorem caseCKmaxGapAuditRouting_of_inCaseC_closureCapValue_pos
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    0 < (caseCKmaxGapAuditRouting_of_inCaseC hC).closureCapValue := by
  exact CaseCKmaxGapAuditRouting.closureCapValue_pos
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC)

theorem caseCKmaxGapAuditRouting_of_inCaseC_mem_hasWitness
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∀ S,
      S ∈ (caseCKmaxGapAuditRouting_of_inCaseC hC).family →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  exact CaseCKmaxGapAuditRouting.mem_hasWitness
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC)

theorem caseCKmaxGapAuditRouting_of_inCaseC_mem_rigid
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∀ S,
      S ∈ (caseCKmaxGapAuditRouting_of_inCaseC hC).family →
      Lehmer.CaseC.GapClosure.RigidProfile
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  exact CaseCKmaxGapAuditRouting.mem_rigid
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC)

def CaseCKmaxGapAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty
    (CaseCKmaxGapAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

theorem caseCKmaxGapAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCKmaxGapAuditAvailable hC := by
  exact ⟨caseCKmaxGapAuditRouting_of_inCaseC hC⟩

end CaseC
end Audit
end Lehmer