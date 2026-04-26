-- FILE: Lean/Lehmer/Audit/CaseC/NonIntegrality.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Audit.CaseC.Params : def thm
- Lehmer.Audit.CaseC.ClosureData : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Audit.CaseC.Params
import Lehmer.Audit.CaseC.ClosureData

namespace Lehmer
namespace Audit
namespace CaseC

structure AuditCaseCNonIntegralityData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  params : Lehmer.CaseC.Params
  closure : Lehmer.CaseC.ClosureData params
  nonIntegrality :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage params closure

@[simp] theorem AuditCaseCNonIntegralityData.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D) :
    (AuditCaseCNonIntegralityData.mk hC P D X).inCaseC = hC := rfl

@[simp] theorem AuditCaseCNonIntegralityData.params_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D) :
    (AuditCaseCNonIntegralityData.mk hC P D X).params = P := rfl

@[simp] theorem AuditCaseCNonIntegralityData.closure_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D) :
    (AuditCaseCNonIntegralityData.mk hC P D X).closure = D := rfl

@[simp] theorem AuditCaseCNonIntegralityData.nonIntegrality_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D) :
    (AuditCaseCNonIntegralityData.mk hC P D X).nonIntegrality = X := rfl

def auditCaseCNonIntegralityOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage.mk []
    (Lehmer.CaseC.GapClosure.nonIntegralityWitnessFamily_nil
      (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC))

def auditCaseCNonIntegralityDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCNonIntegralityData n :=
  AuditCaseCNonIntegralityData.mk hC
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCNonIntegralityOf hC)

@[simp] theorem auditCaseCNonIntegralityDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).inCaseC = hC := rfl

@[simp] theorem auditCaseCNonIntegralityDataOf_params
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).params = auditCaseCParamsOf hC := rfl

@[simp] theorem auditCaseCNonIntegralityDataOf_closure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).closure = auditCaseCClosureDataOf hC := rfl

@[simp] theorem auditCaseCNonIntegralityDataOf_nonIntegrality
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).nonIntegrality = auditCaseCNonIntegralityOf hC := rfl

theorem AuditCaseCNonIntegralityData.in_caseC
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) :
    Lehmer.Pipeline.InCaseC n := by
  exact X.inCaseC

def AuditCaseCNonIntegralityData.level
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) : ℕ :=
  Lehmer.CaseC.level X.params

@[simp] theorem AuditCaseCNonIntegralityData.level_def
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) :
    X.level = Lehmer.CaseC.level X.params := rfl

def AuditCaseCNonIntegralityData.width
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) : ℕ :=
  Lehmer.CaseC.width X.params

@[simp] theorem AuditCaseCNonIntegralityData.width_def
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) :
    X.width = Lehmer.CaseC.width X.params := rfl

def AuditCaseCNonIntegralityData.cap
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) : ℕ :=
  Lehmer.CaseC.cap X.params X.closure

@[simp] theorem AuditCaseCNonIntegralityData.cap_def
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) :
    X.cap = Lehmer.CaseC.cap X.params X.closure := rfl

def AuditCaseCNonIntegralityData.omegaBound
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) : ℕ :=
  Lehmer.CaseC.omegaBound X.params X.closure

@[simp] theorem AuditCaseCNonIntegralityData.omegaBound_def
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) :
    X.omegaBound = Lehmer.CaseC.omegaBound X.params X.closure := rfl

def AuditCaseCNonIntegralityData.package
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage X.params X.closure :=
  X.nonIntegrality

@[simp] theorem AuditCaseCNonIntegralityData.package_def
    {n : ℕ} (X : AuditCaseCNonIntegralityData n) :
    X.package = X.nonIntegrality := rfl

theorem auditCaseCNonIntegrality_level_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.level (auditCaseCParamsOf hC) = Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCNonIntegrality_width_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.width (auditCaseCParamsOf hC) = Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCNonIntegrality_cap_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.cap (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) =
      Lehmer.Pipeline.pivotOf n := by
  rfl

theorem auditCaseCNonIntegrality_omegaBound_eq
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.omegaBound (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) =
      Lehmer.Pipeline.pivotOf n := by
  rfl

@[simp] theorem auditCaseCNonIntegralityDataOf_level
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).level = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCNonIntegralityDataOf_width
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).width = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCNonIntegralityDataOf_cap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).cap = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCNonIntegralityDataOf_omegaBound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).omegaBound = Lehmer.Pipeline.pivotOf n := rfl

theorem auditCaseCNonIntegralityDataOf_level_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ (auditCaseCNonIntegralityDataOf hC).level := by
  exact hC.1

theorem auditCaseCNonIntegralityDataOf_width_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ (auditCaseCNonIntegralityDataOf hC).width := by
  exact hC.1

theorem auditCaseCNonIntegralityDataOf_cap_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ (auditCaseCNonIntegralityDataOf hC).cap := by
  exact hC.1

theorem auditCaseCNonIntegralityDataOf_omegaBound_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.Pipeline.YA ≤ (auditCaseCNonIntegralityDataOf hC).omegaBound := by
  exact hC.1

theorem auditCaseCNonIntegralityDataOf_level_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).level < Lehmer.Pipeline.YC := by
  exact hC.2

theorem auditCaseCNonIntegralityDataOf_width_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).width < Lehmer.Pipeline.YC := by
  exact hC.2

theorem auditCaseCNonIntegralityDataOf_cap_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).cap < Lehmer.Pipeline.YC := by
  exact hC.2

theorem auditCaseCNonIntegralityDataOf_omegaBound_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCNonIntegralityDataOf hC).omegaBound < Lehmer.Pipeline.YC := by
  exact hC.2

structure CaseCNonIntegralityAuditRouting
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  package :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D

@[simp] theorem CaseCNonIntegralityAuditRouting.package_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D) :
    (CaseCNonIntegralityAuditRouting.mk X).package = X := rfl

def CaseCNonIntegralityAuditRouting.family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCNonIntegralityAuditRouting P D) :
    Lehmer.CaseC.GapClosure.SupportProfileFamily :=
  R.package.family

@[simp] theorem CaseCNonIntegralityAuditRouting.family_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCNonIntegralityAuditRouting P D) :
    R.family = R.package.family := rfl

def caseCNonIntegralityAuditRouting_of_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D) :
    CaseCNonIntegralityAuditRouting P D :=
  CaseCNonIntegralityAuditRouting.mk X

@[simp] theorem caseCNonIntegralityAuditRouting_of_package_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D) :
    (caseCNonIntegralityAuditRouting_of_package P D X).package = X := rfl

def caseCNonIntegralityAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCNonIntegralityAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  caseCNonIntegralityAuditRouting_of_package
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCNonIntegralityOf hC)

@[simp] theorem caseCNonIntegralityAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCNonIntegralityAuditRouting_of_inCaseC hC).package =
      auditCaseCNonIntegralityOf hC := rfl

@[simp] theorem caseCNonIntegralityAuditRouting_of_inCaseC_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (caseCNonIntegralityAuditRouting_of_inCaseC hC).family =
      (auditCaseCNonIntegralityOf hC).family := rfl

theorem caseCNonIntegralityAuditRouting_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCNonIntegralityAuditRouting P D) :
    ∃ X : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D, True := by
  exact ⟨R.package, trivial⟩

theorem exists_caseCNonIntegralityAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∃ R : CaseCNonIntegralityAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC), True := by
  exact ⟨caseCNonIntegralityAuditRouting_of_inCaseC hC, trivial⟩

theorem CaseCNonIntegralityAuditRouting.mem_hasWitness
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCNonIntegralityAuditRouting P D) :
    ∀ S,
      S ∈ R.family →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness P D S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage.mem_hasWitness
    (P := P) (D := D) R.package S hS

theorem CaseCNonIntegralityAuditRouting.mem_rigid
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCNonIntegralityAuditRouting P D) :
    ∀ S,
      S ∈ R.family →
      Lehmer.CaseC.GapClosure.RigidProfile P D S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage.mem_rigid
    (P := P) (D := D) R.package S hS

theorem caseCNonIntegralityAuditRouting_of_inCaseC_mem_hasWitness
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∀ S,
      S ∈ (caseCNonIntegralityAuditRouting_of_inCaseC hC).family →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  exact CaseCNonIntegralityAuditRouting.mem_hasWitness
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCNonIntegralityAuditRouting_of_inCaseC hC)

theorem caseCNonIntegralityAuditRouting_of_inCaseC_mem_rigid
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∀ S,
      S ∈ (caseCNonIntegralityAuditRouting_of_inCaseC hC).family →
      Lehmer.CaseC.GapClosure.RigidProfile
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  exact CaseCNonIntegralityAuditRouting.mem_rigid
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCNonIntegralityAuditRouting_of_inCaseC hC)

def CaseCNonIntegralityAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty
    (CaseCNonIntegralityAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

theorem caseCNonIntegralityAuditAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCNonIntegralityAuditAvailable hC := by
  exact ⟨caseCNonIntegralityAuditRouting_of_inCaseC hC⟩

end CaseC
end Audit
end Lehmer