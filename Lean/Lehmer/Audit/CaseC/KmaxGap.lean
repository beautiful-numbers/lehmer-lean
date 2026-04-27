-- FILE: Lean/Lehmer/Audit/CaseC/KmaxGap.lean
/-
IMPORT CLASSIFICATION

Lehmer.Prelude : meta
Lehmer.Basic.Defs : def
Lehmer.CaseC.Spec : def
Lehmer.CaseC.GapClosure.SupportProfiles : def thm
Lehmer.CaseC.GapClosure.Rigidity : def thm
Lehmer.CaseC.GapClosure.NonIntegrality : def thm
Lehmer.CaseC.GapClosure.KmaxGap : def thm
Lehmer.Pipeline.GlobalSplit : def thm
Lehmer.Audit.CaseC.Params : def thm
Lehmer.Audit.CaseC.ClosureData : def thm
Lehmer.Audit.CaseC.NonIntegrality : def thm
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

open Lehmer.Basic

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

structure AuditCaseCKmaxGapReconstruction
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) where
  kmaxGap :
    Lehmer.CaseC.GapClosure.KmaxGapPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
  nonIntegrality_agrees :
    Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      kmaxGap =
      auditCaseCNonIntegralityOf hC

@[simp] theorem AuditCaseCKmaxGapReconstruction.kmaxGap_mk
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (K :
      Lehmer.CaseC.GapClosure.KmaxGapPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC))
    (hK :
      Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        K =
        auditCaseCNonIntegralityOf hC) :
    (AuditCaseCKmaxGapReconstruction.mk K hK).kmaxGap = K := rfl

@[simp] theorem AuditCaseCKmaxGapReconstruction.nonIntegrality_agrees_mk
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (K :
      Lehmer.CaseC.GapClosure.KmaxGapPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC))
    (hK :
      Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        K =
        auditCaseCNonIntegralityOf hC) :
    (AuditCaseCKmaxGapReconstruction.mk K hK).nonIntegrality_agrees = hK := rfl

theorem AuditCaseCKmaxGapReconstruction.family_eq_auditNonIntegralityFamily
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    R.kmaxGap.family = (auditCaseCNonIntegralityOf hC).family := by
  have hEq := R.nonIntegrality_agrees
  rw [← hEq]
  rfl

theorem AuditCaseCKmaxGapReconstruction.witnesses_eq_auditNonIntegralityWitnesses
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    HEq R.kmaxGap.nonIntegrality (auditCaseCNonIntegralityOf hC).witnesses := by
  cases R with
  | mk K hAgree =>
      cases K with
      | mk F hRigid hNI hGap hKmax hClosureCap =>
          have hFam : F = [] := by
            have hFam' : F = (auditCaseCNonIntegralityOf hC).family := by
              exact congrArg (fun X => X.family) hAgree
            rw [auditCaseCNonIntegrality_family_nil] at hFam'
            exact hFam'
          cases hFam
          cases hAgree
          exact HEq.rfl

theorem AuditCaseCKmaxGapReconstruction.gapValue_pos
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 <
      Lehmer.CaseC.GapClosure.kmaxGapPositiveValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_delta_positive
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap

theorem AuditCaseCKmaxGapReconstruction.kmaxValue_pos
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 <
      Lehmer.CaseC.GapClosure.kmaxGapKmaxValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_kmax_positive
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap

theorem AuditCaseCKmaxGapReconstruction.closureCapValue_pos
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 <
      Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_closureCap_positive
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap

theorem AuditCaseCKmaxGapReconstruction.closureCapValue_atLeastCap
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.CaseC.cap (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) ≤
      Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_closureCap_atLeastCap
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap

theorem AuditCaseCKmaxGapReconstruction.closureCapValue_atLeastClosureN
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCClosureDataOf hC).N ≤
      Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_closureCap_atLeastClosureN
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap

theorem AuditCaseCKmaxGapReconstruction.kmaxControlled
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.CaseC.GapClosure.kmaxGapKmaxValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      R.kmaxGap
      ≤
      (Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap : ℚ) *
      Lehmer.CaseC.GapClosure.kmaxGapPositiveValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_kmaxControlled
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap

theorem AuditCaseCKmaxGapReconstruction.mem_hasWitness
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    ∀ S,
      S ∈ R.kmaxGap.family →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_hasWitness
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap
    S hS

def AuditCaseCKmaxGapReconstruction.mem_rigid
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (R : AuditCaseCKmaxGapReconstruction hC) :
    ∀ S,
      S ∈ R.kmaxGap.family →
      Lehmer.CaseC.GapClosure.RigidProfile
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_rigid
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap
    S hS

def auditCaseCKmaxGapDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    AuditCaseCKmaxGapData n :=
  AuditCaseCKmaxGapData.mk hC
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCNonIntegralityOf hC)
    R.kmaxGap

@[simp] theorem auditCaseCKmaxGapDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).inCaseC = hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_params
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).params = auditCaseCParamsOf hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_closure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).closure = auditCaseCClosureDataOf hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_nonIntegrality
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).nonIntegrality = auditCaseCNonIntegralityOf hC := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_kmaxGap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).kmaxGap = R.kmaxGap := rfl

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
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℚ :=
  Lehmer.CaseC.GapClosure.kmaxGapPositiveValue X.params X.closure X.kmaxGap

@[simp] theorem AuditCaseCKmaxGapData.gapValue_def
    {n : ℕ} (X : AuditCaseCKmaxGapData n) :
    X.gapValue =
      Lehmer.CaseC.GapClosure.kmaxGapPositiveValue X.params X.closure X.kmaxGap := rfl

def AuditCaseCKmaxGapData.kmaxValue
    {n : ℕ} (X : AuditCaseCKmaxGapData n) : ℚ :=
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

theorem auditCaseCKmaxGap_family_eq_main
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    R.kmaxGap.family =
      Lehmer.CaseC.GapClosure.kmaxGapFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := by
  rfl

theorem auditCaseCKmaxGap_gapValue_eq_main
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.CaseC.GapClosure.kmaxGapPositiveValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      R.kmaxGap =
      (auditCaseCKmaxGapDataOf hC R).gapValue := by
  rfl

theorem auditCaseCKmaxGap_kmaxValue_eq_main
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.CaseC.GapClosure.kmaxGapKmaxValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      R.kmaxGap =
      (auditCaseCKmaxGapDataOf hC R).kmaxValue := by
  rfl

theorem auditCaseCKmaxGap_closureCapValue_eq_main
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      R.kmaxGap =
      (auditCaseCKmaxGapDataOf hC R).closureCapValue := by
  rfl

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
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).level = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_width
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).width = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_cap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).cap = Lehmer.Pipeline.pivotOf n := rfl

@[simp] theorem auditCaseCKmaxGapDataOf_omegaBound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).omegaBound = Lehmer.Pipeline.pivotOf n := rfl

theorem AuditCaseCKmaxGapData.level_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.Pipeline.YA ≤ (auditCaseCKmaxGapDataOf hC R).level := by
  simpa using hC.1

theorem AuditCaseCKmaxGapData.width_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.Pipeline.YA ≤ (auditCaseCKmaxGapDataOf hC R).width := by
  simpa using hC.1

theorem AuditCaseCKmaxGapData.cap_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.Pipeline.YA ≤ (auditCaseCKmaxGapDataOf hC R).cap := by
  simpa using hC.1

theorem AuditCaseCKmaxGapData.omegaBound_ge_YA
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Lehmer.Pipeline.YA ≤ (auditCaseCKmaxGapDataOf hC R).omegaBound := by
  simpa using hC.1

theorem AuditCaseCKmaxGapData.level_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).level < Lehmer.Pipeline.YC := by
  simpa using hC.2

theorem AuditCaseCKmaxGapData.width_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).width < Lehmer.Pipeline.YC := by
  simpa using hC.2

theorem AuditCaseCKmaxGapData.cap_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).cap < Lehmer.Pipeline.YC := by
  simpa using hC.2

theorem AuditCaseCKmaxGapData.omegaBound_lt_YC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (auditCaseCKmaxGapDataOf hC R).omegaBound < Lehmer.Pipeline.YC := by
  simpa using hC.2

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
    (R : CaseCKmaxGapAuditRouting P D) : ℚ :=
  Lehmer.CaseC.GapClosure.kmaxGapPositiveValue P D R.package

@[simp] theorem CaseCKmaxGapAuditRouting.gapValue_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    R.gapValue = Lehmer.CaseC.GapClosure.kmaxGapPositiveValue P D R.package := rfl

def CaseCKmaxGapAuditRouting.kmaxValue
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) : ℚ :=
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
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    CaseCKmaxGapAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  caseCKmaxGapAuditRouting_of_package
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    R.kmaxGap

@[simp] theorem caseCKmaxGapAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (caseCKmaxGapAuditRouting_of_inCaseC hC R).package = R.kmaxGap := rfl

@[simp] theorem caseCKmaxGapAuditRouting_of_inCaseC_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    (caseCKmaxGapAuditRouting_of_inCaseC hC R).family =
      Lehmer.CaseC.GapClosure.kmaxGapFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R.kmaxGap := rfl

theorem caseCKmaxGapAuditRouting_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    ∃ _X : Lehmer.CaseC.GapClosure.KmaxGapPackage P D, True := by
  exact ⟨R.package, trivial⟩

theorem exists_caseCKmaxGapAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    ∃ _T : CaseCKmaxGapAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC), True := by
  exact ⟨caseCKmaxGapAuditRouting_of_inCaseC hC R, trivial⟩

theorem CaseCKmaxGapAuditRouting.gapValue_pos
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    0 < R.gapValue := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_delta_positive P D R.package

theorem CaseCKmaxGapAuditRouting.kmaxValue_pos
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    0 < R.kmaxValue := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_kmax_positive P D R.package

theorem CaseCKmaxGapAuditRouting.closureCapValue_pos
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    0 < R.closureCapValue := by
  exact Lehmer.CaseC.GapClosure.kmaxGap_closureCap_positive P D R.package

theorem CaseCKmaxGapAuditRouting.mem_hasWitness
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    ∀ S,
      S ∈ R.family →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness P D S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_hasWitness P D R.package S hS

def CaseCKmaxGapAuditRouting.mem_rigid
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (R : CaseCKmaxGapAuditRouting P D) :
    ∀ S,
      S ∈ R.family →
      Lehmer.CaseC.GapClosure.RigidProfile P D S := by
  intro S hS
  exact Lehmer.CaseC.GapClosure.kmaxGapFamily_mem_rigid P D R.package S hS

theorem caseCKmaxGapAuditRouting_of_inCaseC_gapValue_pos
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 < (caseCKmaxGapAuditRouting_of_inCaseC hC R).gapValue := by
  exact CaseCKmaxGapAuditRouting.gapValue_pos
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

theorem caseCKmaxGapAuditRouting_of_inCaseC_kmaxValue_pos
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 < (caseCKmaxGapAuditRouting_of_inCaseC hC R).kmaxValue := by
  exact CaseCKmaxGapAuditRouting.kmaxValue_pos
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

theorem caseCKmaxGapAuditRouting_of_inCaseC_closureCapValue_pos
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 < (caseCKmaxGapAuditRouting_of_inCaseC hC R).closureCapValue := by
  exact CaseCKmaxGapAuditRouting.closureCapValue_pos
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

theorem caseCKmaxGapAuditRouting_of_inCaseC_mem_hasWitness
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    ∀ S,
      S ∈ (caseCKmaxGapAuditRouting_of_inCaseC hC R).family →
      Lehmer.CaseC.GapClosure.hasNonIntegralityWitness
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  exact CaseCKmaxGapAuditRouting.mem_hasWitness
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

def caseCKmaxGapAuditRouting_of_inCaseC_mem_rigid
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    ∀ S,
      S ∈ (caseCKmaxGapAuditRouting_of_inCaseC hC R).family →
      Lehmer.CaseC.GapClosure.RigidProfile
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        S := by
  exact CaseCKmaxGapAuditRouting.mem_rigid
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

def CaseCKmaxGapAuditReconstructible
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty (AuditCaseCKmaxGapReconstruction hC)

@[simp] theorem CaseCKmaxGapAuditReconstructible_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    CaseCKmaxGapAuditReconstructible hC =
      Nonempty (AuditCaseCKmaxGapReconstruction hC) := rfl

theorem caseCKmaxGapAuditReconstructible_of
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    CaseCKmaxGapAuditReconstructible hC := by
  exact ⟨R⟩

end CaseC
end Audit
end Lehmer