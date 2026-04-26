-- FILE: Lean/Lehmer/Audit/CaseC/GapClosure.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.GapClosure.SupportProfiles : def thm
- Lehmer.CaseC.GapClosure.Rigidity : def thm
- Lehmer.CaseC.GapClosure.NonIntegrality : def thm
- Lehmer.CaseC.GapClosure.KmaxGap : def thm
- Lehmer.CaseC.GapClosure.GapToClosure : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
- Lehmer.Audit.CaseC.Params : def thm
- Lehmer.Audit.CaseC.ClosureData : def thm
- Lehmer.Audit.CaseC.NonIntegrality : def thm
- Lehmer.Audit.CaseC.KmaxGap : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.GapClosure.SupportProfiles
import Lehmer.CaseC.GapClosure.Rigidity
import Lehmer.CaseC.GapClosure.NonIntegrality
import Lehmer.CaseC.GapClosure.KmaxGap
import Lehmer.CaseC.GapClosure.GapToClosure
import Lehmer.Pipeline.GlobalSplit
import Lehmer.Audit.CaseC.Params
import Lehmer.Audit.CaseC.ClosureData
import Lehmer.Audit.CaseC.NonIntegrality
import Lehmer.Audit.CaseC.KmaxGap

namespace Lehmer
namespace Audit
namespace CaseC

open Lehmer.CaseC
open Lehmer.CaseC.GapClosure

def AuditCaseCGapClosureUnavailable : Prop :=
  True

@[simp] theorem AuditCaseCGapClosureUnavailable_def :
    AuditCaseCGapClosureUnavailable = True := rfl

theorem auditCaseCGapClosureUnavailable :
    AuditCaseCGapClosureUnavailable := by
  trivial

namespace GapClosureLocal

theorem isTruncatedFamily_nil
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) :
    Lehmer.CaseC.GapClosure.IsTruncatedFamily P D [] := by
  intro R hR
  cases hR

theorem rigidProfileFamily_nil
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) :
    Lehmer.CaseC.GapClosure.RigidProfileFamily P D [] := by
  intro R hR
  cases hR

end GapClosureLocal

def auditCaseCTruncatedGapPackageOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.TruncatedGapPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.GapClosure.TruncatedGapPackage.mk
    []
    (GapClosureLocal.isTruncatedFamily_nil
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))
    (GapClosureLocal.rigidProfileFamily_nil
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))
    (Lehmer.CaseC.GapClosure.DeltaStarData.mk
      1
      (by decide))
    (Lehmer.CaseC.GapClosure.OmegahatData.mk
      1)

@[simp] theorem auditCaseCTruncatedGapPackageOf_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCTruncatedGapPackageOf hC).family = [] := rfl

theorem auditCaseCBootstrapConditionOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.BootstrapCondition
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCTruncatedGapPackageOf hC) := by
  rfl

def auditCaseCBootstrapPackageOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.BootstrapPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.GapClosure.BootstrapPackage.mk
    (auditCaseCTruncatedGapPackageOf hC)
    (auditCaseCBootstrapConditionOf hC)

@[simp] theorem auditCaseCBootstrapPackageOf_data
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCBootstrapPackageOf hC).data =
      auditCaseCTruncatedGapPackageOf hC := rfl

def auditCaseCClosureBoundDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.ClosureBoundData
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.GapClosure.ClosureBoundData.mk
    (Lehmer.Pipeline.pivotOf n)

@[simp] theorem auditCaseCClosureBoundDataOf_value
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.closureBoundValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCClosureBoundDataOf hC) =
        Lehmer.Pipeline.pivotOf n := rfl

theorem auditCaseCClosureBoundAtLeastCapOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.ClosureBoundAtLeastCap
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCClosureBoundDataOf hC) := by
  rfl

def auditCaseCBootstrapClosureBoundOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.BootstrapClosureBoundPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.GapClosure.BootstrapClosureBoundPackage.mk
    (auditCaseCBootstrapPackageOf hC)
    (auditCaseCClosureBoundDataOf hC)

@[simp] theorem auditCaseCBootstrapClosureBoundOf_data
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCBootstrapClosureBoundOf hC).data =
      auditCaseCBootstrapPackageOf hC := rfl

@[simp] theorem auditCaseCBootstrapClosureBoundOf_bound
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCBootstrapClosureBoundOf hC).bound =
      auditCaseCClosureBoundDataOf hC := rfl

theorem auditCaseCBootstrapClosureBoundAtLeastCapOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.bootstrapClosureBoundAtLeastCap
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCBootstrapClosureBoundOf hC) := by
  rfl

def auditCaseCGapClosureOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.GapClosurePackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.GapClosure.gapClosureFromBootstrapBound
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCBootstrapClosureBoundOf hC)

@[simp] theorem auditCaseCGapClosureOf_data
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCGapClosureOf hC).data =
      auditCaseCBootstrapClosureBoundOf hC := rfl

def auditCaseCGapToClosureOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.GapToClosurePackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  Lehmer.CaseC.GapClosure.GapToClosurePackage.mk
    (auditCaseCKmaxGapOf hC)
    (auditCaseCBootstrapClosureBoundOf hC)

@[simp] theorem auditCaseCGapToClosureOf_kmaxGap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCGapToClosureOf hC).kmaxGap =
      auditCaseCKmaxGapOf hC := rfl

@[simp] theorem auditCaseCGapToClosureOf_bootstrap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCGapToClosureOf hC).bootstrap =
      auditCaseCBootstrapClosureBoundOf hC := rfl

@[simp] theorem auditCaseCGapToClosureOf_gap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    (auditCaseCGapToClosureOf hC).gap =
      auditCaseCGapClosureOf hC := rfl

theorem auditCaseCGapClosure_member_truncated
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∀ R,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC) →
      Lehmer.CaseC.GapClosure.ProfileInTruncatedFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapClosurePackage.member_truncated
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCGapClosureOf hC)
    R
    hR

theorem auditCaseCGapClosure_member_rigid
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    ∀ R,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC) →
      Lehmer.CaseC.GapClosure.RigidProfile
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapClosurePackage.member_rigid
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCGapClosureOf hC)
    R
    hR

theorem auditCaseCGapClosure_bootstrap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.BootstrapCondition
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCGapClosureOf hC).data.data.data := by
  exact Lehmer.CaseC.GapClosure.GapClosurePackage.bootstrap_holds
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCGapClosureOf hC)

theorem auditCaseCGapClosure_omegahat
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    Lehmer.CaseC.GapClosure.OmegahatBelowWidth
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCGapClosureOf hC).data.data.data.omegaHat := by
  exact Lehmer.CaseC.GapClosure.GapClosurePackage.omegahat_below_width
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCGapClosureOf hC)

def AuditCaseCGapClosureAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty
    (Lehmer.CaseC.GapClosure.GapToClosurePackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

theorem auditCaseCGapClosureAvailable
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCGapClosureAvailable hC := by
  exact ⟨auditCaseCGapToClosureOf hC⟩

end CaseC
end Audit
end Lehmer