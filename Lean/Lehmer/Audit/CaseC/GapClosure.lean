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
open Lehmer.Basic

structure AuditCaseCGapClosureReconstruction
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) where
  kmaxReconstruction :
    AuditCaseCKmaxGapReconstruction hC
  gapToClosure :
    Lehmer.CaseC.GapClosure.GapToClosurePackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
  kmaxGap_agrees :
    gapToClosure.kmaxGap =
      kmaxReconstruction.kmaxGap
  nonIntegrality_agrees :
    Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      gapToClosure.kmaxGap =
      auditCaseCNonIntegralityOf hC

@[simp] theorem AuditCaseCGapClosureReconstruction.kmaxReconstruction_mk
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (K : AuditCaseCKmaxGapReconstruction hC)
    (G :
      Lehmer.CaseC.GapClosure.GapToClosurePackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC))
    (hKG : G.kmaxGap = K.kmaxGap)
    (hNI :
      Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        G.kmaxGap =
        auditCaseCNonIntegralityOf hC) :
    (AuditCaseCGapClosureReconstruction.mk K G hKG hNI).kmaxReconstruction = K := rfl

@[simp] theorem AuditCaseCGapClosureReconstruction.gapToClosure_mk
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (K : AuditCaseCKmaxGapReconstruction hC)
    (G :
      Lehmer.CaseC.GapClosure.GapToClosurePackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC))
    (hKG : G.kmaxGap = K.kmaxGap)
    (hNI :
      Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        G.kmaxGap =
        auditCaseCNonIntegralityOf hC) :
    (AuditCaseCGapClosureReconstruction.mk K G hKG hNI).gapToClosure = G := rfl

@[simp] theorem AuditCaseCGapClosureReconstruction.kmaxGap_agrees_mk
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (K : AuditCaseCKmaxGapReconstruction hC)
    (G :
      Lehmer.CaseC.GapClosure.GapToClosurePackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC))
    (hKG : G.kmaxGap = K.kmaxGap)
    (hNI :
      Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        G.kmaxGap =
        auditCaseCNonIntegralityOf hC) :
    (AuditCaseCGapClosureReconstruction.mk K G hKG hNI).kmaxGap_agrees = hKG := rfl

@[simp] theorem AuditCaseCGapClosureReconstruction.nonIntegrality_agrees_mk
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (K : AuditCaseCKmaxGapReconstruction hC)
    (G :
      Lehmer.CaseC.GapClosure.GapToClosurePackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC))
    (hKG : G.kmaxGap = K.kmaxGap)
    (hNI :
      Lehmer.CaseC.GapClosure.KmaxGapPackage.nonIntegralityFamilyPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        G.kmaxGap =
        auditCaseCNonIntegralityOf hC) :
    (AuditCaseCGapClosureReconstruction.mk K G hKG hNI).nonIntegrality_agrees = hNI := rfl

theorem AuditCaseCGapClosureReconstruction.kmaxGap_eq_audit
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    X.gapToClosure.kmaxGap = X.kmaxReconstruction.kmaxGap :=
  X.kmaxGap_agrees

def auditCaseCGapClosureOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.GapClosure.GapClosurePackage
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  X.gapToClosure.gap
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)

@[simp] theorem auditCaseCGapClosureOf_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    auditCaseCGapClosureOf hC X =
      X.gapToClosure.gap
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) := rfl

@[simp] theorem auditCaseCGapClosureOf_data
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureOf hC X).data =
      X.gapToClosure.realizer.bootstrap := by
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_data
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

structure AuditCaseCGapClosureData (n : ℕ) where
  inCaseC : Lehmer.Pipeline.InCaseC n
  params : Lehmer.CaseC.Params
  closure : Lehmer.CaseC.ClosureData params
  nonIntegrality :
    Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage params closure
  kmaxGap :
    Lehmer.CaseC.GapClosure.KmaxGapPackage params closure
  gapToClosure :
    Lehmer.CaseC.GapClosure.GapToClosurePackage params closure

@[simp] theorem AuditCaseCGapClosureData.inCaseC_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (AuditCaseCGapClosureData.mk hC P D NI K G).inCaseC = hC := rfl

@[simp] theorem AuditCaseCGapClosureData.params_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (AuditCaseCGapClosureData.mk hC P D NI K G).params = P := rfl

@[simp] theorem AuditCaseCGapClosureData.closure_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (AuditCaseCGapClosureData.mk hC P D NI K G).closure = D := rfl

@[simp] theorem AuditCaseCGapClosureData.nonIntegrality_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (AuditCaseCGapClosureData.mk hC P D NI K G).nonIntegrality = NI := rfl

@[simp] theorem AuditCaseCGapClosureData.kmaxGap_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (AuditCaseCGapClosureData.mk hC P D NI K G).kmaxGap = K := rfl

@[simp] theorem AuditCaseCGapClosureData.gapToClosure_mk
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (P : Lehmer.CaseC.Params)
    (D : Lehmer.CaseC.ClosureData P)
    (NI : Lehmer.CaseC.GapClosure.NonIntegralityFamilyPackage P D)
    (K : Lehmer.CaseC.GapClosure.KmaxGapPackage P D)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (AuditCaseCGapClosureData.mk hC P D NI K G).gapToClosure = G := rfl

def auditCaseCGapClosureDataOf
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    AuditCaseCGapClosureData n :=
  AuditCaseCGapClosureData.mk hC
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    (auditCaseCNonIntegralityOf hC)
    X.kmaxReconstruction.kmaxGap
    X.gapToClosure

@[simp] theorem auditCaseCGapClosureDataOf_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureDataOf hC X).inCaseC = hC := rfl

@[simp] theorem auditCaseCGapClosureDataOf_params
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureDataOf hC X).params = auditCaseCParamsOf hC := rfl

@[simp] theorem auditCaseCGapClosureDataOf_closure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureDataOf hC X).closure = auditCaseCClosureDataOf hC := rfl

@[simp] theorem auditCaseCGapClosureDataOf_nonIntegrality
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureDataOf hC X).nonIntegrality =
      auditCaseCNonIntegralityOf hC := rfl

@[simp] theorem auditCaseCGapClosureDataOf_kmaxGap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureDataOf hC X).kmaxGap =
      X.kmaxReconstruction.kmaxGap := rfl

@[simp] theorem auditCaseCGapClosureDataOf_gapToClosure
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureDataOf hC X).gapToClosure = X.gapToClosure := rfl

theorem AuditCaseCGapClosureReconstruction.gap_family_eq_auditKmaxFamily
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.GapClosure.gapClosureFamily
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCGapClosureOf hC X) =
    Lehmer.CaseC.GapClosure.kmaxGapFamily
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.kmaxReconstruction.kmaxGap := by
  simpa [auditCaseCGapClosureOf, X.kmaxGap_agrees] using
    Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_family_eq_kmax_family
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_delta_eq_auditKmaxDelta
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.GapClosure.gapClosureDeltaValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCGapClosureOf hC X) =
    Lehmer.CaseC.GapClosure.kmaxGapPositiveValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.kmaxReconstruction.kmaxGap := by
  simpa [auditCaseCGapClosureOf, X.kmaxGap_agrees] using
    Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_delta_eq_kmax_delta
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_kmax_eq_auditKmaxValue
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.GapClosure.gapClosureKmaxValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCGapClosureOf hC X) =
    Lehmer.CaseC.GapClosure.kmaxGapKmaxValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.kmaxReconstruction.kmaxGap := by
  simpa [auditCaseCGapClosureOf, X.kmaxGap_agrees] using
    Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_kmax_eq_kmax_gap
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_bound_eq_auditClosureCap
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.GapClosure.gapClosureBoundValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCGapClosureOf hC X) =
    Lehmer.CaseC.GapClosure.kmaxGapClosureCapValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.kmaxReconstruction.kmaxGap := by
  simpa [auditCaseCGapClosureOf, X.kmaxGap_agrees] using
    Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_bound_eq_kmax_cap
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.kmax_controlled
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.GapClosure.kmaxGapKmaxValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.kmaxReconstruction.kmaxGap
      ≤
      (Lehmer.CaseC.GapClosure.gapClosureBoundValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) : ℚ) *
      Lehmer.CaseC.GapClosure.gapClosureDeltaValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) := by
  simpa [auditCaseCGapClosureOf, X.kmaxGap_agrees] using
    Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_kmax_controlled
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.gapToClosure

def AuditCaseCGapClosureReady
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) : Prop :=
  Lehmer.CaseC.GapClosure.GapToClosureReady
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

@[simp] theorem AuditCaseCGapClosureReady_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    AuditCaseCGapClosureReady hC X =
      Lehmer.CaseC.GapClosure.GapToClosureReady
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        X.gapToClosure := rfl

theorem auditCaseCGapClosureReady
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    AuditCaseCGapClosureReady hC X := by
  exact Lehmer.CaseC.GapClosure.gapToClosureReady
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

def AuditCaseCGapClosureData.ready
    {n : ℕ} (X : AuditCaseCGapClosureData n) : Prop :=
  Lehmer.CaseC.GapClosure.GapToClosureReady X.params X.closure X.gapToClosure

@[simp] theorem AuditCaseCGapClosureData.ready_def
    {n : ℕ} (X : AuditCaseCGapClosureData n) :
    X.ready =
      Lehmer.CaseC.GapClosure.GapToClosureReady X.params X.closure X.gapToClosure := rfl

theorem auditCaseCGapClosureDataOf_ready
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCGapClosureDataOf hC X).ready := by
  exact Lehmer.CaseC.GapClosure.gapToClosureReady
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_member_preAdmissible
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X) →
      Lehmer.CaseC.Certificate.PreCaseCAdmissibleSupport
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (Lehmer.CaseC.GapClosure.profileSupport R) := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_member_preAdmissible
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure
    R hR

theorem AuditCaseCGapClosureReconstruction.gap_member_admissibleAtLevel
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X) →
      Lehmer.CaseC.Certificate.AdmissibleSupportAtLevel
        (Lehmer.CaseC.level (auditCaseCParamsOf hC))
        (Lehmer.CaseC.GapClosure.profileSupport R) := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_member_admissibleAtLevel
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure
    R hR

theorem AuditCaseCGapClosureReconstruction.gap_member_locksB
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X) →
      Lehmer.CaseC.Certificate.LocksB
        (Lehmer.CaseC.level (auditCaseCParamsOf hC))
        (Lehmer.CaseC.GapClosure.profileSupport R) := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_member_locksB
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure
    R hR

theorem AuditCaseCGapClosureReconstruction.gap_member_truncated
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X) →
      Lehmer.CaseC.GapClosure.ProfileInTruncatedFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_member_truncated
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure
    R hR

def AuditCaseCGapClosureReconstruction.gap_member_rigid
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X) →
      Lehmer.CaseC.GapClosure.RigidProfile
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        R := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_member_rigid
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure
    R hR

theorem AuditCaseCGapClosureReconstruction.gap_member_index_le_kmax
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X) →
      Lehmer.CaseC.GapClosure.profileSupportIndex R ≤
        Lehmer.CaseC.GapClosure.gapClosureKmaxValue
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC)
          (auditCaseCGapClosureOf hC X) := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_member_index_le_kmax
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure
    R hR

theorem AuditCaseCGapClosureReconstruction.gap_delta_le_member_gap
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      ∀ hR : R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X),
        Lehmer.CaseC.GapClosure.gapClosureDeltaValue
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC)
          (auditCaseCGapClosureOf hC X) ≤
          Lehmer.CaseC.GapClosure.profileRigidityGapValue
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            R
            ((Lehmer.CaseC.GapClosure.GapClosurePackage.member_rigid
              (auditCaseCParamsOf hC)
              (auditCaseCClosureDataOf hC)
              (auditCaseCGapClosureOf hC X)) R hR) := by
  intro R hR
  simpa [auditCaseCGapClosureOf] using
    (Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_delta_le_member_gap
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      X.gapToClosure
      R hR)

theorem AuditCaseCGapClosureReconstruction.gap_delta_positive
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    0 <
      Lehmer.CaseC.GapClosure.gapClosureDeltaValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) := by
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_delta_positive
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_kmax_positive
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    0 <
      Lehmer.CaseC.GapClosure.gapClosureKmaxValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) := by
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_kmax_positive
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_bound_positive
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    0 <
      Lehmer.CaseC.GapClosure.gapClosureBoundValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) := by
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_bound_positive
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_bound_atLeastCap
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.cap (auditCaseCParamsOf hC) (auditCaseCClosureDataOf hC) ≤
      Lehmer.CaseC.GapClosure.gapClosureBoundValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) := by
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_bound_atLeastCap
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_bound_atLeastClosureN
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    (auditCaseCClosureDataOf hC).N ≤
      Lehmer.CaseC.GapClosure.gapClosureBoundValue
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) := by
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_bound_atLeastClosureN
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_omegahat_lt_width
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC) :
    Lehmer.CaseC.GapClosure.gapClosureOmegahatValue
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      (auditCaseCGapClosureOf hC X) <
      Lehmer.CaseC.width (auditCaseCParamsOf hC) := by
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_omegahat_lt_width
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

theorem AuditCaseCGapClosureReconstruction.gap_member_within_closure_omega
    {n : ℕ} {hC : Lehmer.Pipeline.InCaseC n}
    (X : AuditCaseCGapClosureReconstruction hC)
    (hMatch :
      Lehmer.CaseC.GapClosure.truncatedGapOmegahatMatchesClosureData
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X).data.data.data) :
    ∀ R : Lehmer.CaseC.GapClosure.SupportProfile,
      R ∈ Lehmer.CaseC.GapClosure.gapClosureFamily
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)
            (auditCaseCGapClosureOf hC X) →
      Lehmer.CaseC.SupportWithinOmega
        (auditCaseCClosureDataOf hC).omegaHat
        (Lehmer.CaseC.GapClosure.profileSupport R) := by
  intro R hR
  exact Lehmer.CaseC.GapClosure.GapToClosurePackage.gap_member_within_closure_omega
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure
    hMatch
    R hR

def AuditCaseCGapClosureReconstructible
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) : Prop :=
  Nonempty (AuditCaseCGapClosureReconstruction hC)

@[simp] theorem AuditCaseCGapClosureReconstructible_def
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n) :
    AuditCaseCGapClosureReconstructible hC =
      Nonempty (AuditCaseCGapClosureReconstruction hC) := rfl

theorem auditCaseCGapClosureReconstructible_of
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    AuditCaseCGapClosureReconstructible hC := by
  exact ⟨X⟩

structure CaseCGapClosureAuditRouting
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  package : Lehmer.CaseC.GapClosure.GapToClosurePackage P D

@[simp] theorem CaseCGapClosureAuditRouting.package_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (CaseCGapClosureAuditRouting.mk G).package = G := rfl

def CaseCGapClosureAuditRouting.gap
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    Lehmer.CaseC.GapClosure.GapClosurePackage P D :=
  X.package.gap P D

@[simp] theorem CaseCGapClosureAuditRouting.gap_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    X.gap P D = X.package.gap P D := rfl

def CaseCGapClosureAuditRouting.family
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    Lehmer.CaseC.GapClosure.SupportProfileFamily :=
  Lehmer.CaseC.GapClosure.gapClosureFamily P D (X.gap P D)

@[simp] theorem CaseCGapClosureAuditRouting.family_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    X.family P D =
      Lehmer.CaseC.GapClosure.gapClosureFamily P D (X.gap P D) := rfl

def CaseCGapClosureAuditRouting.gapValue
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) : ℚ :=
  Lehmer.CaseC.GapClosure.gapClosureDeltaValue P D (X.gap P D)

@[simp] theorem CaseCGapClosureAuditRouting.gapValue_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    X.gapValue P D =
      Lehmer.CaseC.GapClosure.gapClosureDeltaValue P D (X.gap P D) := rfl

def CaseCGapClosureAuditRouting.kmaxValue
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) : ℚ :=
  Lehmer.CaseC.GapClosure.gapClosureKmaxValue P D (X.gap P D)

@[simp] theorem CaseCGapClosureAuditRouting.kmaxValue_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    X.kmaxValue P D =
      Lehmer.CaseC.GapClosure.gapClosureKmaxValue P D (X.gap P D) := rfl

def CaseCGapClosureAuditRouting.boundValue
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) : ℕ :=
  Lehmer.CaseC.GapClosure.gapClosureBoundValue P D (X.gap P D)

@[simp] theorem CaseCGapClosureAuditRouting.boundValue_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    X.boundValue P D =
      Lehmer.CaseC.GapClosure.gapClosureBoundValue P D (X.gap P D) := rfl

def caseCGapClosureAuditRouting_of_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    CaseCGapClosureAuditRouting P D :=
  CaseCGapClosureAuditRouting.mk G

@[simp] theorem caseCGapClosureAuditRouting_of_package_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D) :
    (caseCGapClosureAuditRouting_of_package P D G).package = G := rfl

def caseCGapClosureAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    CaseCGapClosureAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) :=
  caseCGapClosureAuditRouting_of_package
    (auditCaseCParamsOf hC)
    (auditCaseCClosureDataOf hC)
    X.gapToClosure

@[simp] theorem caseCGapClosureAuditRouting_of_inCaseC_package
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (caseCGapClosureAuditRouting_of_inCaseC hC X).package = X.gapToClosure := rfl

@[simp] theorem caseCGapClosureAuditRouting_of_inCaseC_gap
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (caseCGapClosureAuditRouting_of_inCaseC hC X).gap
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) =
      auditCaseCGapClosureOf hC X := rfl

@[simp] theorem caseCGapClosureAuditRouting_of_inCaseC_family
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    (caseCGapClosureAuditRouting_of_inCaseC hC X).family
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC) =
      Lehmer.CaseC.GapClosure.gapClosureFamily
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)
        (auditCaseCGapClosureOf hC X) := rfl

theorem caseCGapClosureAuditRouting_sound
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    ∃ _G : Lehmer.CaseC.GapClosure.GapToClosurePackage P D, True := by
  exact ⟨X.package, trivial⟩

theorem exists_caseCGapClosureAuditRouting_of_inCaseC
    {n : ℕ} (hC : Lehmer.Pipeline.InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    ∃ _R : CaseCGapClosureAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC), True := by
  exact ⟨caseCGapClosureAuditRouting_of_inCaseC hC X, trivial⟩

end CaseC
end Audit
end Lehmer