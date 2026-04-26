-- FILE: Lean/Lehmer/CaseC/Certificate/Coverage.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def thm
- Lehmer.CaseC.Certificate.Record : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def RecordCoversSupport
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) : Prop :=
  recordCoversSupport r S

@[simp] theorem RecordCoversSupport_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) :
    RecordCoversSupport r S = recordCoversSupport r S := rfl

theorem record_covers_iff_mem_cylinder
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) :
    RecordCoversSupport r S ↔ S ∈ recordCylinder r := by
  rfl

theorem recordCoversSupport_iff_prefix
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) :
    RecordCoversSupport r S ↔ IsPrefixOf (recordPrefix r) S := by
  rfl

def RecordCoversState
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (U : State P) : Prop :=
  RecordCoversSupport r U.support

@[simp] theorem RecordCoversState_def
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (U : State P) :
    RecordCoversState P D r U =
      RecordCoversSupport r U.support := rfl

theorem recordCoversState_iff_support
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (U : State P) :
    RecordCoversState P D r U ↔
      RecordCoversSupport r U.support := Iff.rfl

theorem RecordCoversState_mk
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (S : Support) :
    RecordCoversState P D r (State.mk S) ↔
      RecordCoversSupport r S := Iff.rfl

def RecordChildrenCoverSupport
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) : Prop :=
  ChildPrefixesCoverSupport (recordChildren r) S

@[simp] theorem RecordChildrenCoverSupport_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) :
    RecordChildrenCoverSupport r S =
      ChildPrefixesCoverSupport (recordChildren r) S := rfl

theorem recordChildrenCoverSupport_iff
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) :
    RecordChildrenCoverSupport r S ↔
      ∃ p : Prefix,
        p ∈ recordChildren r ∧
        PrefixCoversSupport p S := by
  rfl

theorem recordChildrenCoverSupport_iff_cylinder
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (S : Support) :
    RecordChildrenCoverSupport r S ↔
      ∃ p : Prefix,
        p ∈ recordChildren r ∧
        S ∈ Cylinder p := by
  rfl

def RecordChildrenCoverState
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (U : State P) : Prop :=
  RecordChildrenCoverSupport r U.support

@[simp] theorem RecordChildrenCoverState_def
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (U : State P) :
    RecordChildrenCoverState P D r U =
      RecordChildrenCoverSupport r U.support := rfl

theorem RecordChildrenCoverState_mk
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (S : Support) :
    RecordChildrenCoverState P D r (State.mk S) ↔
      RecordChildrenCoverSupport r S := Iff.rfl

def FamilyCoversSupport
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) (S : Support) : Prop :=
  ∃ r : RecordData P D,
    r ∈ R ∧ RecordCoversSupport r S

@[simp] theorem FamilyCoversSupport_def
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) (S : Support) :
    FamilyCoversSupport P D R S =
      (∃ r : RecordData P D,
        r ∈ R ∧ RecordCoversSupport r S) := rfl

@[simp] theorem FamilyCoversSupport_nil
    (P : Params) (D : ClosureData P)
    (S : Support) :
    ¬ FamilyCoversSupport P D [] S := by
  intro h
  rcases h with ⟨r, hr, _⟩
  simp at hr

theorem FamilyCoversSupport_cons
    (P : Params) (D : ClosureData P)
    (r : RecordData P D)
    (rs : RecordFamily P D)
    (S : Support) :
    FamilyCoversSupport P D (r :: rs) S ↔
      RecordCoversSupport r S ∨
      FamilyCoversSupport P D rs S := by
  constructor
  · intro h
    rcases h with ⟨r', hr', hcov⟩
    simp at hr'
    rcases hr' with rfl | hrs
    · exact Or.inl hcov
    · exact Or.inr ⟨r', hrs, hcov⟩
  · intro h
    rcases h with h | h
    · exact ⟨r, by simp, h⟩
    · rcases h with ⟨r', hr', hcov⟩
      exact ⟨r', by simp [hr'], hcov⟩

def FamilyCoversState
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) (U : State P) : Prop :=
  FamilyCoversSupport P D R U.support

@[simp] theorem FamilyCoversState_def
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) (U : State P) :
    FamilyCoversState P D R U =
      FamilyCoversSupport P D R U.support := rfl

theorem FamilyCoversState_mk
    (P : Params) (D : ClosureData P)
    (R : RecordFamily P D) (S : Support) :
    FamilyCoversState P D R (State.mk S) ↔
      FamilyCoversSupport P D R S := Iff.rfl

def GlobalCertificateCoversSupport
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support) : Prop :=
  CertificateCoversSupport P D C.records S

@[simp] theorem GlobalCertificateCoversSupport_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support) :
    GlobalCertificateCoversSupport P D C S =
      CertificateCoversSupport P D C.records S := rfl

theorem globalCertificateCoversSupport_iff_family
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support) :
    GlobalCertificateCoversSupport P D C S ↔
      FamilyCoversSupport P D (certificateRecords C) S := by
  constructor
  · intro h
    rcases h with ⟨r, hr, hCov⟩
    exact ⟨r, hr, hCov⟩
  · intro h
    rcases h with ⟨r, hr, hCov⟩
    exact ⟨r, hr, hCov⟩

theorem GlobalCertificateCoversSupport_of_hasRecord
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (r : RecordData P D)
    (S : Support) :
    certificateHasRecord C r →
    RecordCoversSupport r S →
    GlobalCertificateCoversSupport P D C S := by
  intro hr hcov
  exact ⟨r, hr, hcov⟩

def GlobalCertificateCoversState
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (U : State P) : Prop :=
  GlobalCertificateCoversSupport P D C U.support

@[simp] theorem GlobalCertificateCoversState_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (U : State P) :
    GlobalCertificateCoversState P D C U =
      GlobalCertificateCoversSupport P D C U.support := rfl

theorem globalCertificateCoversState_iff_support
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (U : State P) :
    GlobalCertificateCoversState P D C U ↔
      GlobalCertificateCoversSupport P D C U.support := Iff.rfl

theorem GlobalCertificateCoversState_of_hasRecord
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (r : RecordData P D)
    (U : State P) :
    certificateHasRecord C r →
    RecordCoversState P D r U →
    GlobalCertificateCoversState P D C U := by
  intro hr hcov
  exact ⟨r, hr, hcov⟩

theorem GlobalCertificateCoversState_mk
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support) :
    GlobalCertificateCoversState P D C (State.mk S) ↔
      GlobalCertificateCoversSupport P D C S := Iff.rfl

theorem globalCertificate_covers_admissible_support
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    GlobalCertificateCoversSupport P D C S := by
  exact C.coversDomain S hAdm

theorem globalCertificate_has_record_covering_admissible_support
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    ∃ r : RecordData P D,
      certificateHasRecord C r ∧
      RecordCoversSupport r S := by
  exact globalCertificate_covers_record C S hAdm

theorem globalCertificate_covers_admissible_state
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    GlobalCertificateCoversState P D C U := by
  exact C.coversDomain U.support hAdm

theorem globalCertificate_has_record_covering_admissible_state
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    ∃ r : RecordData P D,
      certificateHasRecord C r ∧
      RecordCoversState P D r U := by
  rcases C.coversDomain U.support hAdm with ⟨r, hr, hCov⟩
  exact ⟨r, hr, hCov⟩

theorem rootPrefix_covers_admissible_support
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    PrefixCoversSupport (RootPrefix P) S := by
  exact C.rootCovers S hAdm

theorem rootPrefix_covers_admissible_state
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    PrefixCoversSupport (RootPrefix P) U.support := by
  exact C.rootCovers U.support hAdm

theorem finiteReductionRecord_children_cover_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    {d : FiniteReductionData P D r.pref}
    (hRoute : recordRouting r = RecordRouting.finiteReduction r d)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    RecordChildrenCoverSupport r S := by
  have hChild :
      ChildPrefixesCoverSupport d.children S :=
    recordRouting_finiteReduction_routes_support hRoute S hAdm hCov
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness e =>
          simp [recordRouting] at hRoute
      | exclusion e =>
          simp [recordRouting] at hRoute
      | finiteReduction fd =>
          simp [recordRouting] at hRoute
          cases hRoute
          simpa [RecordChildrenCoverSupport, recordChildren] using hChild

theorem finiteReductionRecord_children_cover_state
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    {d : FiniteReductionData P D r.pref}
    (hRoute : recordRouting r = RecordRouting.finiteReduction r d)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support)
    (hCov : RecordCoversState P D r U) :
    RecordChildrenCoverState P D r U := by
  exact finiteReductionRecord_children_cover_support
    hRoute U.support hAdm hCov

end Certificate
end CaseC
end Lehmer