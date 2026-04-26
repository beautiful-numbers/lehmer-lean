-- FILE: Lean/Lehmer/CaseC/Certificate/Record.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def IsEmptinessRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  recordKind r = LocalClosureKind.emptiness

def IsExclusionRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  recordKind r = LocalClosureKind.exclusion

def IsFiniteReductionRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  recordKind r = LocalClosureKind.finiteReduction

@[simp] theorem IsEmptinessRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsEmptinessRecord r = (recordKind r = LocalClosureKind.emptiness) := rfl

@[simp] theorem IsExclusionRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsExclusionRecord r = (recordKind r = LocalClosureKind.exclusion) := rfl

@[simp] theorem IsFiniteReductionRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsFiniteReductionRecord r = (recordKind r = LocalClosureKind.finiteReduction) := rfl

def recordPrefix
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prefix :=
  r.pref

@[simp] theorem recordPrefix_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    recordPrefix r = r.pref := rfl

def recordSupport
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Support :=
  r.pref.support

@[simp] theorem recordSupport_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    recordSupport r = r.pref.support := rfl

def recordClosure
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : LocalClosureData P D r.pref :=
  r.closure

@[simp] theorem recordClosure_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    recordClosure r = r.closure := rfl

def recordHasChild
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (p : Prefix) : Prop :=
  p ∈ recordChildren r

@[simp] theorem recordHasChild_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (p : Prefix) :
    recordHasChild r p = (p ∈ recordChildren r) := rfl

def certificateHasRecord
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D) (r : RecordData P D) : Prop :=
  r ∈ certificateRecords C

@[simp] theorem certificateHasRecord_def
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D) (r : RecordData P D) :
    certificateHasRecord C r = (r ∈ certificateRecords C) := rfl

def recordEmptinessData?
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  ∃ d : EmptinessData P D r.pref,
    r.closure = LocalClosureData.emptiness d

def recordExclusionData?
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  ∃ d : ExclusionData P D r.pref,
    r.closure = LocalClosureData.exclusion d

def recordFiniteReductionData?
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  ∃ d : FiniteReductionData P D r.pref,
    r.closure = LocalClosureData.finiteReduction d

theorem isEmptinessRecord_iff_exists_data
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsEmptinessRecord r ↔ recordEmptinessData? r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          constructor
          · intro _
            exact ⟨d, rfl⟩
          · intro _
            rfl
      | exclusion d =>
          constructor
          · intro h
            cases h
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
      | finiteReduction d =>
          constructor
          · intro h
            cases h
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'

theorem isExclusionRecord_iff_exists_data
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsExclusionRecord r ↔ recordExclusionData? r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          constructor
          · intro h
            cases h
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
      | exclusion d =>
          constructor
          · intro _
            exact ⟨d, rfl⟩
          · intro _
            rfl
      | finiteReduction d =>
          constructor
          · intro h
            cases h
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'

theorem isFiniteReductionRecord_iff_exists_data
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsFiniteReductionRecord r ↔ recordFiniteReductionData? r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          constructor
          · intro h
            cases h
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
      | exclusion d =>
          constructor
          · intro h
            cases h
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
      | finiteReduction d =>
          constructor
          · intro _
            exact ⟨d, rfl⟩
          · intro _
            rfl

theorem IsEmptinessRecord.not_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsEmptinessRecord r → ¬ IsExclusionRecord r := by
  intro hE hX
  have h : LocalClosureKind.emptiness = LocalClosureKind.exclusion := by
    calc
      LocalClosureKind.emptiness = recordKind r := hE.symm
      _ = LocalClosureKind.exclusion := hX
  exact localClosureKind_emptiness_ne_exclusion h

theorem IsEmptinessRecord.not_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsEmptinessRecord r → ¬ IsFiniteReductionRecord r := by
  intro hE hF
  have h : LocalClosureKind.emptiness = LocalClosureKind.finiteReduction := by
    calc
      LocalClosureKind.emptiness = recordKind r := hE.symm
      _ = LocalClosureKind.finiteReduction := hF
  exact localClosureKind_emptiness_ne_finiteReduction h

theorem IsExclusionRecord.not_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsExclusionRecord r → ¬ IsEmptinessRecord r := by
  intro hX hE
  exact (IsEmptinessRecord.not_exclusion r hE) hX

theorem IsExclusionRecord.not_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsExclusionRecord r → ¬ IsFiniteReductionRecord r := by
  intro hX hF
  have h : LocalClosureKind.exclusion = LocalClosureKind.finiteReduction := by
    calc
      LocalClosureKind.exclusion = recordKind r := hX.symm
      _ = LocalClosureKind.finiteReduction := hF
  exact localClosureKind_exclusion_ne_finiteReduction h

theorem IsFiniteReductionRecord.not_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsFiniteReductionRecord r → ¬ IsEmptinessRecord r := by
  intro hF hE
  exact (IsEmptinessRecord.not_finiteReduction r hE) hF

theorem IsFiniteReductionRecord.not_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsFiniteReductionRecord r → ¬ IsExclusionRecord r := by
  intro hF hX
  exact (IsExclusionRecord.not_finiteReduction r hX) hF

theorem record_exhaustive
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    IsEmptinessRecord r ∨
    IsExclusionRecord r ∨
    IsFiniteReductionRecord r := by
  cases h : recordKind r with
  | emptiness =>
      left
      exact h
  | exclusion =>
      right
      left
      exact h
  | finiteReduction =>
      right
      right
      exact h

inductive RecordRouting
    (P : Params) (D : ClosureData P) : Type where
  | emptiness (r : RecordData P D) (d : EmptinessData P D r.pref)
  | exclusion (r : RecordData P D) (d : ExclusionData P D r.pref)
  | finiteReduction (r : RecordData P D) (d : FiniteReductionData P D r.pref)

def RecordRouting.record
    {P : Params} {D : ClosureData P} :
    RecordRouting P D → RecordData P D
  | .emptiness r _ => r
  | .exclusion r _ => r
  | .finiteReduction r _ => r

def RecordRouting.tag
    {P : Params} {D : ClosureData P} :
    RecordRouting P D → LocalClosureKind
  | .emptiness _ _ => LocalClosureKind.emptiness
  | .exclusion _ _ => LocalClosureKind.exclusion
  | .finiteReduction _ _ => LocalClosureKind.finiteReduction

def RecordRouting.children
    {P : Params} {D : ClosureData P} :
    RecordRouting P D → ChildPrefixes
  | .emptiness _ _ => []
  | .exclusion _ _ => []
  | .finiteReduction _ d => d.children

@[simp] theorem RecordRouting.record_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : EmptinessData P D r.pref) :
    (RecordRouting.emptiness r d).record = r := rfl

@[simp] theorem RecordRouting.record_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : ExclusionData P D r.pref) :
    (RecordRouting.exclusion r d).record = r := rfl

@[simp] theorem RecordRouting.record_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : FiniteReductionData P D r.pref) :
    (RecordRouting.finiteReduction r d).record = r := rfl

@[simp] theorem RecordRouting.tag_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : EmptinessData P D r.pref) :
    (RecordRouting.emptiness r d).tag = LocalClosureKind.emptiness := rfl

@[simp] theorem RecordRouting.tag_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : ExclusionData P D r.pref) :
    (RecordRouting.exclusion r d).tag = LocalClosureKind.exclusion := rfl

@[simp] theorem RecordRouting.tag_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : FiniteReductionData P D r.pref) :
    (RecordRouting.finiteReduction r d).tag = LocalClosureKind.finiteReduction := rfl

@[simp] theorem RecordRouting.children_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : EmptinessData P D r.pref) :
    (RecordRouting.emptiness r d).children = [] := rfl

@[simp] theorem RecordRouting.children_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : ExclusionData P D r.pref) :
    (RecordRouting.exclusion r d).children = [] := rfl

@[simp] theorem RecordRouting.children_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) (d : FiniteReductionData P D r.pref) :
    (RecordRouting.finiteReduction r d).children = d.children := rfl

def recordRouting
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : RecordRouting P D :=
  match r with
  | ⟨pref, .emptiness d⟩ =>
      RecordRouting.emptiness ⟨pref, .emptiness d⟩ d
  | ⟨pref, .exclusion d⟩ =>
      RecordRouting.exclusion ⟨pref, .exclusion d⟩ d
  | ⟨pref, .finiteReduction d⟩ =>
      RecordRouting.finiteReduction ⟨pref, .finiteReduction d⟩ d

@[simp] theorem recordRouting_record
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (recordRouting r).record = r := by
  cases r with
  | mk pref closure =>
      cases closure <;> rfl

@[simp] theorem recordRouting_tag
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (recordRouting r).tag = recordKind r := by
  cases r with
  | mk pref closure =>
      cases closure <;> rfl

theorem recordRouting_spec
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ d : EmptinessData P D r.pref,
      recordRouting r = RecordRouting.emptiness r d ∧
      IsEmptinessRecord r) ∨
    (∃ d : ExclusionData P D r.pref,
      recordRouting r = RecordRouting.exclusion r d ∧
      IsExclusionRecord r) ∨
    (∃ d : FiniteReductionData P D r.pref,
      recordRouting r = RecordRouting.finiteReduction r d ∧
      IsFiniteReductionRecord r) := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          left
          exact ⟨d, rfl, rfl⟩
      | exclusion d =>
          right
          left
          exact ⟨d, rfl, rfl⟩
      | finiteReduction d =>
          right
          right
          exact ⟨d, rfl, rfl⟩

theorem RecordRouting.is_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ d : EmptinessData P D r.pref,
      recordRouting r = RecordRouting.emptiness r d) ↔
    IsEmptinessRecord r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          constructor
          · intro _
            rfl
          · intro _
            exact ⟨d, rfl⟩
      | exclusion d =>
          constructor
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
          · intro h
            cases h
      | finiteReduction d =>
          constructor
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
          · intro h
            cases h

theorem RecordRouting.is_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ d : ExclusionData P D r.pref,
      recordRouting r = RecordRouting.exclusion r d) ↔
    IsExclusionRecord r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          constructor
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
          · intro h
            cases h
      | exclusion d =>
          constructor
          · intro _
            rfl
          · intro _
            exact ⟨d, rfl⟩
      | finiteReduction d =>
          constructor
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
          · intro h
            cases h

theorem RecordRouting.is_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ d : FiniteReductionData P D r.pref,
      recordRouting r = RecordRouting.finiteReduction r d) ↔
    IsFiniteReductionRecord r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          constructor
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
          · intro h
            cases h
      | exclusion d =>
          constructor
          · intro h
            rcases h with ⟨d', hd'⟩
            cases hd'
          · intro h
            cases h
      | finiteReduction d =>
          constructor
          · intro _
            rfl
          · intro _
            exact ⟨d, rfl⟩

theorem recordRouting_emptiness_closes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    {d : EmptinessData P D r.pref}
    (_hRoute : recordRouting r = RecordRouting.emptiness r d)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : recordCoversSupport r S) :
    False := by
  exact emptinessData_closes_support P D r.pref d S hAdm hCov

theorem recordRouting_exclusion_closes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    {d : ExclusionData P D r.pref}
    (_hRoute : recordRouting r = RecordRouting.exclusion r d)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : recordCoversSupport r S)
    (hCandClosed :
      d.kind = ExclusionKind.candNFailure →
        CandNEmpty P D S →
        False)
    (hNonInt :
      d.kind = ExclusionKind.nonIntegrality →
        supportNonIntegral S →
        False) :
    False := by
  exact exclusionData_closes_support
    P D r.pref d S hAdm hCov hCandClosed hNonInt

theorem recordRouting_finiteReduction_routes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    {d : FiniteReductionData P D r.pref}
    (_hRoute : recordRouting r = RecordRouting.finiteReduction r d)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : recordCoversSupport r S) :
    ChildPrefixesCoverSupport d.children S := by
  exact finiteReductionData_routes_support_to_child
    P D r.pref d S hAdm hCov

theorem recordRouting_finiteReduction_child_descends
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    {d : FiniteReductionData P D r.pref}
    (_hRoute : recordRouting r = RecordRouting.finiteReduction r d)
    (child : Prefix)
    (hChild : child ∈ d.children) :
    d.descentMeasure child < d.descentMeasure r.pref := by
  exact finiteReductionData_child_descends
    P D r.pref child d hChild

theorem certificateHasRecord_records
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D)
    (r : RecordData P D) :
    certificateHasRecord C r ↔ r ∈ C.records := by
  rfl

theorem certificateHasRecord_of_mem
    {P : Params} {D : ClosureData P}
    {C : GlobalCertificate P D}
    {r : RecordData P D}
    (h : r ∈ C.records) :
    certificateHasRecord C r := by
  exact h

theorem mem_of_certificateHasRecord
    {P : Params} {D : ClosureData P}
    {C : GlobalCertificate P D}
    {r : RecordData P D}
    (h : certificateHasRecord C r) :
    r ∈ C.records := by
  exact h

theorem globalCertificate_covers_record
    {P : Params} {D : ClosureData P}
    (C : GlobalCertificate P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    ∃ r : RecordData P D,
      certificateHasRecord C r ∧
      recordCoversSupport r S := by
  rcases globalCertificate_covers_support P D C S hAdm with ⟨r, hr, hCov⟩
  exact ⟨r, hr, hCov⟩

end Certificate
end CaseC
end Lehmer