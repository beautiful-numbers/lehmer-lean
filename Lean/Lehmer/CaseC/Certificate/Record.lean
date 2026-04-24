-- FILE: Lean/Lehmer/CaseC/Certificate/Record.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def IsEmptinessRecord (r : RecordData) : Prop :=
  recordKind r = LocalClosureKind.emptiness

def IsExclusionRecord (r : RecordData) : Prop :=
  recordKind r = LocalClosureKind.exclusion

def IsFiniteReductionRecord (r : RecordData) : Prop :=
  recordKind r = LocalClosureKind.finiteReduction

@[simp] theorem IsEmptinessRecord_def (r : RecordData) :
    IsEmptinessRecord r = (recordKind r = LocalClosureKind.emptiness) := rfl

@[simp] theorem IsExclusionRecord_def (r : RecordData) :
    IsExclusionRecord r = (recordKind r = LocalClosureKind.exclusion) := rfl

@[simp] theorem IsFiniteReductionRecord_def (r : RecordData) :
    IsFiniteReductionRecord r = (recordKind r = LocalClosureKind.finiteReduction) := rfl

def recordPrefix (r : RecordData) : Prefix :=
  r.pref

@[simp] theorem recordPrefix_def (r : RecordData) :
    recordPrefix r = r.pref := rfl

def recordSupport (r : RecordData) : Support :=
  r.pref.support

@[simp] theorem recordSupport_def (r : RecordData) :
    recordSupport r = r.pref.support := rfl

def recordClosure (r : RecordData) : LocalClosure :=
  r.closure

@[simp] theorem recordClosure_def (r : RecordData) :
    recordClosure r = r.closure := rfl

def recordHasChild (r : RecordData) (p : Prefix) : Prop :=
  p ∈ recordChildren r

@[simp] theorem recordHasChild_def (r : RecordData) (p : Prefix) :
    recordHasChild r p = (p ∈ recordChildren r) := rfl

def certificateHasRecord (C : GlobalCertificate) (r : RecordData) : Prop :=
  r ∈ certificateRecords C

@[simp] theorem certificateHasRecord_def (C : GlobalCertificate) (r : RecordData) :
    certificateHasRecord C r = (r ∈ certificateRecords C) := rfl

theorem IsEmptinessRecord.not_exclusion (r : RecordData) :
    IsEmptinessRecord r → ¬ IsExclusionRecord r := by
  intro hE hX
  have h : LocalClosureKind.emptiness = LocalClosureKind.exclusion := by
    calc
      LocalClosureKind.emptiness = recordKind r := hE.symm
      _ = LocalClosureKind.exclusion := hX
  exact localClosureKind_emptiness_ne_exclusion h

theorem IsEmptinessRecord.not_finiteReduction (r : RecordData) :
    IsEmptinessRecord r → ¬ IsFiniteReductionRecord r := by
  intro hE hF
  have h : LocalClosureKind.emptiness = LocalClosureKind.finiteReduction := by
    calc
      LocalClosureKind.emptiness = recordKind r := hE.symm
      _ = LocalClosureKind.finiteReduction := hF
  exact localClosureKind_emptiness_ne_finiteReduction h

theorem IsExclusionRecord.not_emptiness (r : RecordData) :
    IsExclusionRecord r → ¬ IsEmptinessRecord r := by
  intro hX hE
  exact (IsEmptinessRecord.not_exclusion r hE) hX

theorem IsExclusionRecord.not_finiteReduction (r : RecordData) :
    IsExclusionRecord r → ¬ IsFiniteReductionRecord r := by
  intro hX hF
  have h : LocalClosureKind.exclusion = LocalClosureKind.finiteReduction := by
    calc
      LocalClosureKind.exclusion = recordKind r := hX.symm
      _ = LocalClosureKind.finiteReduction := hF
  exact localClosureKind_exclusion_ne_finiteReduction h

theorem IsFiniteReductionRecord.not_emptiness (r : RecordData) :
    IsFiniteReductionRecord r → ¬ IsEmptinessRecord r := by
  intro hF hE
  exact (IsEmptinessRecord.not_finiteReduction r hE) hF

theorem IsFiniteReductionRecord.not_exclusion (r : RecordData) :
    IsFiniteReductionRecord r → ¬ IsExclusionRecord r := by
  intro hF hX
  exact (IsExclusionRecord.not_finiteReduction r hX) hF

theorem record_exhaustive (r : RecordData) :
    IsEmptinessRecord r ∨ IsExclusionRecord r ∨ IsFiniteReductionRecord r := by
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

/--
Routing of a local prefix-record into one of the three paper-level closure modes:
emptiness / exclusion / finite splitting.
This is a classification layer only; local soundness/completeness is handled later.
-/
inductive RecordRouting where
  | emptiness (r : RecordData)
  | exclusion (r : RecordData)
  | finiteReduction (r : RecordData)

def recordRouting (r : RecordData) : RecordRouting :=
  match r.closure.kind with
  | LocalClosureKind.emptiness => RecordRouting.emptiness r
  | LocalClosureKind.exclusion => RecordRouting.exclusion r
  | LocalClosureKind.finiteReduction => RecordRouting.finiteReduction r

def RecordRouting.record : RecordRouting → RecordData
  | .emptiness r => r
  | .exclusion r => r
  | .finiteReduction r => r

@[simp] theorem RecordRouting.record_emptiness (r : RecordData) :
    (RecordRouting.emptiness r).record = r := rfl

@[simp] theorem RecordRouting.record_exclusion (r : RecordData) :
    (RecordRouting.exclusion r).record = r := rfl

@[simp] theorem RecordRouting.record_finiteReduction (r : RecordData) :
    (RecordRouting.finiteReduction r).record = r := rfl

theorem RecordRouting.sound (rr : RecordRouting) :
    rr.record = rr.record := rfl

def RecordRouting.tag : RecordRouting → LocalClosureKind
  | .emptiness _ => LocalClosureKind.emptiness
  | .exclusion _ => LocalClosureKind.exclusion
  | .finiteReduction _ => LocalClosureKind.finiteReduction

@[simp] theorem RecordRouting.tag_emptiness (r : RecordData) :
    (RecordRouting.emptiness r).tag = LocalClosureKind.emptiness := rfl

@[simp] theorem RecordRouting.tag_exclusion (r : RecordData) :
    (RecordRouting.exclusion r).tag = LocalClosureKind.exclusion := rfl

@[simp] theorem RecordRouting.tag_finiteReduction (r : RecordData) :
    (RecordRouting.finiteReduction r).tag = LocalClosureKind.finiteReduction := rfl

@[simp] theorem recordRouting_tag (r : RecordData) :
    (recordRouting r).tag = recordKind r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | mk kind children =>
          cases kind <;> rfl

theorem recordRouting_spec (r : RecordData) :
    (recordRouting r = RecordRouting.emptiness r ∧ IsEmptinessRecord r) ∨
    (recordRouting r = RecordRouting.exclusion r ∧ IsExclusionRecord r) ∨
    (recordRouting r = RecordRouting.finiteReduction r ∧ IsFiniteReductionRecord r) := by
  cases r with
  | mk pref closure =>
      cases closure with
      | mk kind children =>
          cases kind
          · left
            exact ⟨rfl, rfl⟩
          · right
            left
            exact ⟨rfl, rfl⟩
          · right
            right
            exact ⟨rfl, rfl⟩

@[simp] theorem recordRouting_record (r : RecordData) :
    (recordRouting r).record = r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | mk kind children =>
          cases kind <;> rfl

theorem RecordRouting.is_emptiness (r : RecordData) :
    (recordRouting r = RecordRouting.emptiness r) ↔ IsEmptinessRecord r := by
  constructor
  · intro h
    have ht : (recordRouting r).tag = LocalClosureKind.emptiness := by
      simp [h]
    simp [recordRouting_tag] at ht
    exact ht
  · intro hE
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · rfl
            · exact False.elim ((IsEmptinessRecord.not_exclusion
                ⟨pref, ⟨LocalClosureKind.exclusion, children⟩⟩ hE) rfl)
            · exact False.elim ((IsEmptinessRecord.not_finiteReduction
                ⟨pref, ⟨LocalClosureKind.finiteReduction, children⟩⟩ hE) rfl)

theorem RecordRouting.is_exclusion (r : RecordData) :
    (recordRouting r = RecordRouting.exclusion r) ↔ IsExclusionRecord r := by
  constructor
  · intro h
    have ht : (recordRouting r).tag = LocalClosureKind.exclusion := by
      simp [h]
    simp [recordRouting_tag] at ht
    exact ht
  · intro hX
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · exact False.elim ((IsExclusionRecord.not_emptiness
                ⟨pref, ⟨LocalClosureKind.emptiness, children⟩⟩ hX) rfl)
            · rfl
            · exact False.elim ((IsExclusionRecord.not_finiteReduction
                ⟨pref, ⟨LocalClosureKind.finiteReduction, children⟩⟩ hX) rfl)

theorem RecordRouting.is_finiteReduction (r : RecordData) :
    (recordRouting r = RecordRouting.finiteReduction r) ↔ IsFiniteReductionRecord r := by
  constructor
  · intro h
    have ht : (recordRouting r).tag = LocalClosureKind.finiteReduction := by
      simp [h]
    simp [recordRouting_tag] at ht
    exact ht
  · intro hF
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · exact False.elim ((IsFiniteReductionRecord.not_emptiness
                ⟨pref, ⟨LocalClosureKind.emptiness, children⟩⟩ hF) rfl)
            · exact False.elim ((IsFiniteReductionRecord.not_exclusion
                ⟨pref, ⟨LocalClosureKind.exclusion, children⟩⟩ hF) rfl)
            · rfl

end Certificate
end CaseC
end Lehmer