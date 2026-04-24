-- FILE: Lean/Lehmer/CaseC/Certificate/CheckerLocal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Priority : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.SoundnessLocal : def thm
- Lehmer.CaseC.Certificate.CompletenessLocal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal
import Lehmer.CaseC.Certificate.CompletenessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def LocallyCheckedRecord (r : RecordData) : Prop :=
  LocallySoundRecord r ∧ LocallyCompleteRecord r

@[simp] theorem LocallyCheckedRecord_def (r : RecordData) :
    LocallyCheckedRecord r =
      (LocallySoundRecord r ∧ LocallyCompleteRecord r) := rfl

theorem locallyCheckedRecord_sound (r : RecordData) :
    LocallyCheckedRecord r → LocallySoundRecord r := by
  intro h
  exact h.1

theorem locallyCheckedRecord_complete (r : RecordData) :
    LocallyCheckedRecord r → LocallyCompleteRecord r := by
  intro h
  exact h.2

theorem locallyCheckedRecord_of_sound_complete (r : RecordData) :
    LocallySoundRecord r →
    LocallyCompleteRecord r →
    LocallyCheckedRecord r := by
  intro hs hc
  exact ⟨hs, hc⟩

theorem locallyCheckedRecord_exhaustive (r : RecordData) :
    LocallyCheckedRecord r ∨ ¬ LocallyCheckedRecord r := by
  exact Classical.em _

theorem locallyCheckedRecord_kind_readable (r : RecordData) :
    LocallyCheckedRecord r →
      IsEmptinessRecord r ∨ IsExclusionRecord r ∨ IsFiniteReductionRecord r := by
  intro _
  exact record_exhaustive r

theorem locallyCheckedRecord_not_exclusion_of_emptiness
    (r : RecordData) :
    LocallyCheckedRecord r →
    IsEmptinessRecord r →
    ¬ IsExclusionRecord r := by
  intro _ hE
  exact IsEmptinessRecord.not_exclusion r hE

theorem locallyCheckedRecord_not_finiteReduction_of_emptiness
    (r : RecordData) :
    LocallyCheckedRecord r →
    IsEmptinessRecord r →
    ¬ IsFiniteReductionRecord r := by
  intro _ hE
  exact IsEmptinessRecord.not_finiteReduction r hE

theorem locallyCheckedRecord_not_finiteReduction_of_exclusion
    (r : RecordData) :
    LocallyCheckedRecord r →
    IsExclusionRecord r →
    ¬ IsFiniteReductionRecord r := by
  intro _ hE
  exact IsExclusionRecord.not_finiteReduction r hE

theorem locallyCheckedRecord_routing_readable (r : RecordData) :
    LocallyCheckedRecord r →
      (recordRouting r = RecordRouting.emptiness r ∧ IsEmptinessRecord r) ∨
      (recordRouting r = RecordRouting.exclusion r ∧ IsExclusionRecord r) ∨
      (recordRouting r = RecordRouting.finiteReduction r ∧ IsFiniteReductionRecord r) := by
  intro _
  exact recordRouting_spec r

structure CheckerLocalPackage where
  record : RecordData
  checked : LocallyCheckedRecord record

@[simp] theorem CheckerLocalPackage.record_mk
    (r : RecordData) (h : LocallyCheckedRecord r) :
    (CheckerLocalPackage.mk r h).record = r := rfl

@[simp] theorem CheckerLocalPackage.checked_mk
    (r : RecordData) (h : LocallyCheckedRecord r) :
    (CheckerLocalPackage.mk r h).checked = h := rfl

theorem CheckerLocalPackage.sound (X : CheckerLocalPackage) :
    LocallySoundRecord X.record := by
  exact locallyCheckedRecord_sound X.record X.checked

theorem CheckerLocalPackage.complete (X : CheckerLocalPackage) :
    LocallyCompleteRecord X.record := by
  exact locallyCheckedRecord_complete X.record X.checked

theorem CheckerLocalPackage.kind_readable (X : CheckerLocalPackage) :
    IsEmptinessRecord X.record ∨
      IsExclusionRecord X.record ∨
      IsFiniteReductionRecord X.record := by
  exact locallyCheckedRecord_kind_readable X.record X.checked

def checkedRecordKind (X : CheckerLocalPackage) : LocalClosureKind :=
  recordKind X.record

@[simp] theorem checkedRecordKind_def (X : CheckerLocalPackage) :
    checkedRecordKind X = recordKind X.record := rfl

def checkedRecordChildren (X : CheckerLocalPackage) :=
  recordChildren X.record

@[simp] theorem checkedRecordChildren_def (X : CheckerLocalPackage) :
    checkedRecordChildren X = recordChildren X.record := rfl

def checkedRecordCylinder (X : CheckerLocalPackage) :=
  recordCylinder X.record

@[simp] theorem checkedRecordCylinder_def (X : CheckerLocalPackage) :
    checkedRecordCylinder X = recordCylinder X.record := rfl

theorem CheckerLocalPackage.isEmptiness_or_isExclusion_or_isFiniteReduction
    (X : CheckerLocalPackage) :
    IsEmptinessRecord X.record ∨
      IsExclusionRecord X.record ∨
      IsFiniteReductionRecord X.record := by
  exact X.kind_readable

theorem CheckerLocalPackage.not_exclusion_of_emptiness
    (X : CheckerLocalPackage) :
    IsEmptinessRecord X.record → ¬ IsExclusionRecord X.record := by
  intro h
  exact locallyCheckedRecord_not_exclusion_of_emptiness X.record X.checked h

theorem CheckerLocalPackage.not_finiteReduction_of_emptiness
    (X : CheckerLocalPackage) :
    IsEmptinessRecord X.record → ¬ IsFiniteReductionRecord X.record := by
  intro h
  exact locallyCheckedRecord_not_finiteReduction_of_emptiness X.record X.checked h

theorem CheckerLocalPackage.not_finiteReduction_of_exclusion
    (X : CheckerLocalPackage) :
    IsExclusionRecord X.record → ¬ IsFiniteReductionRecord X.record := by
  intro h
  exact locallyCheckedRecord_not_finiteReduction_of_exclusion X.record X.checked h

theorem CheckerLocalPackage.routing_readable (X : CheckerLocalPackage) :
    (recordRouting X.record = RecordRouting.emptiness X.record ∧ IsEmptinessRecord X.record) ∨
      (recordRouting X.record = RecordRouting.exclusion X.record ∧ IsExclusionRecord X.record) ∨
      (recordRouting X.record = RecordRouting.finiteReduction X.record ∧ IsFiniteReductionRecord X.record) := by
  exact locallyCheckedRecord_routing_readable X.record X.checked

def mkLocallyCheckedRecord (r : RecordData)
    (hs : LocallySoundRecord r) (hc : LocallyCompleteRecord r) :
    CheckerLocalPackage :=
  CheckerLocalPackage.mk r ⟨hs, hc⟩

@[simp] theorem mkLocallyCheckedRecord_record (r : RecordData)
    (hs : LocallySoundRecord r) (hc : LocallyCompleteRecord r) :
    (mkLocallyCheckedRecord r hs hc).record = r := rfl

@[simp] theorem mkLocallyCheckedRecord_checked (r : RecordData)
    (hs : LocallySoundRecord r) (hc : LocallyCompleteRecord r) :
    (mkLocallyCheckedRecord r hs hc).checked = ⟨hs, hc⟩ := rfl

end Certificate
end CaseC
end Lehmer