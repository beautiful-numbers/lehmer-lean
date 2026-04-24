-- FILE: Lean/Lehmer/CaseC/Certificate/SoundnessLocal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Priority : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority
import Lehmer.CaseC.Certificate.Coverage

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def LocallySoundEmptinessRecord (r : RecordData) : Prop :=
  IsEmptinessRecord r

def LocallySoundExclusionRecord (r : RecordData) : Prop :=
  IsExclusionRecord r

def LocallySoundFiniteReductionRecord (r : RecordData) : Prop :=
  IsFiniteReductionRecord r

@[simp] theorem LocallySoundEmptinessRecord_def (r : RecordData) :
    LocallySoundEmptinessRecord r = IsEmptinessRecord r := rfl

@[simp] theorem LocallySoundExclusionRecord_def (r : RecordData) :
    LocallySoundExclusionRecord r = IsExclusionRecord r := rfl

@[simp] theorem LocallySoundFiniteReductionRecord_def (r : RecordData) :
    LocallySoundFiniteReductionRecord r = IsFiniteReductionRecord r := rfl

def LocallySoundRecord (r : RecordData) : Prop :=
  LocallySoundEmptinessRecord r ∨
    LocallySoundExclusionRecord r ∨
    LocallySoundFiniteReductionRecord r

@[simp] theorem LocallySoundRecord_def (r : RecordData) :
    LocallySoundRecord r =
      (LocallySoundEmptinessRecord r ∨
        LocallySoundExclusionRecord r ∨
        LocallySoundFiniteReductionRecord r) := rfl

theorem LocallySoundEmptinessRecord.not_exclusion (r : RecordData) :
    LocallySoundEmptinessRecord r → ¬ LocallySoundExclusionRecord r := by
  intro h
  exact IsEmptinessRecord.not_exclusion r h

theorem LocallySoundEmptinessRecord.not_finiteReduction (r : RecordData) :
    LocallySoundEmptinessRecord r → ¬ LocallySoundFiniteReductionRecord r := by
  intro h
  exact IsEmptinessRecord.not_finiteReduction r h

theorem LocallySoundExclusionRecord.not_emptiness (r : RecordData) :
    LocallySoundExclusionRecord r → ¬ LocallySoundEmptinessRecord r := by
  intro h
  exact IsExclusionRecord.not_emptiness r h

theorem LocallySoundExclusionRecord.not_finiteReduction (r : RecordData) :
    LocallySoundExclusionRecord r → ¬ LocallySoundFiniteReductionRecord r := by
  intro h
  exact IsExclusionRecord.not_finiteReduction r h

theorem LocallySoundFiniteReductionRecord.not_emptiness (r : RecordData) :
    LocallySoundFiniteReductionRecord r → ¬ LocallySoundEmptinessRecord r := by
  intro h
  exact IsFiniteReductionRecord.not_emptiness r h

theorem LocallySoundFiniteReductionRecord.not_exclusion (r : RecordData) :
    LocallySoundFiniteReductionRecord r → ¬ LocallySoundExclusionRecord r := by
  intro h
  exact IsFiniteReductionRecord.not_exclusion r h

theorem localSoundness_exhaustive (r : RecordData) :
    LocallySoundEmptinessRecord r ∨
      LocallySoundExclusionRecord r ∨
      LocallySoundFiniteReductionRecord r := by
  exact record_exhaustive r

theorem locallySoundRecord_exhaustive (r : RecordData) :
    LocallySoundRecord r := by
  exact localSoundness_exhaustive r

/--
Local routing of soundness through the three paper-level closure modes:
emptiness / exclusion / finite splitting.

This is only a local classification layer. The routing is canonical only when built
from `localSoundnessRouting r`.
-/
inductive LocalSoundnessRouting where
  | emptiness (r : RecordData)
  | exclusion (r : RecordData)
  | finiteReduction (r : RecordData)

def localSoundnessRouting (r : RecordData) : LocalSoundnessRouting :=
  match recordKind r with
  | LocalClosureKind.emptiness => LocalSoundnessRouting.emptiness r
  | LocalClosureKind.exclusion => LocalSoundnessRouting.exclusion r
  | LocalClosureKind.finiteReduction => LocalSoundnessRouting.finiteReduction r

def LocalSoundnessRouting.record : LocalSoundnessRouting → RecordData
  | .emptiness r => r
  | .exclusion r => r
  | .finiteReduction r => r

@[simp] theorem LocalSoundnessRouting.record_emptiness
    (r : RecordData) :
    (LocalSoundnessRouting.emptiness r).record = r := rfl

@[simp] theorem LocalSoundnessRouting.record_exclusion
    (r : RecordData) :
    (LocalSoundnessRouting.exclusion r).record = r := rfl

@[simp] theorem LocalSoundnessRouting.record_finiteReduction
    (r : RecordData) :
    (LocalSoundnessRouting.finiteReduction r).record = r := rfl

def LocalSoundnessRouting.kind : LocalSoundnessRouting → LocalClosureKind
  | .emptiness _ => LocalClosureKind.emptiness
  | .exclusion _ => LocalClosureKind.exclusion
  | .finiteReduction _ => LocalClosureKind.finiteReduction

@[simp] theorem LocalSoundnessRouting.kind_emptiness
    (r : RecordData) :
    (LocalSoundnessRouting.emptiness r).kind = LocalClosureKind.emptiness := rfl

@[simp] theorem LocalSoundnessRouting.kind_exclusion
    (r : RecordData) :
    (LocalSoundnessRouting.exclusion r).kind = LocalClosureKind.exclusion := rfl

@[simp] theorem LocalSoundnessRouting.kind_finiteReduction
    (r : RecordData) :
    (LocalSoundnessRouting.finiteReduction r).kind = LocalClosureKind.finiteReduction := rfl

@[simp] theorem localSoundnessRouting_record (r : RecordData) :
    (localSoundnessRouting r).record = r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | mk kind children =>
          cases kind <;> rfl

@[simp] theorem localSoundnessRouting_kind (r : RecordData) :
    (localSoundnessRouting r).kind = recordKind r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | mk kind children =>
          cases kind <;> rfl

theorem LocalSoundnessRouting.sound (r : RecordData) :
    LocallySoundRecord (localSoundnessRouting r).record := by
  rw [localSoundnessRouting_record]
  exact locallySoundRecord_exhaustive r

theorem LocalSoundnessRouting.is_emptiness
    (r : RecordData) :
    (localSoundnessRouting r = LocalSoundnessRouting.emptiness r) ↔
      LocallySoundEmptinessRecord r := by
  constructor
  · intro h
    have hk : (localSoundnessRouting r).kind = LocalClosureKind.emptiness := by
      simp [h]
    rw [localSoundnessRouting_kind] at hk
    simp at hk
    exact hk
  · intro hE
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · rfl
            · exact False.elim ((LocallySoundEmptinessRecord.not_exclusion
                ⟨pref, ⟨LocalClosureKind.exclusion, children⟩⟩ hE) rfl)
            · exact False.elim ((LocallySoundEmptinessRecord.not_finiteReduction
                ⟨pref, ⟨LocalClosureKind.finiteReduction, children⟩⟩ hE) rfl)

theorem LocalSoundnessRouting.is_exclusion
    (r : RecordData) :
    (localSoundnessRouting r = LocalSoundnessRouting.exclusion r) ↔
      LocallySoundExclusionRecord r := by
  constructor
  · intro h
    have hk : (localSoundnessRouting r).kind = LocalClosureKind.exclusion := by
      simp [h]
    rw [localSoundnessRouting_kind] at hk
    simp at hk
    exact hk
  · intro hX
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · exact False.elim ((LocallySoundExclusionRecord.not_emptiness
                ⟨pref, ⟨LocalClosureKind.emptiness, children⟩⟩ hX) rfl)
            · rfl
            · exact False.elim ((LocallySoundExclusionRecord.not_finiteReduction
                ⟨pref, ⟨LocalClosureKind.finiteReduction, children⟩⟩ hX) rfl)

theorem LocalSoundnessRouting.is_finiteReduction
    (r : RecordData) :
    (localSoundnessRouting r = LocalSoundnessRouting.finiteReduction r) ↔
      LocallySoundFiniteReductionRecord r := by
  constructor
  · intro h
    have hk : (localSoundnessRouting r).kind = LocalClosureKind.finiteReduction := by
      simp [h]
    rw [localSoundnessRouting_kind] at hk
    simp at hk
    exact hk
  · intro hF
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · exact False.elim ((LocallySoundFiniteReductionRecord.not_emptiness
                ⟨pref, ⟨LocalClosureKind.emptiness, children⟩⟩ hF) rfl)
            · exact False.elim ((LocallySoundFiniteReductionRecord.not_exclusion
                ⟨pref, ⟨LocalClosureKind.exclusion, children⟩⟩ hF) rfl)
            · rfl

theorem localSoundnessRouting_spec (r : RecordData) :
    (localSoundnessRouting r = LocalSoundnessRouting.emptiness r ∧
      LocallySoundEmptinessRecord r) ∨
    (localSoundnessRouting r = LocalSoundnessRouting.exclusion r ∧
      LocallySoundExclusionRecord r) ∨
    (localSoundnessRouting r = LocalSoundnessRouting.finiteReduction r ∧
      LocallySoundFiniteReductionRecord r) := by
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

theorem localSoundnessRouting_isEmptiness_iff (r : RecordData) :
    (∃ _ : LocallySoundEmptinessRecord r,
        localSoundnessRouting r = LocalSoundnessRouting.emptiness r) ↔
      LocallySoundEmptinessRecord r := by
  constructor
  · intro h
    rcases h with ⟨hE, _⟩
    exact hE
  · intro hE
    exact ⟨hE, (LocalSoundnessRouting.is_emptiness r).2 hE⟩

theorem localSoundnessRouting_isExclusion_iff (r : RecordData) :
    (∃ _ : LocallySoundExclusionRecord r,
        localSoundnessRouting r = LocalSoundnessRouting.exclusion r) ↔
      LocallySoundExclusionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hX, _⟩
    exact hX
  · intro hX
    exact ⟨hX, (LocalSoundnessRouting.is_exclusion r).2 hX⟩

theorem localSoundnessRouting_isFiniteReduction_iff (r : RecordData) :
    (∃ _ : LocallySoundFiniteReductionRecord r,
        localSoundnessRouting r = LocalSoundnessRouting.finiteReduction r) ↔
      LocallySoundFiniteReductionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hF, _⟩
    exact hF
  · intro hF
    exact ⟨hF, (LocalSoundnessRouting.is_finiteReduction r).2 hF⟩

theorem locallySoundFiniteReduction_children_readable (r : RecordData) :
    LocallySoundFiniteReductionRecord r →
      ∀ S, RecordChildrenCoverSupport r S → RecordChildrenCoverSupport r S := by
  intro _ S hS
  exact hS

theorem locallySoundRecord_kind_readable (r : RecordData) :
    LocallySoundRecord r →
      (recordKind r = LocalClosureKind.emptiness ∨
        recordKind r = LocalClosureKind.exclusion ∨
        recordKind r = LocalClosureKind.finiteReduction) := by
  intro h
  rcases h with h | h | h
  · left
    exact h
  · right
    left
    exact h
  · right
    right
    exact h

end Certificate
end CaseC
end Lehmer