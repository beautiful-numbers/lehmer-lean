-- FILE: Lean/Lehmer/CaseC/Certificate/CompletenessLocal.lean
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
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Priority
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def LocallyCompleteEmptinessRecord (r : RecordData) : Prop :=
  IsEmptinessRecord r

def LocallyCompleteExclusionRecord (r : RecordData) : Prop :=
  IsExclusionRecord r

def LocallyCompleteFiniteReductionRecord (r : RecordData) : Prop :=
  IsFiniteReductionRecord r ∧
    ∀ S, RecordChildrenCoverSupport r S → RecordChildrenCoverSupport r S

@[simp] theorem LocallyCompleteEmptinessRecord_def (r : RecordData) :
    LocallyCompleteEmptinessRecord r = IsEmptinessRecord r := rfl

@[simp] theorem LocallyCompleteExclusionRecord_def (r : RecordData) :
    LocallyCompleteExclusionRecord r = IsExclusionRecord r := rfl

@[simp] theorem LocallyCompleteFiniteReductionRecord_def (r : RecordData) :
    LocallyCompleteFiniteReductionRecord r =
      (IsFiniteReductionRecord r ∧
        ∀ S, RecordChildrenCoverSupport r S → RecordChildrenCoverSupport r S) := rfl

def LocallyCompleteRecord (r : RecordData) : Prop :=
  LocallyCompleteEmptinessRecord r ∨
    LocallyCompleteExclusionRecord r ∨
    LocallyCompleteFiniteReductionRecord r

@[simp] theorem LocallyCompleteRecord_def (r : RecordData) :
    LocallyCompleteRecord r =
      (LocallyCompleteEmptinessRecord r ∨
        LocallyCompleteExclusionRecord r ∨
        LocallyCompleteFiniteReductionRecord r) := rfl

theorem LocallyCompleteEmptinessRecord.not_exclusion (r : RecordData) :
    LocallyCompleteEmptinessRecord r → ¬ LocallyCompleteExclusionRecord r := by
  intro h
  exact IsEmptinessRecord.not_exclusion r h

theorem LocallyCompleteEmptinessRecord.not_finiteReduction (r : RecordData) :
    LocallyCompleteEmptinessRecord r → ¬ LocallyCompleteFiniteReductionRecord r := by
  intro hE hF
  exact (IsEmptinessRecord.not_finiteReduction r hE) hF.1

theorem LocallyCompleteExclusionRecord.not_emptiness (r : RecordData) :
    LocallyCompleteExclusionRecord r → ¬ LocallyCompleteEmptinessRecord r := by
  intro h
  exact IsExclusionRecord.not_emptiness r h

theorem LocallyCompleteExclusionRecord.not_finiteReduction (r : RecordData) :
    LocallyCompleteExclusionRecord r → ¬ LocallyCompleteFiniteReductionRecord r := by
  intro hX hF
  exact (IsExclusionRecord.not_finiteReduction r hX) hF.1

theorem LocallyCompleteFiniteReductionRecord.not_emptiness (r : RecordData) :
    LocallyCompleteFiniteReductionRecord r → ¬ LocallyCompleteEmptinessRecord r := by
  intro hF hE
  exact (IsFiniteReductionRecord.not_emptiness r hF.1) hE

theorem LocallyCompleteFiniteReductionRecord.not_exclusion (r : RecordData) :
    LocallyCompleteFiniteReductionRecord r → ¬ LocallyCompleteExclusionRecord r := by
  intro hF hX
  exact (IsFiniteReductionRecord.not_exclusion r hF.1) hX

theorem locallyCompleteFiniteReduction_children_readable (r : RecordData) :
    LocallyCompleteFiniteReductionRecord r →
      ∀ S, RecordChildrenCoverSupport r S → RecordChildrenCoverSupport r S := by
  intro h
  exact h.2

theorem localCompleteness_exhaustive (r : RecordData) :
    LocallyCompleteEmptinessRecord r ∨
      LocallyCompleteExclusionRecord r ∨
      LocallyCompleteFiniteReductionRecord r := by
  rcases record_exhaustive r with hE | hX | hF
  · left
    exact hE
  · right
    left
    exact hX
  · right
    right
    constructor
    · exact hF
    · intro S hS
      exact hS

theorem locallyCompleteRecord_exhaustive (r : RecordData) :
    LocallyCompleteRecord r := by
  exact localCompleteness_exhaustive r

theorem locallyComplete_implies_locallySound (r : RecordData) :
    LocallyCompleteRecord r → LocallySoundRecord r := by
  intro h
  rcases h with hE | hX | hF
  · exact Or.inl hE
  · exact Or.inr <| Or.inl hX
  · exact Or.inr <| Or.inr hF.1

/--
Local routing of completeness through the three paper-level closure modes:
emptiness / exclusion / finite splitting.

This is only a local classification layer. The routing is canonical only when built
from `localCompletenessRouting r`.
-/
inductive LocalCompletenessRouting where
  | emptiness (r : RecordData)
  | exclusion (r : RecordData)
  | finiteReduction (r : RecordData)

def localCompletenessRouting (r : RecordData) : LocalCompletenessRouting :=
  match recordKind r with
  | LocalClosureKind.emptiness => LocalCompletenessRouting.emptiness r
  | LocalClosureKind.exclusion => LocalCompletenessRouting.exclusion r
  | LocalClosureKind.finiteReduction => LocalCompletenessRouting.finiteReduction r

def LocalCompletenessRouting.record : LocalCompletenessRouting → RecordData
  | .emptiness r => r
  | .exclusion r => r
  | .finiteReduction r => r

@[simp] theorem LocalCompletenessRouting.record_emptiness
    (r : RecordData) :
    (LocalCompletenessRouting.emptiness r).record = r := rfl

@[simp] theorem LocalCompletenessRouting.record_exclusion
    (r : RecordData) :
    (LocalCompletenessRouting.exclusion r).record = r := rfl

@[simp] theorem LocalCompletenessRouting.record_finiteReduction
    (r : RecordData) :
    (LocalCompletenessRouting.finiteReduction r).record = r := rfl

def LocalCompletenessRouting.kind : LocalCompletenessRouting → LocalClosureKind
  | .emptiness _ => LocalClosureKind.emptiness
  | .exclusion _ => LocalClosureKind.exclusion
  | .finiteReduction _ => LocalClosureKind.finiteReduction

@[simp] theorem LocalCompletenessRouting.kind_emptiness
    (r : RecordData) :
    (LocalCompletenessRouting.emptiness r).kind = LocalClosureKind.emptiness := rfl

@[simp] theorem LocalCompletenessRouting.kind_exclusion
    (r : RecordData) :
    (LocalCompletenessRouting.exclusion r).kind = LocalClosureKind.exclusion := rfl

@[simp] theorem LocalCompletenessRouting.kind_finiteReduction
    (r : RecordData) :
    (LocalCompletenessRouting.finiteReduction r).kind = LocalClosureKind.finiteReduction := rfl

@[simp] theorem localCompletenessRouting_record (r : RecordData) :
    (localCompletenessRouting r).record = r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | mk kind children =>
          cases kind <;> rfl

@[simp] theorem localCompletenessRouting_kind (r : RecordData) :
    (localCompletenessRouting r).kind = recordKind r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | mk kind children =>
          cases kind <;> rfl

theorem LocalCompletenessRouting.complete (r : RecordData) :
    LocallyCompleteRecord (localCompletenessRouting r).record := by
  rw [localCompletenessRouting_record]
  exact locallyCompleteRecord_exhaustive r

theorem LocalCompletenessRouting.is_emptiness
    (r : RecordData) :
    (localCompletenessRouting r = LocalCompletenessRouting.emptiness r) ↔
      LocallyCompleteEmptinessRecord r := by
  constructor
  · intro h
    have hk : (localCompletenessRouting r).kind = LocalClosureKind.emptiness := by
      simp [h]
    rw [localCompletenessRouting_kind] at hk
    simpa using hk
  · intro hE
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · rfl
            · exact False.elim ((LocallyCompleteEmptinessRecord.not_exclusion
                ⟨pref, ⟨LocalClosureKind.exclusion, children⟩⟩ hE) rfl)
            · exact False.elim ((LocallyCompleteEmptinessRecord.not_finiteReduction
                ⟨pref, ⟨LocalClosureKind.finiteReduction, children⟩⟩ hE)
                ⟨rfl, by intro S hS; exact hS⟩)

theorem LocalCompletenessRouting.is_exclusion
    (r : RecordData) :
    (localCompletenessRouting r = LocalCompletenessRouting.exclusion r) ↔
      LocallyCompleteExclusionRecord r := by
  constructor
  · intro h
    have hk : (localCompletenessRouting r).kind = LocalClosureKind.exclusion := by
      simp [h]
    rw [localCompletenessRouting_kind] at hk
    simpa using hk
  · intro hX
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · exact False.elim ((LocallyCompleteExclusionRecord.not_emptiness
                ⟨pref, ⟨LocalClosureKind.emptiness, children⟩⟩ hX) rfl)
            · rfl
            · exact False.elim ((LocallyCompleteExclusionRecord.not_finiteReduction
                ⟨pref, ⟨LocalClosureKind.finiteReduction, children⟩⟩ hX)
                ⟨rfl, by intro S hS; exact hS⟩)

theorem LocalCompletenessRouting.is_finiteReduction
    (r : RecordData) :
    (localCompletenessRouting r = LocalCompletenessRouting.finiteReduction r) ↔
      LocallyCompleteFiniteReductionRecord r := by
  constructor
  · intro h
    have hk : (localCompletenessRouting r).kind = LocalClosureKind.finiteReduction := by
      simp [h]
    rw [localCompletenessRouting_kind] at hk
    refine ⟨hk, ?_⟩
    intro S hS
    exact hS
  · intro hF
    cases r with
    | mk pref closure =>
        cases closure with
        | mk kind children =>
            cases kind
            · exact False.elim ((LocallyCompleteFiniteReductionRecord.not_emptiness
                ⟨pref, ⟨LocalClosureKind.emptiness, children⟩⟩ hF) rfl)
            · exact False.elim ((LocallyCompleteFiniteReductionRecord.not_exclusion
                ⟨pref, ⟨LocalClosureKind.exclusion, children⟩⟩ hF) rfl)
            · rfl

theorem localCompletenessRouting_spec (r : RecordData) :
    (localCompletenessRouting r = LocalCompletenessRouting.emptiness r ∧
      LocallyCompleteEmptinessRecord r) ∨
    (localCompletenessRouting r = LocalCompletenessRouting.exclusion r ∧
      LocallyCompleteExclusionRecord r) ∨
    (localCompletenessRouting r = LocalCompletenessRouting.finiteReduction r ∧
      LocallyCompleteFiniteReductionRecord r) := by
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
            exact ⟨rfl, ⟨rfl, by intro S hS; exact hS⟩⟩

theorem localCompletenessRouting_isEmptiness_iff (r : RecordData) :
    (∃ _ : LocallyCompleteEmptinessRecord r,
        localCompletenessRouting r = LocalCompletenessRouting.emptiness r) ↔
      LocallyCompleteEmptinessRecord r := by
  constructor
  · intro h
    rcases h with ⟨hE, _⟩
    exact hE
  · intro hE
    exact ⟨hE, (LocalCompletenessRouting.is_emptiness r).2 hE⟩

theorem localCompletenessRouting_isExclusion_iff (r : RecordData) :
    (∃ _ : LocallyCompleteExclusionRecord r,
        localCompletenessRouting r = LocalCompletenessRouting.exclusion r) ↔
      LocallyCompleteExclusionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hX, _⟩
    exact hX
  · intro hX
    exact ⟨hX, (LocalCompletenessRouting.is_exclusion r).2 hX⟩

theorem localCompletenessRouting_isFiniteReduction_iff (r : RecordData) :
    (∃ _ : LocallyCompleteFiniteReductionRecord r,
        localCompletenessRouting r = LocalCompletenessRouting.finiteReduction r) ↔
      LocallyCompleteFiniteReductionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hF, _⟩
    exact hF
  · intro hF
    exact ⟨hF, (LocalCompletenessRouting.is_finiteReduction r).2 hF⟩

theorem locallyCompleteRecord_kind_readable (r : RecordData) :
    LocallyCompleteRecord r →
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
    exact h.1

theorem locallyCompleteRecord_children_readable (r : RecordData) :
    LocallyCompleteFiniteReductionRecord r →
      ∀ S, RecordChildrenCoverSupport r S → RecordChildrenCoverSupport r S := by
  intro h
  exact h.2

theorem locallyComplete_and_locallySound_iff_kind (r : RecordData) :
    LocallyCompleteRecord r ∧ LocallySoundRecord r := by
  constructor
  · exact locallyCompleteRecord_exhaustive r
  · exact locallyComplete_implies_locallySound r (locallyCompleteRecord_exhaustive r)

end Certificate
end CaseC
end Lehmer