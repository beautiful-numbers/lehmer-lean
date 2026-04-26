-- FILE: Lean/Lehmer/CaseC/Certificate/SoundnessLocal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def LocallySoundEmptinessRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  IsEmptinessRecord r

def LocallySoundExclusionRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  IsExclusionRecord r

def LocallySoundFiniteReductionRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  IsFiniteReductionRecord r

@[simp] theorem LocallySoundEmptinessRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundEmptinessRecord r = IsEmptinessRecord r := rfl

@[simp] theorem LocallySoundExclusionRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundExclusionRecord r = IsExclusionRecord r := rfl

@[simp] theorem LocallySoundFiniteReductionRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundFiniteReductionRecord r =
      IsFiniteReductionRecord r := rfl

def LocallySoundRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  LocallySoundEmptinessRecord r ∨
    LocallySoundExclusionRecord r ∨
    LocallySoundFiniteReductionRecord r

@[simp] theorem LocallySoundRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundRecord r =
      (LocallySoundEmptinessRecord r ∨
        LocallySoundExclusionRecord r ∨
        LocallySoundFiniteReductionRecord r) := rfl

theorem LocallySoundEmptinessRecord.not_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundEmptinessRecord r →
      ¬ LocallySoundExclusionRecord r := by
  intro h
  exact IsEmptinessRecord.not_exclusion r h

theorem LocallySoundEmptinessRecord.not_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundEmptinessRecord r →
      ¬ LocallySoundFiniteReductionRecord r := by
  intro h
  exact IsEmptinessRecord.not_finiteReduction r h

theorem LocallySoundExclusionRecord.not_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundExclusionRecord r →
      ¬ LocallySoundEmptinessRecord r := by
  intro h
  exact IsExclusionRecord.not_emptiness r h

theorem LocallySoundExclusionRecord.not_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundExclusionRecord r →
      ¬ LocallySoundFiniteReductionRecord r := by
  intro h
  exact IsExclusionRecord.not_finiteReduction r h

theorem LocallySoundFiniteReductionRecord.not_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundFiniteReductionRecord r →
      ¬ LocallySoundEmptinessRecord r := by
  intro h
  exact IsFiniteReductionRecord.not_emptiness r h

theorem LocallySoundFiniteReductionRecord.not_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundFiniteReductionRecord r →
      ¬ LocallySoundExclusionRecord r := by
  intro h
  exact IsFiniteReductionRecord.not_exclusion r h

theorem localSoundness_exhaustive
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundEmptinessRecord r ∨
      LocallySoundExclusionRecord r ∨
      LocallySoundFiniteReductionRecord r := by
  exact record_exhaustive r

theorem locallySoundRecord_exhaustive
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundRecord r := by
  exact localSoundness_exhaustive r

/--
Local routing of soundness through the three paper-level closure modes:
emptiness / exclusion / finite splitting.

This is only a local classification layer. The routing is canonical only when built
from `localSoundnessRouting r`.
-/
inductive LocalSoundnessRouting
    (P : Params) (D : ClosureData P) where
  | emptiness (r : RecordData P D)
  | exclusion (r : RecordData P D)
  | finiteReduction (r : RecordData P D)

def localSoundnessRouting
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : LocalSoundnessRouting P D :=
  match r with
  | ⟨pref, LocalClosureData.emptiness d⟩ =>
      LocalSoundnessRouting.emptiness
        ({ pref := pref, closure := LocalClosureData.emptiness d } :
          RecordData P D)
  | ⟨pref, LocalClosureData.exclusion d⟩ =>
      LocalSoundnessRouting.exclusion
        ({ pref := pref, closure := LocalClosureData.exclusion d } :
          RecordData P D)
  | ⟨pref, LocalClosureData.finiteReduction d⟩ =>
      LocalSoundnessRouting.finiteReduction
        ({ pref := pref, closure := LocalClosureData.finiteReduction d } :
          RecordData P D)

def LocalSoundnessRouting.record
    {P : Params} {D : ClosureData P} :
    LocalSoundnessRouting P D → RecordData P D
  | .emptiness r => r
  | .exclusion r => r
  | .finiteReduction r => r

@[simp] theorem LocalSoundnessRouting.record_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalSoundnessRouting.emptiness r).record = r := rfl

@[simp] theorem LocalSoundnessRouting.record_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalSoundnessRouting.exclusion r).record = r := rfl

@[simp] theorem LocalSoundnessRouting.record_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalSoundnessRouting.finiteReduction r).record = r := rfl

def LocalSoundnessRouting.kind
    {P : Params} {D : ClosureData P} :
    LocalSoundnessRouting P D → LocalClosureKind
  | .emptiness _ => LocalClosureKind.emptiness
  | .exclusion _ => LocalClosureKind.exclusion
  | .finiteReduction _ => LocalClosureKind.finiteReduction

@[simp] theorem LocalSoundnessRouting.kind_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalSoundnessRouting.emptiness r).kind =
      LocalClosureKind.emptiness := rfl

@[simp] theorem LocalSoundnessRouting.kind_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalSoundnessRouting.exclusion r).kind =
      LocalClosureKind.exclusion := rfl

@[simp] theorem LocalSoundnessRouting.kind_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalSoundnessRouting.finiteReduction r).kind =
      LocalClosureKind.finiteReduction := rfl

@[simp] theorem localSoundnessRouting_record
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localSoundnessRouting r).record = r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d => rfl
      | exclusion d => rfl
      | finiteReduction d => rfl

@[simp] theorem localSoundnessRouting_kind
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localSoundnessRouting r).kind = recordKind r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d => rfl
      | exclusion d => rfl
      | finiteReduction d => rfl

theorem LocalSoundnessRouting.sound
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundRecord (localSoundnessRouting r).record := by
  rw [localSoundnessRouting_record]
  exact locallySoundRecord_exhaustive r

theorem LocalSoundnessRouting.is_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localSoundnessRouting r =
        LocalSoundnessRouting.emptiness r) ↔
      LocallySoundEmptinessRecord r := by
  constructor
  · intro h
    have hk :
        (localSoundnessRouting r).kind =
          LocalClosureKind.emptiness := by
      simp [h]
    rw [localSoundnessRouting_kind] at hk
    simpa [LocallySoundEmptinessRecord] using hk
  · intro hE
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness d =>
            rfl
        | exclusion d =>
            exact False.elim
              ((LocallySoundEmptinessRecord.not_exclusion
                ({ pref := pref, closure := LocalClosureData.exclusion d } :
                  RecordData P D) hE) rfl)
        | finiteReduction d =>
            exact False.elim
              ((LocallySoundEmptinessRecord.not_finiteReduction
                ({ pref := pref,
                   closure := LocalClosureData.finiteReduction d } :
                  RecordData P D) hE) rfl)

theorem LocalSoundnessRouting.is_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localSoundnessRouting r =
        LocalSoundnessRouting.exclusion r) ↔
      LocallySoundExclusionRecord r := by
  constructor
  · intro h
    have hk :
        (localSoundnessRouting r).kind =
          LocalClosureKind.exclusion := by
      simp [h]
    rw [localSoundnessRouting_kind] at hk
    simpa [LocallySoundExclusionRecord] using hk
  · intro hX
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness d =>
            exact False.elim
              ((LocallySoundExclusionRecord.not_emptiness
                ({ pref := pref, closure := LocalClosureData.emptiness d } :
                  RecordData P D) hX) rfl)
        | exclusion d =>
            rfl
        | finiteReduction d =>
            exact False.elim
              ((LocallySoundExclusionRecord.not_finiteReduction
                ({ pref := pref,
                   closure := LocalClosureData.finiteReduction d } :
                  RecordData P D) hX) rfl)

theorem LocalSoundnessRouting.is_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localSoundnessRouting r =
        LocalSoundnessRouting.finiteReduction r) ↔
      LocallySoundFiniteReductionRecord r := by
  constructor
  · intro h
    have hk :
        (localSoundnessRouting r).kind =
          LocalClosureKind.finiteReduction := by
      simp [h]
    rw [localSoundnessRouting_kind] at hk
    simpa [LocallySoundFiniteReductionRecord] using hk
  · intro hF
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness d =>
            exact False.elim
              ((LocallySoundFiniteReductionRecord.not_emptiness
                ({ pref := pref, closure := LocalClosureData.emptiness d } :
                  RecordData P D) hF) rfl)
        | exclusion d =>
            exact False.elim
              ((LocallySoundFiniteReductionRecord.not_exclusion
                ({ pref := pref, closure := LocalClosureData.exclusion d } :
                  RecordData P D) hF) rfl)
        | finiteReduction d =>
            rfl

theorem localSoundnessRouting_spec
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localSoundnessRouting r = LocalSoundnessRouting.emptiness r ∧
      LocallySoundEmptinessRecord r) ∨
    (localSoundnessRouting r = LocalSoundnessRouting.exclusion r ∧
      LocallySoundExclusionRecord r) ∨
    (localSoundnessRouting r = LocalSoundnessRouting.finiteReduction r ∧
      LocallySoundFiniteReductionRecord r) := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          left
          exact ⟨rfl, rfl⟩
      | exclusion d =>
          right
          left
          exact ⟨rfl, rfl⟩
      | finiteReduction d =>
          right
          right
          exact ⟨rfl, rfl⟩

theorem localSoundnessRouting_isEmptiness_iff
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ _ : LocallySoundEmptinessRecord r,
        localSoundnessRouting r =
          LocalSoundnessRouting.emptiness r) ↔
      LocallySoundEmptinessRecord r := by
  constructor
  · intro h
    rcases h with ⟨hE, _⟩
    exact hE
  · intro hE
    exact ⟨hE, (LocalSoundnessRouting.is_emptiness r).2 hE⟩

theorem localSoundnessRouting_isExclusion_iff
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ _ : LocallySoundExclusionRecord r,
        localSoundnessRouting r =
          LocalSoundnessRouting.exclusion r) ↔
      LocallySoundExclusionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hX, _⟩
    exact hX
  · intro hX
    exact ⟨hX, (LocalSoundnessRouting.is_exclusion r).2 hX⟩

theorem localSoundnessRouting_isFiniteReduction_iff
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ _ : LocallySoundFiniteReductionRecord r,
        localSoundnessRouting r =
          LocalSoundnessRouting.finiteReduction r) ↔
      LocallySoundFiniteReductionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hF, _⟩
    exact hF
  · intro hF
    exact ⟨hF, (LocalSoundnessRouting.is_finiteReduction r).2 hF⟩

theorem locallySoundEmptiness_closes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (hE : LocallySoundEmptinessRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    False := by
  rcases (RecordRouting.is_emptiness r).2 hE with ⟨d, hRoute⟩
  exact recordRouting_emptiness_closes_support
    hRoute S hAdm hCov

theorem locallySoundExclusion_closes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (hX : LocallySoundExclusionRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S)
    (hCandClosed :
      ∀ d : ExclusionData P D r.pref,
        d.kind = ExclusionKind.candNFailure →
          CandNEmpty P D S →
          False)
    (hNonInt :
      ∀ d : ExclusionData P D r.pref,
        d.kind = ExclusionKind.nonIntegrality →
          supportNonIntegral S →
          False) :
    False := by
  rcases (RecordRouting.is_exclusion r).2 hX with ⟨d, hRoute⟩
  exact recordRouting_exclusion_closes_support hRoute S hAdm hCov
    (hCandClosed d) (hNonInt d)

theorem locallySoundFiniteReduction_routes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (hF : LocallySoundFiniteReductionRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    ∃ d : FiniteReductionData P D r.pref,
      ChildPrefixesCoverSupport d.children S := by
  rcases (RecordRouting.is_finiteReduction r).2 hF with ⟨d, hRoute⟩
  exact ⟨d, recordRouting_finiteReduction_routes_support
    hRoute S hAdm hCov⟩

theorem locallySoundFiniteReduction_child_descends
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (_hF : LocallySoundFiniteReductionRecord r)
    (child : Prefix) :
    (∀ d : FiniteReductionData P D r.pref,
      child ∈ d.children →
      d.descentMeasure child < d.descentMeasure r.pref) := by
  intro d hChild
  exact d.childDescends child hChild

theorem locallySoundFiniteReduction_children_readable
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundFiniteReductionRecord r →
      ∀ S, RecordChildrenCoverSupport r S →
        RecordChildrenCoverSupport r S := by
  intro _ S hS
  exact hS

theorem locallySoundRecord_kind_readable
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
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