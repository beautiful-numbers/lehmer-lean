-- FILE: Lean/Lehmer/CaseC/Certificate/CompletenessLocal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.SoundnessLocal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def LocallyCompleteEmptinessRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  IsEmptinessRecord r

def LocallyCompleteExclusionRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  IsExclusionRecord r

def LocallyCompleteFiniteReductionRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  ∃ d : FiniteReductionData P D r.pref,
    r.closure = LocalClosureData.finiteReduction d ∧
      ∀ S : Support,
        CaseCAdmissibleSupport P D S →
        recordCoversSupport r S →
        ChildPrefixesCoverSupport d.children S

@[simp] theorem LocallyCompleteEmptinessRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteEmptinessRecord r = IsEmptinessRecord r := rfl

@[simp] theorem LocallyCompleteExclusionRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteExclusionRecord r = IsExclusionRecord r := rfl

@[simp] theorem LocallyCompleteFiniteReductionRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteFiniteReductionRecord r =
      (∃ d : FiniteReductionData P D r.pref,
        r.closure = LocalClosureData.finiteReduction d ∧
          ∀ S : Support,
            CaseCAdmissibleSupport P D S →
            recordCoversSupport r S →
            ChildPrefixesCoverSupport d.children S) := rfl

def LocallyCompleteRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  LocallyCompleteEmptinessRecord r ∨
    LocallyCompleteExclusionRecord r ∨
    LocallyCompleteFiniteReductionRecord r

@[simp] theorem LocallyCompleteRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteRecord r =
      (LocallyCompleteEmptinessRecord r ∨
        LocallyCompleteExclusionRecord r ∨
        LocallyCompleteFiniteReductionRecord r) := rfl

theorem LocallyCompleteEmptinessRecord.not_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteEmptinessRecord r → ¬ LocallyCompleteExclusionRecord r := by
  intro h
  exact IsEmptinessRecord.not_exclusion r h

theorem LocallyCompleteEmptinessRecord.not_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteEmptinessRecord r → ¬ LocallyCompleteFiniteReductionRecord r := by
  intro hE hF
  rcases hF with ⟨d, hd, _⟩
  have hFR : IsFiniteReductionRecord r := by
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness e =>
            cases hd
        | exclusion e =>
            cases hd
        | finiteReduction e =>
            rfl
  exact (IsEmptinessRecord.not_finiteReduction r hE) hFR

theorem LocallyCompleteExclusionRecord.not_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteExclusionRecord r → ¬ LocallyCompleteEmptinessRecord r := by
  intro h
  exact IsExclusionRecord.not_emptiness r h

theorem LocallyCompleteExclusionRecord.not_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteExclusionRecord r → ¬ LocallyCompleteFiniteReductionRecord r := by
  intro hX hF
  rcases hF with ⟨d, hd, _⟩
  have hFR : IsFiniteReductionRecord r := by
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness e =>
            cases hd
        | exclusion e =>
            cases hd
        | finiteReduction e =>
            rfl
  exact (IsExclusionRecord.not_finiteReduction r hX) hFR

theorem LocallyCompleteFiniteReductionRecord.not_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteFiniteReductionRecord r → ¬ LocallyCompleteEmptinessRecord r := by
  intro hF hE
  exact (LocallyCompleteEmptinessRecord.not_finiteReduction r hE) hF

theorem LocallyCompleteFiniteReductionRecord.not_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteFiniteReductionRecord r → ¬ LocallyCompleteExclusionRecord r := by
  intro hF hX
  exact (LocallyCompleteExclusionRecord.not_finiteReduction r hX) hF

theorem locallyCompleteFiniteReduction_routes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (h : LocallyCompleteFiniteReductionRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : recordCoversSupport r S) :
    ∃ d : FiniteReductionData P D r.pref,
      r.closure = LocalClosureData.finiteReduction d ∧
        ChildPrefixesCoverSupport d.children S := by
  rcases h with ⟨d, hd, hCover⟩
  exact ⟨d, hd, hCover S hAdm hCov⟩

theorem locallyCompleteFiniteReduction_children_readable
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteFiniteReductionRecord r →
      ∀ S,
        CaseCAdmissibleSupport P D S →
        recordCoversSupport r S →
        ∃ d : FiniteReductionData P D r.pref,
          r.closure = LocalClosureData.finiteReduction d ∧
            ChildPrefixesCoverSupport d.children S := by
  intro h S hAdm hCov
  exact locallyCompleteFiniteReduction_routes_support h S hAdm hCov

theorem localCompleteness_exhaustive
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteEmptinessRecord r ∨
      LocallyCompleteExclusionRecord r ∨
      LocallyCompleteFiniteReductionRecord r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d =>
          left
          rfl
      | exclusion d =>
          right
          left
          rfl
      | finiteReduction d =>
          right
          right
          exact ⟨d, rfl, by
            intro S hAdm hCov
            exact finiteReductionData_routes_support_to_child
              P D pref d S hAdm hCov⟩

theorem locallyCompleteRecord_exhaustive
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteRecord r := by
  exact localCompleteness_exhaustive r

theorem locallyComplete_implies_locallySound
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteRecord r → LocallySoundRecord r := by
  intro h
  rcases h with hE | hX | hF
  · exact Or.inl hE
  · exact Or.inr <| Or.inl hX
  · right
    right
    rcases hF with ⟨d, hd, _⟩
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness e =>
            cases hd
        | exclusion e =>
            cases hd
        | finiteReduction e =>
            rfl

/--
Local routing of completeness through the three paper-level closure modes:
emptiness / exclusion / finite splitting.

This is only a local classification layer. The routing is canonical only when built
from `localCompletenessRouting r`.
-/
inductive LocalCompletenessRouting
    (P : Params) (D : ClosureData P) where
  | emptiness (r : RecordData P D)
  | exclusion (r : RecordData P D)
  | finiteReduction (r : RecordData P D)

def localCompletenessRouting
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : LocalCompletenessRouting P D :=
  match r with
  | ⟨pref, LocalClosureData.emptiness d⟩ =>
      LocalCompletenessRouting.emptiness
        ({ pref := pref, closure := LocalClosureData.emptiness d } :
          RecordData P D)
  | ⟨pref, LocalClosureData.exclusion d⟩ =>
      LocalCompletenessRouting.exclusion
        ({ pref := pref, closure := LocalClosureData.exclusion d } :
          RecordData P D)
  | ⟨pref, LocalClosureData.finiteReduction d⟩ =>
      LocalCompletenessRouting.finiteReduction
        ({ pref := pref, closure := LocalClosureData.finiteReduction d } :
          RecordData P D)

def LocalCompletenessRouting.record
    {P : Params} {D : ClosureData P} :
    LocalCompletenessRouting P D → RecordData P D
  | .emptiness r => r
  | .exclusion r => r
  | .finiteReduction r => r

@[simp] theorem LocalCompletenessRouting.record_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalCompletenessRouting.emptiness r).record = r := rfl

@[simp] theorem LocalCompletenessRouting.record_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalCompletenessRouting.exclusion r).record = r := rfl

@[simp] theorem LocalCompletenessRouting.record_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalCompletenessRouting.finiteReduction r).record = r := rfl

def LocalCompletenessRouting.kind
    {P : Params} {D : ClosureData P} :
    LocalCompletenessRouting P D → LocalClosureKind
  | .emptiness _ => LocalClosureKind.emptiness
  | .exclusion _ => LocalClosureKind.exclusion
  | .finiteReduction _ => LocalClosureKind.finiteReduction

@[simp] theorem LocalCompletenessRouting.kind_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalCompletenessRouting.emptiness r).kind = LocalClosureKind.emptiness := rfl

@[simp] theorem LocalCompletenessRouting.kind_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalCompletenessRouting.exclusion r).kind = LocalClosureKind.exclusion := rfl

@[simp] theorem LocalCompletenessRouting.kind_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (LocalCompletenessRouting.finiteReduction r).kind =
      LocalClosureKind.finiteReduction := rfl

@[simp] theorem localCompletenessRouting_record
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localCompletenessRouting r).record = r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d => rfl
      | exclusion d => rfl
      | finiteReduction d => rfl

@[simp] theorem localCompletenessRouting_kind
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localCompletenessRouting r).kind = recordKind r := by
  cases r with
  | mk pref closure =>
      cases closure with
      | emptiness d => rfl
      | exclusion d => rfl
      | finiteReduction d => rfl

theorem LocalCompletenessRouting.complete
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteRecord (localCompletenessRouting r).record := by
  rw [localCompletenessRouting_record]
  exact locallyCompleteRecord_exhaustive r

theorem LocalCompletenessRouting.is_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localCompletenessRouting r =
        LocalCompletenessRouting.emptiness r) ↔
      LocallyCompleteEmptinessRecord r := by
  constructor
  · intro h
    have hk :
        (localCompletenessRouting r).kind =
          LocalClosureKind.emptiness := by
      simp [h]
    rw [localCompletenessRouting_kind] at hk
    simpa [LocallyCompleteEmptinessRecord] using hk
  · intro hE
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness d =>
            rfl
        | exclusion d =>
            exact False.elim
              ((LocallyCompleteEmptinessRecord.not_exclusion
                ({ pref := pref, closure := LocalClosureData.exclusion d } :
                  RecordData P D) hE) rfl)
        | finiteReduction d =>
            have hF : LocallyCompleteFiniteReductionRecord
                ({ pref := pref, closure := LocalClosureData.finiteReduction d } :
                  RecordData P D) := by
              exact ⟨d, rfl, by
                intro S hAdm hCov
                exact finiteReductionData_routes_support_to_child
                  P D pref d S hAdm hCov⟩
            exact False.elim
              ((LocallyCompleteEmptinessRecord.not_finiteReduction
                ({ pref := pref, closure := LocalClosureData.finiteReduction d } :
                  RecordData P D) hE) hF)

theorem LocalCompletenessRouting.is_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localCompletenessRouting r =
        LocalCompletenessRouting.exclusion r) ↔
      LocallyCompleteExclusionRecord r := by
  constructor
  · intro h
    have hk :
        (localCompletenessRouting r).kind =
          LocalClosureKind.exclusion := by
      simp [h]
    rw [localCompletenessRouting_kind] at hk
    simpa [LocallyCompleteExclusionRecord] using hk
  · intro hX
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness d =>
            exact False.elim
              ((LocallyCompleteExclusionRecord.not_emptiness
                ({ pref := pref, closure := LocalClosureData.emptiness d } :
                  RecordData P D) hX) rfl)
        | exclusion d =>
            rfl
        | finiteReduction d =>
            have hF : LocallyCompleteFiniteReductionRecord
                ({ pref := pref, closure := LocalClosureData.finiteReduction d } :
                  RecordData P D) := by
              exact ⟨d, rfl, by
                intro S hAdm hCov
                exact finiteReductionData_routes_support_to_child
                  P D pref d S hAdm hCov⟩
            exact False.elim
              ((LocallyCompleteExclusionRecord.not_finiteReduction
                ({ pref := pref, closure := LocalClosureData.finiteReduction d } :
                  RecordData P D) hX) hF)

theorem LocalCompletenessRouting.is_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localCompletenessRouting r =
        LocalCompletenessRouting.finiteReduction r) ↔
      LocallyCompleteFiniteReductionRecord r := by
  constructor
  · intro h
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness d =>
            cases h
        | exclusion d =>
            cases h
        | finiteReduction d =>
            exact ⟨d, rfl, by
              intro S hAdm hCov
              exact finiteReductionData_routes_support_to_child
                P D pref d S hAdm hCov⟩
  · intro hF
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness d =>
            exact False.elim
              ((LocallyCompleteFiniteReductionRecord.not_emptiness
                ({ pref := pref, closure := LocalClosureData.emptiness d } :
                  RecordData P D) hF) rfl)
        | exclusion d =>
            exact False.elim
              ((LocallyCompleteFiniteReductionRecord.not_exclusion
                ({ pref := pref, closure := LocalClosureData.exclusion d } :
                  RecordData P D) hF) rfl)
        | finiteReduction d =>
            rfl

theorem localCompletenessRouting_spec
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (localCompletenessRouting r = LocalCompletenessRouting.emptiness r ∧
      LocallyCompleteEmptinessRecord r) ∨
    (localCompletenessRouting r = LocalCompletenessRouting.exclusion r ∧
      LocallyCompleteExclusionRecord r) ∨
    (localCompletenessRouting r = LocalCompletenessRouting.finiteReduction r ∧
      LocallyCompleteFiniteReductionRecord r) := by
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
          exact ⟨rfl, ⟨d, rfl, by
            intro S hAdm hCov
            exact finiteReductionData_routes_support_to_child
              P D pref d S hAdm hCov⟩⟩

theorem localCompletenessRouting_isEmptiness_iff
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ _ : LocallyCompleteEmptinessRecord r,
        localCompletenessRouting r =
          LocalCompletenessRouting.emptiness r) ↔
      LocallyCompleteEmptinessRecord r := by
  constructor
  · intro h
    rcases h with ⟨hE, _⟩
    exact hE
  · intro hE
    exact ⟨hE, (LocalCompletenessRouting.is_emptiness r).2 hE⟩

theorem localCompletenessRouting_isExclusion_iff
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ _ : LocallyCompleteExclusionRecord r,
        localCompletenessRouting r =
          LocalCompletenessRouting.exclusion r) ↔
      LocallyCompleteExclusionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hX, _⟩
    exact hX
  · intro hX
    exact ⟨hX, (LocalCompletenessRouting.is_exclusion r).2 hX⟩

theorem localCompletenessRouting_isFiniteReduction_iff
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    (∃ _ : LocallyCompleteFiniteReductionRecord r,
        localCompletenessRouting r =
          LocalCompletenessRouting.finiteReduction r) ↔
      LocallyCompleteFiniteReductionRecord r := by
  constructor
  · intro h
    rcases h with ⟨hF, _⟩
    exact hF
  · intro hF
    exact ⟨hF, (LocalCompletenessRouting.is_finiteReduction r).2 hF⟩

theorem locallyCompleteRecord_kind_readable
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
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
    rcases h with ⟨d, hd, _⟩
    cases r with
    | mk pref closure =>
        cases closure with
        | emptiness e =>
            cases hd
        | exclusion e =>
            cases hd
        | finiteReduction e =>
            rfl

theorem locallyCompleteRecord_children_readable
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteFiniteReductionRecord r →
      ∀ S,
        CaseCAdmissibleSupport P D S →
        recordCoversSupport r S →
        ∃ d : FiniteReductionData P D r.pref,
          r.closure = LocalClosureData.finiteReduction d ∧
            ChildPrefixesCoverSupport d.children S := by
  intro h S hAdm hCov
  exact locallyCompleteFiniteReduction_routes_support h S hAdm hCov

theorem locallyComplete_and_locallySound_iff_kind
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCompleteRecord r ∧ LocallySoundRecord r := by
  constructor
  · exact locallyCompleteRecord_exhaustive r
  · exact locallyComplete_implies_locallySound r (locallyCompleteRecord_exhaustive r)

end Certificate
end CaseC
end Lehmer