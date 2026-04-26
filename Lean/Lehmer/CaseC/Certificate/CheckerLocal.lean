-- FILE: Lean/Lehmer/CaseC/Certificate/CheckerLocal.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.SoundnessLocal : def thm
- Lehmer.CaseC.Certificate.CompletenessLocal : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.SoundnessLocal
import Lehmer.CaseC.Certificate.CompletenessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

def LocallyCheckedRecord
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) : Prop :=
  LocallySoundRecord r ∧ LocallyCompleteRecord r

@[simp] theorem LocallyCheckedRecord_def
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r =
      (LocallySoundRecord r ∧ LocallyCompleteRecord r) := rfl

theorem locallyCheckedRecord_sound
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r → LocallySoundRecord r := by
  intro h
  exact h.1

theorem locallyCheckedRecord_complete
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r → LocallyCompleteRecord r := by
  intro h
  exact h.2

theorem locallyCheckedRecord_of_sound_complete
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallySoundRecord r →
    LocallyCompleteRecord r →
    LocallyCheckedRecord r := by
  intro hs hc
  exact ⟨hs, hc⟩

theorem locallyCheckedRecord_exhaustive
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r ∨ ¬ LocallyCheckedRecord r := by
  exact Classical.em _

theorem locallyCheckedRecord_routing_cases
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (_hChk : LocallyCheckedRecord r) :
    IsEmptinessRecord r ∨
      IsExclusionRecord r ∨
      IsFiniteReductionRecord r := by
  exact record_exhaustive r

theorem locallyCheckedRecord_kind_readable
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r →
      IsEmptinessRecord r ∨
        IsExclusionRecord r ∨
        IsFiniteReductionRecord r := by
  intro hChk
  exact locallyCheckedRecord_routing_cases hChk

theorem locallyCheckedRecord_not_exclusion_of_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r →
    IsEmptinessRecord r →
    ¬ IsExclusionRecord r := by
  intro _ hE
  exact IsEmptinessRecord.not_exclusion r hE

theorem locallyCheckedRecord_not_finiteReduction_of_emptiness
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r →
    IsEmptinessRecord r →
    ¬ IsFiniteReductionRecord r := by
  intro _ hE
  exact IsEmptinessRecord.not_finiteReduction r hE

theorem locallyCheckedRecord_not_emptiness_of_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r →
    IsExclusionRecord r →
    ¬ IsEmptinessRecord r := by
  intro _ hX
  exact IsExclusionRecord.not_emptiness r hX

theorem locallyCheckedRecord_not_finiteReduction_of_exclusion
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r →
    IsExclusionRecord r →
    ¬ IsFiniteReductionRecord r := by
  intro _ hX
  exact IsExclusionRecord.not_finiteReduction r hX

theorem locallyCheckedRecord_not_emptiness_of_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r →
    IsFiniteReductionRecord r →
    ¬ IsEmptinessRecord r := by
  intro _ hF
  exact IsFiniteReductionRecord.not_emptiness r hF

theorem locallyCheckedRecord_not_exclusion_of_finiteReduction
    {P : Params} {D : ClosureData P}
    (r : RecordData P D) :
    LocallyCheckedRecord r →
    IsFiniteReductionRecord r →
    ¬ IsExclusionRecord r := by
  intro _ hF
  exact IsFiniteReductionRecord.not_exclusion r hF

theorem locallyCheckedRecord_emptiness_closes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (_hChk : LocallyCheckedRecord r)
    (hE : IsEmptinessRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    False := by
  rcases (RecordRouting.is_emptiness r).2 hE with ⟨d, hRoute⟩
  exact recordRouting_emptiness_closes_support hRoute S hAdm hCov

theorem locallyCheckedRecord_exclusion_closes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (_hChk : LocallyCheckedRecord r)
    (hX : IsExclusionRecord r)
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

theorem locallyCheckedRecord_finiteReduction_routes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (_hChk : LocallyCheckedRecord r)
    (hF : IsFiniteReductionRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    ∃ d : FiniteReductionData P D r.pref,
      ChildPrefixesCoverSupport d.children S := by
  rcases (RecordRouting.is_finiteReduction r).2 hF with ⟨d, hRoute⟩
  exact ⟨d, recordRouting_finiteReduction_routes_support hRoute S hAdm hCov⟩

theorem locallyCheckedRecord_finiteReduction_child_descends
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (_hChk : LocallyCheckedRecord r)
    (_hF : IsFiniteReductionRecord r)
    (child : Prefix) :
    ∀ d : FiniteReductionData P D r.pref,
      child ∈ d.children →
        d.descentMeasure child < d.descentMeasure r.pref := by
  intro d hChild
  exact d.childDescends child hChild

theorem locallyCheckedRecord_closes_or_routes_support
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    (hChk : LocallyCheckedRecord r)
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
          False)
    (hChildClosed :
      ∀ child : Prefix,
        PrefixCoversSupport child S →
          False) :
    False := by
  rcases locallyCheckedRecord_routing_cases hChk with hE | hX | hF
  · exact locallyCheckedRecord_emptiness_closes_support hChk hE S hAdm hCov
  · exact locallyCheckedRecord_exclusion_closes_support
      hChk hX S hAdm hCov hCandClosed hNonInt
  · rcases locallyCheckedRecord_finiteReduction_routes_support
      hChk hF S hAdm hCov with ⟨d, hChildren⟩
    rcases hChildren with ⟨child, _hMem, hChildCov⟩
    exact hChildClosed child hChildCov

structure CheckerLocalPackage
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) where
  checked : LocallyCheckedRecord r

@[simp] theorem CheckerLocalPackage.checked_mk
    (P : Params) (D : ClosureData P)
    (r : RecordData P D)
    (h : LocallyCheckedRecord r) :
    (CheckerLocalPackage.mk h : CheckerLocalPackage P D r).checked = h := rfl

theorem CheckerLocalPackage.sound
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r) :
    LocallySoundRecord r := by
  exact locallyCheckedRecord_sound r X.checked

theorem CheckerLocalPackage.complete
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r) :
    LocallyCompleteRecord r := by
  exact locallyCheckedRecord_complete r X.checked

theorem CheckerLocalPackage.routing_cases
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r) :
    IsEmptinessRecord r ∨
      IsExclusionRecord r ∨
      IsFiniteReductionRecord r := by
  exact locallyCheckedRecord_routing_cases X.checked

theorem CheckerLocalPackage.closes_or_routes_support
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r)
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
          False)
    (hChildClosed :
      ∀ child : Prefix,
        PrefixCoversSupport child S →
          False) :
    False := by
  exact locallyCheckedRecord_closes_or_routes_support
    X.checked S hAdm hCov hCandClosed hNonInt hChildClosed

theorem CheckerLocalPackage.emptiness_closes_support
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r)
    (hE : IsEmptinessRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    False := by
  exact locallyCheckedRecord_emptiness_closes_support
    X.checked hE S hAdm hCov

theorem CheckerLocalPackage.exclusion_closes_support
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r)
    (hX : IsExclusionRecord r)
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
  exact locallyCheckedRecord_exclusion_closes_support
    X.checked hX S hAdm hCov hCandClosed hNonInt

theorem CheckerLocalPackage.finiteReduction_routes_support
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r)
    (hF : IsFiniteReductionRecord r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    ∃ d : FiniteReductionData P D r.pref,
      ChildPrefixesCoverSupport d.children S := by
  exact locallyCheckedRecord_finiteReduction_routes_support
    X.checked hF S hAdm hCov

theorem CheckerLocalPackage.finiteReduction_child_descends
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r)
    (hF : IsFiniteReductionRecord r)
    (child : Prefix) :
    ∀ d : FiniteReductionData P D r.pref,
      child ∈ d.children →
        d.descentMeasure child < d.descentMeasure r.pref := by
  exact locallyCheckedRecord_finiteReduction_child_descends
    X.checked hF child

def mkLocallyCheckedRecord
    (P : Params) (D : ClosureData P)
    (r : RecordData P D)
    (hs : LocallySoundRecord r)
    (hc : LocallyCompleteRecord r) :
    CheckerLocalPackage P D r :=
  { checked := ⟨hs, hc⟩ }

@[simp] theorem mkLocallyCheckedRecord_checked
    (P : Params) (D : ClosureData P)
    (r : RecordData P D)
    (hs : LocallySoundRecord r)
    (hc : LocallyCompleteRecord r) :
    (mkLocallyCheckedRecord P D r hs hc).checked = ⟨hs, hc⟩ := rfl

theorem checkerLocal_sound
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r) :
    LocallySoundRecord r := by
  exact X.sound P D

theorem checkerLocal_complete
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r) :
    LocallyCompleteRecord r := by
  exact X.complete P D

theorem checkerLocal_checked
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (X : CheckerLocalPackage P D r) :
    LocallyCheckedRecord r := by
  exact X.checked

end Certificate
end CaseC
end Lehmer