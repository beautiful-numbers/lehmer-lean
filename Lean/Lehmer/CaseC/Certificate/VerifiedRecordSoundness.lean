-- FILE: Lean/Lehmer/CaseC/Certificate/VerifiedRecordSoundness.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Candidate : def thm
- Lehmer.CaseC.Certificate.Format : def thm
- Lehmer.CaseC.Certificate.Record : def thm
- Lehmer.CaseC.Certificate.Coverage : def thm
- Lehmer.CaseC.Certificate.CheckerLocal : def thm
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Candidate
import Lehmer.CaseC.Certificate.Format
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.CheckerLocal
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic
open Lehmer.Pipeline

def CandidateCoveredByRecord
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (n : ℕ) : Prop :=
  RecordCoversState P D r (candidateState P n)

@[simp] theorem CandidateCoveredByRecord_def
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (n : ℕ) :
    CandidateCoveredByRecord P D r n =
      RecordCoversState P D r (candidateState P n) := rfl

def CandidateCoveredByChild
    (p : Prefix) (n : ℕ) : Prop :=
  PrefixCoversSupport p (candidateSupport n)

@[simp] theorem CandidateCoveredByChild_def
    (p : Prefix) (n : ℕ) :
    CandidateCoveredByChild p n =
      PrefixCoversSupport p (candidateSupport n) := rfl

def RecordChildrenCoverCandidate
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (n : ℕ) : Prop :=
  RecordChildrenCoverSupport r (candidateSupport n)

@[simp] theorem RecordChildrenCoverCandidate_def
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (n : ℕ) :
    RecordChildrenCoverCandidate P D r n =
      RecordChildrenCoverSupport r (candidateSupport n) := rfl

theorem candidateCoveredByRecord_iff
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (n : ℕ) :
    CandidateCoveredByRecord P D r n ↔
      RecordCoversState P D r (candidateState P n) := by
  rfl

theorem candidateCoveredByChild_iff_prefix
    (p : Prefix) (n : ℕ) :
    CandidateCoveredByChild p n ↔
      IsPrefixOf p (candidateSupport n) := by
  rfl

theorem candidateCoveredByRecord_support
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) (n : ℕ) :
    CandidateCoveredByRecord P D r n ↔
      RecordCoversSupport r (candidateSupport n) := by
  rfl

structure VerifiedRecordCertificate
    (P : Params) (D : ClosureData P)
    (r : RecordData P D) : Type where
  checker : CheckerLocalPackage P D r

theorem VerifiedRecordCertificate.checked
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (V : VerifiedRecordCertificate P D r) :
    LocallyCheckedRecord r := by
  exact V.checker.checked

theorem VerifiedRecordCertificate.sound
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (V : VerifiedRecordCertificate P D r) :
    LocallySoundRecord r := by
  exact CheckerLocalPackage.sound P D V.checker

theorem VerifiedRecordCertificate.complete
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (V : VerifiedRecordCertificate P D r) :
    LocallyCompleteRecord r := by
  exact CheckerLocalPackage.complete P D V.checker

theorem VerifiedRecordCertificate.routing_cases
    (P : Params) (D : ClosureData P)
    {r : RecordData P D}
    (V : VerifiedRecordCertificate P D r) :
    IsEmptinessRecord r ∨
      IsExclusionRecord r ∨
      IsFiniteReductionRecord r := by
  exact CheckerLocalPackage.routing_cases P D V.checker

def VerifiedCertificateRecords
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) : Type :=
  ∀ r : RecordData P D,
    certificateHasRecord C r →
    VerifiedRecordCertificate P D r

structure VerifiedRecordSoundnessContext
    (P : Params) (D : ClosureData P) where
  nonIntegralityClosed :
    ∀ S : Support,
      CaseCAdmissibleSupport P D S →
      supportNonIntegral S →
      False
  candNClosed :
    ∀ S : Support,
      CaseCAdmissibleSupport P D S →
      CandNEmpty P D S →
      False
  childClosed :
    ∀ child : Prefix,
      ∀ S : Support,
        CaseCAdmissibleSupport P D S →
        PrefixCoversSupport child S →
        False

theorem VerifiedRecordSoundnessContext.close_nonIntegrality
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hNonInt : supportNonIntegral S) :
    False := by
  exact Γ.nonIntegralityClosed S hAdm hNonInt

theorem VerifiedRecordSoundnessContext.close_candN
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hEmpty : CandNEmpty P D S) :
    False := by
  exact Γ.candNClosed S hAdm hEmpty

theorem VerifiedRecordSoundnessContext.close_child
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (child : Prefix)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : PrefixCoversSupport child S) :
    False := by
  exact Γ.childClosed child S hAdm hCov

theorem soundnessContext_exclusionKindViolation_closes_support
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (k : ExclusionKind)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hV : ExclusionKindViolation P D k S) :
    False := by
  exact exclusionKindViolation_contradicts_admissible
    P D k S hAdm hV
    (by
      intro hk hEmpty
      subst hk
      exact Γ.candNClosed S hAdm hEmpty)
    (by
      intro hk hNonInt
      subst hk
      exact Γ.nonIntegralityClosed S hAdm hNonInt)

theorem verifiedRecordCertificate_closes_support
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (r : RecordData P D)
    (hV : VerifiedRecordCertificate P D r)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCov : RecordCoversSupport r S) :
    False := by
  exact CheckerLocalPackage.closes_or_routes_support P D
    hV.checker
    S hAdm hCov
    (by
      intro _d _hd hEmpty
      exact Γ.candNClosed S hAdm hEmpty)
    (by
      intro _d _hd hNonInt
      exact Γ.nonIntegralityClosed S hAdm hNonInt)
    (by
      intro child hChildCov
      exact Γ.childClosed child S hAdm hChildCov)

theorem verifiedRecordCertificate_finiteReduction_child_descends
    {P : Params} {D : ClosureData P}
    {r : RecordData P D}
    {d : FiniteReductionData P D r.pref}
    (hRoute : recordRouting r = RecordRouting.finiteReduction r d)
    (child : Prefix)
    (hChild : child ∈ d.children) :
    d.descentMeasure child < d.descentMeasure r.pref := by
  exact recordRouting_finiteReduction_child_descends
    hRoute child hChild

theorem verifiedRecordCertificate_closes_state
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (r : RecordData P D)
    (hV : VerifiedRecordCertificate P D r)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support)
    (hCov : RecordCoversState P D r U) :
    False := by
  exact verifiedRecordCertificate_closes_support
    P D Γ r hV U.support hAdm hCov

theorem verifiedCertificateRecords_excludes_covered_support
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCover : GlobalCertificateCoversSupport P D C S) :
    False := by
  rcases hCover with ⟨r, hr, hCov⟩
  exact verifiedRecordCertificate_closes_support
    P D Γ r (hV r hr) S hAdm hCov

theorem verifiedCertificateRecords_excludes_covered_support_expanded
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S)
    (hCover : GlobalCertificateCoversSupport P D C S) :
    False := by
  exact verifiedCertificateRecords_excludes_covered_support
    P D Γ C hV S hAdm hCover

theorem verifiedCertificateRecords_excludes_covered_state
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support)
    (hCover : GlobalCertificateCoversState P D C U) :
    False := by
  exact verifiedCertificateRecords_excludes_covered_support
    P D Γ C hV U.support hAdm hCover

theorem verifiedCertificateRecords_excludes_admissible_support
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (S : Support)
    (hAdm : CaseCAdmissibleSupport P D S) :
    False := by
  have hCover : GlobalCertificateCoversSupport P D C S :=
    globalCertificate_covers_admissible_support P D C S hAdm
  exact verifiedCertificateRecords_excludes_covered_support
    P D Γ C hV S hAdm hCover

theorem verifiedCertificateRecords_excludes_admissible_state
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    (U : State P)
    (hAdm : CaseCAdmissibleSupport P D U.support) :
    False := by
  have hCover : GlobalCertificateCoversState P D C U :=
    globalCertificate_covers_admissible_state P D C U hAdm
  exact verifiedCertificateRecords_excludes_covered_state
    P D Γ C hV U hAdm hCover

def CandidateCoveredByCertificate
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) (n : ℕ) : Prop :=
  GlobalCertificateCoversState P D C (candidateState P n)

@[simp] theorem CandidateCoveredByCertificate_def
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) (n : ℕ) :
    CandidateCoveredByCertificate P D C n =
      GlobalCertificateCoversState P D C (candidateState P n) := rfl

theorem candidateCoveredByCertificate_iff_support
    (P : Params) (D : ClosureData P)
    (C : GlobalCertificate P D) (n : ℕ) :
    CandidateCoveredByCertificate P D C n ↔
      GlobalCertificateCoversSupport P D C (candidateSupport n) := by
  rfl

theorem verifiedCertificateRecords_excludes_covered_candidate
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    {n : ℕ}
    (_hL : LehmerComposite n)
    (_hC : InCaseC n)
    (hAdm : CaseCAdmissibleSupport P D (candidateSupport n))
    (hCover : CandidateCoveredByCertificate P D C n) :
    False := by
  exact verifiedCertificateRecords_excludes_covered_state
    P D Γ C hV (candidateState P n) hAdm hCover

theorem verifiedCertificateRecords_excludes_admissible_candidate
    (P : Params) (D : ClosureData P)
    (Γ : VerifiedRecordSoundnessContext P D)
    (C : GlobalCertificate P D)
    (hV : VerifiedCertificateRecords P D C)
    {n : ℕ}
    (hL : LehmerComposite n)
    (hC : InCaseC n)
    (hAdm : CaseCAdmissibleSupport P D (candidateSupport n)) :
    False := by
  have hCover : CandidateCoveredByCertificate P D C n := by
    exact globalCertificate_covers_admissible_state
      P D C (candidateState P n) hAdm
  exact verifiedCertificateRecords_excludes_covered_candidate
    P D Γ C hV hL hC hAdm hCover

end Certificate
end CaseC
end Lehmer