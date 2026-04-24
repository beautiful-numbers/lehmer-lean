-- FILE: Lean/Lehmer/CaseC/Certificate/Priority.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Certificate.Format : def
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

def PrefixPriority (p q : Prefix) : Prop :=
  prefixCard p ≥ prefixCard q

@[simp] theorem PrefixPriority_def (p q : Prefix) :
    PrefixPriority p q = (prefixCard p ≥ prefixCard q) := rfl

theorem PrefixPriority_refl (p : Prefix) :
    PrefixPriority p p := by
  unfold PrefixPriority
  exact le_rfl

theorem PrefixPriority_trans {p q r : Prefix} :
    PrefixPriority p q → PrefixPriority q r → PrefixPriority p r := by
  intro hpq hqr
  unfold PrefixPriority at hpq hqr ⊢
  exact le_trans hqr hpq

def RecordPriority (r s : RecordData) : Prop :=
  PrefixPriority (recordPrefix r) (recordPrefix s)

@[simp] theorem RecordPriority_def (r s : RecordData) :
    RecordPriority r s = PrefixPriority (recordPrefix r) (recordPrefix s) := rfl

theorem RecordPriority_refl (r : RecordData) :
    RecordPriority r r := by
  unfold RecordPriority
  exact PrefixPriority_refl _

theorem RecordPriority_trans {r s t : RecordData} :
    RecordPriority r s → RecordPriority s t → RecordPriority r t := by
  intro hrs hst
  unfold RecordPriority at hrs hst ⊢
  exact PrefixPriority_trans hrs hst

def recordFamilyPrefixes (R : RecordFamily) : List Prefix :=
  R.map recordPrefix

@[simp] theorem recordFamilyPrefixes_nil :
    recordFamilyPrefixes [] = [] := rfl

@[simp] theorem recordFamilyPrefixes_cons (r : RecordData) (rs : RecordFamily) :
    recordFamilyPrefixes (r :: rs) = recordPrefix r :: recordFamilyPrefixes rs := rfl

def priorityHead? (R : RecordFamily) : Option RecordData :=
  R.head?

@[simp] theorem priorityHead?_nil :
    priorityHead? [] = none := rfl

@[simp] theorem priorityHead?_cons (r : RecordData) (rs : RecordFamily) :
    priorityHead? (r :: rs) = some r := rfl

def isPriorityHead (R : RecordFamily) (r : RecordData) : Prop :=
  priorityHead? R = some r

@[simp] theorem isPriorityHead_def (R : RecordFamily) (r : RecordData) :
    isPriorityHead R r = (priorityHead? R = some r) := rfl

@[simp] theorem isPriorityHead_nil (r : RecordData) :
    ¬ isPriorityHead [] r := by
  simp [isPriorityHead]

@[simp] theorem isPriorityHead_cons (r : RecordData) (rs : RecordFamily) :
    isPriorityHead (r :: rs) r := by
  simp [isPriorityHead]

theorem priority_family_exhaustive (R : RecordFamily) :
    R = [] ∨ ∃ r rs, R = r :: rs := by
  cases R with
  | nil =>
      left
      rfl
  | cons r rs =>
      right
      exact ⟨r, rs, rfl⟩

inductive PriorityRouting where
  | empty
  | head (r : RecordData) (rs : RecordFamily)

def priorityRouting_of_family : RecordFamily → PriorityRouting
  | [] => PriorityRouting.empty
  | r :: rs => PriorityRouting.head r rs

@[simp] theorem priorityRouting_of_family_nil :
    priorityRouting_of_family [] = PriorityRouting.empty := rfl

@[simp] theorem priorityRouting_of_family_cons (r : RecordData) (rs : RecordFamily) :
    priorityRouting_of_family (r :: rs) = PriorityRouting.head r rs := rfl

def PriorityRouting.family : PriorityRouting → RecordFamily
  | .empty => []
  | .head r rs => r :: rs

@[simp] theorem PriorityRouting.family_empty :
    PriorityRouting.family PriorityRouting.empty = [] := rfl

@[simp] theorem PriorityRouting.family_head (r : RecordData) (rs : RecordFamily) :
    PriorityRouting.family (.head r rs) = r :: rs := rfl

def PriorityRouting.selected? : PriorityRouting → Option RecordData
  | .empty => none
  | .head r _ => some r

@[simp] theorem PriorityRouting.selected?_empty :
    PriorityRouting.selected? PriorityRouting.empty = none := rfl

@[simp] theorem PriorityRouting.selected?_head (r : RecordData) (rs : RecordFamily) :
    PriorityRouting.selected? (.head r rs) = some r := rfl

theorem PriorityRouting.sound (pr : PriorityRouting) :
    priorityHead? pr.family = pr.selected? := by
  cases pr <;> rfl

theorem PriorityRouting.is_empty (pr : PriorityRouting) :
    pr = PriorityRouting.empty ∨ ∃ r rs, pr = PriorityRouting.head r rs := by
  cases pr with
  | empty =>
      left
      rfl
  | head r rs =>
      right
      exact ⟨r, rs, rfl⟩

theorem PriorityRouting.is_head (pr : PriorityRouting) :
    pr.selected? = none ∨ ∃ r, pr.selected? = some r := by
  cases pr with
  | empty =>
      left
      rfl
  | head r rs =>
      right
      exact ⟨r, rfl⟩

def certificatePriorityHead? (C : GlobalCertificate) : Option RecordData :=
  priorityHead? (certificateRecords C)

@[simp] theorem certificatePriorityHead?_def (C : GlobalCertificate) :
    certificatePriorityHead? C = priorityHead? (certificateRecords C) := rfl

theorem priorityHead?_eq_some_iff (R : RecordFamily) (r : RecordData) :
    priorityHead? R = some r ↔ ∃ rs, R = r :: rs := by
  cases R with
  | nil =>
      simp [priorityHead?]
  | cons r₀ rs₀ =>
      constructor
      · intro h
        simp [priorityHead?] at h
        cases h
        exact ⟨rs₀, rfl⟩
      · intro h
        rcases h with ⟨rs, hR⟩
        cases hR
        simp [priorityHead?]

theorem priorityHead?_eq_none_iff (R : RecordFamily) :
    priorityHead? R = none ↔ R = [] := by
  cases R with
  | nil =>
      simp [priorityHead?]
  | cons r rs =>
      simp [priorityHead?]

theorem priorityHead?_deterministic (R : RecordFamily) (r s : RecordData) :
    priorityHead? R = some r → priorityHead? R = some s → r = s := by
  intro hr hs
  rw [hr] at hs
  exact Option.some.inj hs

theorem isPriorityHead_unique (R : RecordFamily) (r s : RecordData) :
    isPriorityHead R r → isPriorityHead R s → r = s := by
  intro hr hs
  exact priorityHead?_deterministic R r s hr hs

theorem priorityHead?_of_nonempty (R : RecordFamily) :
    R ≠ [] → ∃ r, priorityHead? R = some r := by
  intro hR
  cases R with
  | nil =>
      contradiction
  | cons r rs =>
      exact ⟨r, rfl⟩

theorem priorityHead?_none_or_some (R : RecordFamily) :
    priorityHead? R = none ∨ ∃ r, priorityHead? R = some r := by
  cases R with
  | nil =>
      left
      rfl
  | cons r rs =>
      right
      exact ⟨r, rfl⟩

theorem priorityRouting_of_family_sound (R : RecordFamily) :
    PriorityRouting.family (priorityRouting_of_family R) = R := by
  cases R <;> rfl

theorem priorityRouting_of_family_selected (R : RecordFamily) :
    PriorityRouting.selected? (priorityRouting_of_family R) = priorityHead? R := by
  cases R <;> rfl

end Certificate
end CaseC
end Lehmer