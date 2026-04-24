-- FILE: Lean/Lehmer/CaseC/Certificate/Format.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec

namespace Lehmer
namespace CaseC
namespace Certificate

open Lehmer.Basic

inductive LocalClosureKind where
  | emptiness
  | exclusion
  | finiteReduction
deriving DecidableEq

@[simp] theorem localClosureKind_emptiness_ne_exclusion :
    LocalClosureKind.emptiness ≠ LocalClosureKind.exclusion := by
  decide

@[simp] theorem localClosureKind_emptiness_ne_finiteReduction :
    LocalClosureKind.emptiness ≠ LocalClosureKind.finiteReduction := by
  decide

@[simp] theorem localClosureKind_exclusion_ne_emptiness :
    LocalClosureKind.exclusion ≠ LocalClosureKind.emptiness := by
  decide

@[simp] theorem localClosureKind_exclusion_ne_finiteReduction :
    LocalClosureKind.exclusion ≠ LocalClosureKind.finiteReduction := by
  decide

@[simp] theorem localClosureKind_finiteReduction_ne_emptiness :
    LocalClosureKind.finiteReduction ≠ LocalClosureKind.emptiness := by
  decide

@[simp] theorem localClosureKind_finiteReduction_ne_exclusion :
    LocalClosureKind.finiteReduction ≠ LocalClosureKind.exclusion := by
  decide

abbrev ChildPrefixes := List Prefix

structure LocalClosure where
  kind : LocalClosureKind
  children : ChildPrefixes

@[simp] theorem localClosure_kind_mk (k : LocalClosureKind) (cs : ChildPrefixes) :
    (LocalClosure.mk k cs).kind = k := rfl

@[simp] theorem localClosure_children_mk (k : LocalClosureKind) (cs : ChildPrefixes) :
    (LocalClosure.mk k cs).children = cs := rfl

def isEmptinessClosure (c : LocalClosure) : Prop :=
  c.kind = LocalClosureKind.emptiness

def isExclusionClosure (c : LocalClosure) : Prop :=
  c.kind = LocalClosureKind.exclusion

def isFiniteReductionClosure (c : LocalClosure) : Prop :=
  c.kind = LocalClosureKind.finiteReduction

@[simp] theorem isEmptinessClosure_def (c : LocalClosure) :
    isEmptinessClosure c = (c.kind = LocalClosureKind.emptiness) := rfl

@[simp] theorem isExclusionClosure_def (c : LocalClosure) :
    isExclusionClosure c = (c.kind = LocalClosureKind.exclusion) := rfl

@[simp] theorem isFiniteReductionClosure_def (c : LocalClosure) :
    isFiniteReductionClosure c = (c.kind = LocalClosureKind.finiteReduction) := rfl

structure RecordData where
  pref : Prefix
  closure : LocalClosure

@[simp] theorem recordData_mk_pref (p : Prefix) (c : LocalClosure) :
    (RecordData.mk p c).pref = p := rfl

@[simp] theorem recordData_mk_closure (p : Prefix) (c : LocalClosure) :
    (RecordData.mk p c).closure = c := rfl

def recordChildren (r : RecordData) : ChildPrefixes :=
  r.closure.children

@[simp] theorem recordChildren_def (r : RecordData) :
    recordChildren r = r.closure.children := rfl

def recordKind (r : RecordData) : LocalClosureKind :=
  r.closure.kind

@[simp] theorem recordKind_def (r : RecordData) :
    recordKind r = r.closure.kind := rfl

def recordCylinder (r : RecordData) : Set Support :=
  Cylinder r.pref

@[simp] theorem recordCylinder_def (r : RecordData) :
    recordCylinder r = Cylinder r.pref := rfl

abbrev RecordFamily := List RecordData

structure GlobalCertificate where
  records : RecordFamily

@[simp] theorem globalCertificate_mk_records (rs : RecordFamily) :
    (GlobalCertificate.mk rs).records = rs := rfl

def certificateRecords (C : GlobalCertificate) : RecordFamily :=
  C.records

@[simp] theorem certificateRecords_def (C : GlobalCertificate) :
    certificateRecords C = C.records := rfl

def certificatePrefixes (C : GlobalCertificate) : List Prefix :=
  C.records.map (fun r => r.pref)

@[simp] theorem certificatePrefixes_def (C : GlobalCertificate) :
    certificatePrefixes C = C.records.map (fun r => r.pref) := rfl

end Certificate
end CaseC
end Lehmer