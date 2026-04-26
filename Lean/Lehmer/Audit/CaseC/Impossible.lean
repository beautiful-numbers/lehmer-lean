-- FILE: Lean/Lehmer/Audit/CaseC/Impossible.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Main : assemble
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Main

namespace Lehmer
namespace Audit
namespace CaseC

structure AuditCaseCImpossibleData
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P) where
  main : Lehmer.CaseC.CaseCMainPackage P D

@[simp] theorem AuditCaseCImpossibleData.main_mk
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (AuditCaseCImpossibleData.mk X).main = X := rfl

def auditCaseCImpossibleOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    Lehmer.CaseC.CaseCMainPackage P D :=
  X

@[simp] theorem auditCaseCImpossibleOf_eq
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    auditCaseCImpossibleOf P D X = X := rfl

def auditCaseCImpossibleDataOf
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    AuditCaseCImpossibleData P D :=
  AuditCaseCImpossibleData.mk X

@[simp] theorem auditCaseCImpossibleDataOf_main
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (auditCaseCImpossibleDataOf P D X).main = X := rfl

def AuditCaseCImpossibleData.package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCImpossibleData P D) :
    Lehmer.CaseC.CaseCMainPackage P D :=
  X.main

@[simp] theorem AuditCaseCImpossibleData.package_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCImpossibleData P D) :
    X.package = X.main := rfl

def AuditCaseCImpossibleData.impossible
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCImpossibleData P D) : Prop :=
  Lehmer.CaseC.CaseCImpossible

@[simp] theorem AuditCaseCImpossibleData.impossible_def
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCImpossibleData P D) :
    X.impossible = Lehmer.CaseC.CaseCImpossible := rfl

theorem AuditCaseCImpossibleData.package_impossible
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCImpossibleData P D) :
    Lehmer.CaseC.CaseCImpossible := by
  exact X.package.impossible

theorem AuditCaseCImpossibleData.impossible_pointwise
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCImpossibleData P D)
    {n : ℕ} (hL : Lehmer.Basic.LehmerComposite n) (hC : Lehmer.Pipeline.InCaseC n) :
    False := by
  exact Lehmer.CaseC.CaseCMainPackage.impossible_pointwise P D X.package hL hC

theorem AuditCaseCImpossibleData.not_inCaseC_of_LehmerComposite
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : AuditCaseCImpossibleData P D)
    {n : ℕ} (hL : Lehmer.Basic.LehmerComposite n) :
    ¬ Lehmer.Pipeline.InCaseC n := by
  exact Lehmer.CaseC.CaseCMainPackage.not_inCaseC_of_LehmerComposite P D X.package hL

theorem auditCaseCImpossibleOf_pointwise
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D)
    {n : ℕ} (hL : Lehmer.Basic.LehmerComposite n) (hC : Lehmer.Pipeline.InCaseC n) :
    False := by
  exact Lehmer.CaseC.caseC_impossible_from_package P D X hL hC

theorem auditCaseCImpossibleOf_not_inCaseC
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D)
    {n : ℕ} (hL : Lehmer.Basic.LehmerComposite n) :
    ¬ Lehmer.Pipeline.InCaseC n := by
  exact Lehmer.CaseC.not_inCaseC_of_LehmerComposite_from_package P D X hL

@[simp] theorem auditCaseCImpossibleDataOf_package
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D) :
    (auditCaseCImpossibleDataOf P D X).package = X := rfl

theorem auditCaseCImpossibleDataOf_pointwise
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D)
    {n : ℕ} (hL : Lehmer.Basic.LehmerComposite n) (hC : Lehmer.Pipeline.InCaseC n) :
    False := by
  exact auditCaseCImpossibleOf_pointwise P D X hL hC

theorem auditCaseCImpossibleDataOf_not_inCaseC
    (P : Lehmer.CaseC.Params) (D : Lehmer.CaseC.ClosureData P)
    (X : Lehmer.CaseC.CaseCMainPackage P D)
    {n : ℕ} (hL : Lehmer.Basic.LehmerComposite n) :
    ¬ Lehmer.Pipeline.InCaseC n := by
  exact auditCaseCImpossibleOf_not_inCaseC P D X hL

end CaseC
end Audit
end Lehmer