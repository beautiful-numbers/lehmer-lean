-- FILE: Lean/Lehmer/CaseC/BranchData.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseC.Spec : def
- Lehmer.CaseC.Main : assemble
- Lehmer.Pipeline.GlobalSplit : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseC.Spec
import Lehmer.CaseC.Main
import Lehmer.Pipeline.GlobalSplit

namespace Lehmer
namespace CaseC

open Lehmer.Basic
open Lehmer.Pipeline

/--
Constructive reconstruction API for the Case C branch.

This is the minimal honest interface needed to pass from the pipeline-side
predicate `InCaseC n` to the fully assembled mathematical package consumed by
`CaseC.Main`.
-/
structure CaseCReconstruction where
  paramsOf :
    ∀ {n : ℕ}, InCaseC n → Params
  closureOf :
    ∀ {n : ℕ} (hC : InCaseC n), ClosureData (paramsOf hC)
  mainOf :
    ∀ {n : ℕ} (hC : InCaseC n),
      CaseCMainPackage (paramsOf hC) (closureOf hC)

@[simp] theorem CaseCReconstruction.paramsOf_eq
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    R.paramsOf hC = R.paramsOf hC := rfl

@[simp] theorem CaseCReconstruction.closureOf_eq
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    R.closureOf hC = R.closureOf hC := rfl

@[simp] theorem CaseCReconstruction.mainOf_eq
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    R.mainOf hC = R.mainOf hC := rfl

/--
Canonical bundled branch data for a number already known to lie in Case C,
relative to a constructive reconstruction API.
-/
structure BranchData (R : CaseCReconstruction) (n : ℕ) where
  inCaseC : InCaseC n
  params : Params
  closure : ClosureData params
  main : CaseCMainPackage params closure

@[simp] theorem BranchData.inCaseC_mk
    (R : CaseCReconstruction) {n : ℕ}
    (hC : InCaseC n) (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (BranchData.mk hC P D X).inCaseC = hC := rfl

@[simp] theorem BranchData.params_mk
    (R : CaseCReconstruction) {n : ℕ}
    (hC : InCaseC n) (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (BranchData.mk hC P D X).params = P := rfl

@[simp] theorem BranchData.closure_mk
    (R : CaseCReconstruction) {n : ℕ}
    (hC : InCaseC n) (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (BranchData.mk hC P D X).closure = D := rfl

@[simp] theorem BranchData.main_mk
    (R : CaseCReconstruction) {n : ℕ}
    (hC : InCaseC n) (P : Params) (D : ClosureData P)
    (X : CaseCMainPackage P D) :
    (BranchData.mk hC P D X).main = X := rfl

/--
Constructive branch-data builder from `InCaseC n`, using the reconstruction API.
-/
def branchDataOf
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    BranchData R n :=
  BranchData.mk hC (R.paramsOf hC) (R.closureOf hC) (R.mainOf hC)

@[simp] theorem branchDataOf_inCaseC
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    (branchDataOf R hC).inCaseC = hC := rfl

@[simp] theorem branchDataOf_params
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    (branchDataOf R hC).params = R.paramsOf hC := rfl

@[simp] theorem branchDataOf_closure
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    (branchDataOf R hC).closure = R.closureOf hC := rfl

@[simp] theorem branchDataOf_main
    (R : CaseCReconstruction) {n : ℕ} (hC : InCaseC n) :
    (branchDataOf R hC).main = R.mainOf hC := rfl

/--
Projection back to the pipeline-side branch predicate.
-/
theorem BranchData.in_caseC
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    InCaseC n := by
  exact X.inCaseC

/--
The bundled Case C main package carried by branch data is ready in the sense of
the assembled Case C layer.
-/
theorem BranchData.ready
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    CaseCMainReady X.params X.closure X.main := by
  exact caseCMainReady X.params X.closure X.main

/--
The bundled Case C main package yields the branch impossibility theorem.
-/
theorem BranchData.impossible_pointwise
    (R : CaseCReconstruction) {n m : ℕ} (X : BranchData R n)
    (hL : LehmerComposite m) (hC : InCaseC m) :
    False := by
  exact CaseCMainPackage.impossible_pointwise X.params X.closure X.main hL hC

/--
In particular, every Lehmer composite in Case C is excluded by the bundled main
package.
-/
theorem BranchData.not_inCaseC_of_LehmerComposite
    (R : CaseCReconstruction) {n m : ℕ} (X : BranchData R n)
    (hL : LehmerComposite m) :
    ¬ InCaseC m := by
  intro hC
  exact X.impossible_pointwise hL hC

/--
Certificate projection carried by the bundled main package.
-/
def BranchData.certificate
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Certificate.GlobalCertificate :=
  caseCMainCertificate X.params X.closure X.main

@[simp] theorem BranchData.certificate_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.certificate = caseCMainCertificate X.params X.closure X.main := rfl

theorem BranchData.certificate_checked
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Certificate.CertificateMainChecked X.certificate := by
  exact caseCMainCertificate_checked X.params X.closure X.main

theorem BranchData.certificate_sound
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Certificate.GloballySoundCertificate X.certificate := by
  exact caseCMainCertificate_sound X.params X.closure X.main

theorem BranchData.certificate_complete
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Certificate.GloballyCompleteCertificate X.certificate := by
  exact caseCMainCertificate_complete X.params X.closure X.main

theorem BranchData.certificate_coverageReady
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Certificate.CoverageReadyCertificate X.certificate := by
  exact caseCMainCertificate_coverageReady X.params X.closure X.main

theorem BranchData.certificate_mem_sound
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    ∀ r, Certificate.certificateHasRecord X.certificate r →
      Certificate.LocallySoundRecord r := by
  intro r hr
  exact caseCMainCertificate_mem_sound X.params X.closure X.main r hr

theorem BranchData.certificate_mem_complete
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    ∀ r, Certificate.certificateHasRecord X.certificate r →
      Certificate.LocallyCompleteRecord r := by
  intro r hr
  exact caseCMainCertificate_mem_complete X.params X.closure X.main r hr

theorem BranchData.certificate_mem_checked
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    ∀ r, Certificate.certificateHasRecord X.certificate r →
      Certificate.LocallyCheckedRecord r := by
  intro r hr
  exact caseCMainCertificate_mem_checked X.params X.closure X.main r hr

/--
Head record projection for downstream audit consumers.
-/
def BranchData.certificateHead?
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Option Certificate.RecordData :=
  caseCMainCertificateHead? X.params X.closure X.main

@[simp] theorem BranchData.certificateHead?_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.certificateHead? = caseCMainCertificateHead? X.params X.closure X.main := rfl

/--
Readable projection of the gap family carried by the bundled main package.
-/
def BranchData.gapFamily
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    GapClosure.SupportProfileFamily :=
  caseCMainGapFamily X.params X.closure X.main

@[simp] theorem BranchData.gapFamily_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.gapFamily = caseCMainGapFamily X.params X.closure X.main := rfl

theorem BranchData.gapFamily_mem_hasWitness
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    ∀ S, S ∈ X.gapFamily →
      GapClosure.hasNonIntegralityWitness X.params X.closure S := by
  intro S hS
  exact caseCMainGapFamily_mem_hasWitness X.params X.closure X.main S hS

theorem BranchData.gapFamily_mem_rigid
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    ∀ S, S ∈ X.gapFamily →
      GapClosure.RigidProfile X.params X.closure S := by
  intro S hS
  exact caseCMainGapFamily_mem_rigid X.params X.closure X.main S hS

/--
Readable projection of the residual closure package carried by the bundled main
package.
-/
def BranchData.residualClosedState
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    StateMachine.ResidualState X.params X.closure :=
  X.main.residual.state

theorem BranchData.residualClosed
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    StateMachine.ResidualClosed X.params X.closure X.residualClosedState := by
  exact caseCMainResidualClosed X.params X.closure X.main

end CaseC
end Lehmer