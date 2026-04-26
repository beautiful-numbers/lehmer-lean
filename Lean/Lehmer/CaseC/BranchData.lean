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

def BranchData.gapToClosure
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    GapClosure.GapToClosurePackage X.params X.closure :=
  caseCMainGapToClosure X.params X.closure X.main

@[simp] theorem BranchData.gapToClosure_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.gapToClosure = caseCMainGapToClosure X.params X.closure X.main := rfl

def BranchData.gap
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    GapClosure.GapClosurePackage X.params X.closure :=
  caseCMainGap X.params X.closure X.main

@[simp] theorem BranchData.gap_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.gap = caseCMainGap X.params X.closure X.main := rfl

def BranchData.residual
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    StateMachine.ResidualClosurePackage X.params X.closure :=
  caseCMainResidualClosure X.params X.closure X.main

@[simp] theorem BranchData.residual_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.residual = caseCMainResidualClosure X.params X.closure X.main := rfl

def BranchData.residualTerminalContext
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    StateMachine.ResidualTerminalClosureContext X.params X.closure :=
  caseCMainResidualTerminalContext X.params X.closure X.main

@[simp] theorem BranchData.residualTerminalContext_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.residualTerminalContext =
      caseCMainResidualTerminalContext X.params X.closure X.main := rfl

def BranchData.terminalClosureContext
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    CaseCTerminalClosureContext X.params X.closure :=
  caseCMainTerminalClosureContext X.params X.closure X.main

@[simp] theorem BranchData.terminalClosureContext_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.terminalClosureContext =
      caseCMainTerminalClosureContext X.params X.closure X.main := rfl

def BranchData.candidateAdmissibility
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    CaseCCandidateAdmissibilityPackage X.params X.closure :=
  caseCMainCandidateAdmissibility X.params X.closure X.main

@[simp] theorem BranchData.candidateAdmissibility_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.candidateAdmissibility =
      caseCMainCandidateAdmissibility X.params X.closure X.main := rfl

def BranchData.certificateData
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    CaseCCertificateData X.params X.closure :=
  caseCMainCertificateData X.params X.closure X.main

@[simp] theorem BranchData.certificateData_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.certificateData =
      caseCMainCertificateData X.params X.closure X.main := rfl

/--
Certificate projection carried by the bundled main package.
-/
def BranchData.certificate
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Certificate.GlobalCertificate X.params X.closure :=
  caseCMainCertificate X.params X.closure X.main

@[simp] theorem BranchData.certificate_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.certificate = caseCMainCertificate X.params X.closure X.main := rfl

def BranchData.verifiedRecords
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Certificate.VerifiedCertificateRecords X.params X.closure X.certificate :=
  caseCMainVerifiedRecords X.params X.closure X.main

@[simp] theorem BranchData.verifiedRecords_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.verifiedRecords =
      caseCMainVerifiedRecords X.params X.closure X.main := rfl

/--
Head record projection for downstream audit consumers.
-/
def BranchData.certificateHead?
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    Option (Certificate.RecordData X.params X.closure) :=
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

theorem BranchData.gap_ready
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    GapClosure.GapToClosureReady X.params X.closure X.gapToClosure := by
  simpa [BranchData.gapToClosure] using
    caseCMain_gap_ready X.params X.closure X.main

theorem BranchData.omega_lt_width
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    GapClosure.gapClosureOmegahatValue X.params X.closure X.gap <
      width X.params := by
  simpa [BranchData.gap] using
    caseCMain_omega_lt_width X.params X.closure X.main

theorem BranchData.bound_atLeastCap
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    cap X.params X.closure ≤
      GapClosure.gapClosureBoundValue X.params X.closure X.gap := by
  simpa [BranchData.gap] using
    caseCMain_bound_atLeastCap X.params X.closure X.main

theorem BranchData.bound_atLeastClosureN
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.closure.N ≤
      GapClosure.gapClosureBoundValue X.params X.closure X.gap := by
  simpa [BranchData.gap] using
    caseCMain_bound_atLeastClosureN X.params X.closure X.main

/--
Readable projection of the residual closure package carried by the bundled main
package.
-/
def BranchData.residualClosedState
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    StateMachine.ResidualState X.params X.closure :=
  X.residual.state

@[simp] theorem BranchData.residualClosedState_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.residualClosedState = X.residual.state := rfl

theorem BranchData.residualClosed
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    StateMachine.ResidualClosed X.params X.closure X.residualClosedState := by
  simpa [BranchData.residualClosedState, BranchData.residual] using
    caseCMainResidualClosed X.params X.closure X.main

def BranchData.terminalData
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    CaseCTerminalData X.params X.closure :=
  caseCMainTerminalData X.params X.closure X.main

@[simp] theorem BranchData.terminalData_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.terminalData = caseCMainTerminalData X.params X.closure X.main := rfl

/--
The bundled Case C main package yields the branch impossibility theorem.
-/
theorem BranchData.impossible_pointwise
    (R : CaseCReconstruction) {n m : ℕ} (X : BranchData R n)
    (hL : LehmerComposite m) (hC : InCaseC m) :
    False := by
  exact CaseCMainPackage.impossible_pointwise
    X.params X.closure X.main hL hC

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

def BranchData.caseCImpossible
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    CaseCImpossible :=
  caseCMain_impossible X.params X.closure X.main

@[simp] theorem BranchData.caseCImpossible_def
    (R : CaseCReconstruction) {n : ℕ} (X : BranchData R n) :
    X.caseCImpossible = caseCMain_impossible X.params X.closure X.main := rfl

theorem caseCImpossible_of_reconstruction
    (R : CaseCReconstruction) :
    CaseCImpossible := by
  intro n hL hC
  let X : BranchData R n := branchDataOf R hC
  exact BranchData.impossible_pointwise R X hL hC

theorem not_inCaseC_of_LehmerComposite_reconstruction
    (R : CaseCReconstruction) {n : ℕ}
    (hL : LehmerComposite n) :
    ¬ InCaseC n := by
  intro hC
  exact caseCImpossible_of_reconstruction R n hL hC

end CaseC
end Lehmer