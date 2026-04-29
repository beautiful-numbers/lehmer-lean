-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseC/GapClosure.proof.lean
import Mathlib

def AuditCaseCGapClosureReconstructible
    (InCaseC : Nat -> Prop)
    (AuditCaseCGapClosureReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    {n : Nat}
    (hC : InCaseC n) :
    Prop :=
  Nonempty (AuditCaseCGapClosureReconstruction hC)

def AuditCaseCGapClosureReady
    (InCaseC : Nat -> Prop)
    (AuditCaseCGapClosureReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (Ready :
      forall {n : Nat} {hC : InCaseC n},
        AuditCaseCGapClosureReconstruction hC -> Prop)
    {n : Nat}
    (hC : InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    Prop :=
  Ready X

theorem auditCaseCGapClosureReconstructible_of
    (InCaseC : Nat -> Prop)
    (AuditCaseCGapClosureReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    {n : Nat}
    (hC : InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    AuditCaseCGapClosureReconstructible
      InCaseC
      AuditCaseCGapClosureReconstruction
      hC := by
  exact Nonempty.intro X

theorem auditCaseCGapClosureReady
    (InCaseC : Nat -> Prop)
    (AuditCaseCGapClosureReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (Ready :
      forall {n : Nat} {hC : InCaseC n},
        AuditCaseCGapClosureReconstruction hC -> Prop)
    (ready_of_reconstruction :
      forall {n : Nat} {hC : InCaseC n}
        (X : AuditCaseCGapClosureReconstruction hC),
        Ready X)
    {n : Nat}
    (hC : InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    AuditCaseCGapClosureReady
      InCaseC
      AuditCaseCGapClosureReconstruction
      Ready
      hC
      X := by
  exact ready_of_reconstruction X

theorem auditCaseCGapClosureDataOf_ready
    (InCaseC : Nat -> Prop)
    (AuditCaseCGapClosureReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (AuditCaseCGapClosureData : Nat -> Type)
    (DataReady : forall {n : Nat}, AuditCaseCGapClosureData n -> Prop)
    (auditCaseCGapClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        AuditCaseCGapClosureReconstruction hC ->
        AuditCaseCGapClosureData n)
    (ready_of_data :
      forall {n : Nat} {hC : InCaseC n}
        (X : AuditCaseCGapClosureReconstruction hC),
        DataReady (auditCaseCGapClosureDataOf hC X))
    {n : Nat}
    (hC : InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    DataReady (auditCaseCGapClosureDataOf hC X) := by
  exact ready_of_data X

theorem caseCGapClosureAuditRouting_sound
    (Params : Type)
    (ClosureData : Params -> Type)
    (GapToClosurePackage : forall P : Params, ClosureData P -> Type)
    (CaseCGapClosureAuditRouting :
      forall P : Params, ClosureData P -> Type)
    (routing_package :
      forall {P : Params} {D : ClosureData P},
        CaseCGapClosureAuditRouting P D ->
        GapToClosurePackage P D)
    (P : Params)
    (D : ClosureData P)
    (X : CaseCGapClosureAuditRouting P D) :
    Exists fun _G : GapToClosurePackage P D => True := by
  exact Exists.intro (routing_package X) True.intro

theorem exists_caseCGapClosureAuditRouting_of_inCaseC
    (Params : Type)
    (ClosureData : Params -> Type)
    (GapToClosurePackage : forall P : Params, ClosureData P -> Type)
    (CaseCGapClosureAuditRouting :
      forall P : Params, ClosureData P -> Type)
    (InCaseC : Nat -> Prop)
    (AuditCaseCGapClosureReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCGapClosureAuditRouting_of_inCaseC :
      forall {n : Nat}
        (hC : InCaseC n)
        (X : AuditCaseCGapClosureReconstruction hC),
        CaseCGapClosureAuditRouting
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    {n : Nat}
    (hC : InCaseC n)
    (X : AuditCaseCGapClosureReconstruction hC) :
    Exists fun _R :
      CaseCGapClosureAuditRouting
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) => True := by
  exact Exists.intro
    (caseCGapClosureAuditRouting_of_inCaseC hC X)
    True.intro