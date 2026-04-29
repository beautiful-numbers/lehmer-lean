-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseC/Certificate.proof.lean
import Mathlib

def CaseCCertificateAuditAvailable
    (Params : Type)
    (ClosureData : Params -> Type)
    (CertificateMainPackage : forall P : Params, ClosureData P -> Type)
    (CaseCCertificateAuditRouting :
      forall P : Params, ClosureData P -> Type)
    (InCaseC : Nat -> Prop)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    {n : Nat}
    (hC : InCaseC n) :
    Prop :=
  Nonempty
    (CaseCCertificateAuditRouting
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

theorem caseCCertificateAuditRouting_sound
    (Params : Type)
    (ClosureData : Params -> Type)
    (CertificateMainPackage : forall P : Params, ClosureData P -> Type)
    (CaseCCertificateAuditRouting :
      forall P : Params, ClosureData P -> Type)
    (routing_package :
      forall {P : Params} {D : ClosureData P},
        CaseCCertificateAuditRouting P D ->
        CertificateMainPackage P D)
    (P : Params)
    (D : ClosureData P)
    (R : CaseCCertificateAuditRouting P D) :
    Exists fun _C : CertificateMainPackage P D => True := by
  exact Exists.intro (routing_package R) True.intro

theorem exists_caseCCertificateAuditRouting_of_inCaseC
    (Params : Type)
    (ClosureData : Params -> Type)
    (CertificateMainPackage : forall P : Params, ClosureData P -> Type)
    (CaseCCertificateAuditRouting :
      forall P : Params, ClosureData P -> Type)
    (InCaseC : Nat -> Prop)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCCertificateAuditRouting_of_inCaseC :
      forall {n : Nat}
        (hC : InCaseC n)
        (X :
          CertificateMainPackage
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)),
        CaseCCertificateAuditRouting
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    {n : Nat}
    (hC : InCaseC n)
    (X :
      CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    Exists fun _R :
      CaseCCertificateAuditRouting
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) => True := by
  exact Exists.intro
    (caseCCertificateAuditRouting_of_inCaseC hC X)
    True.intro

theorem caseCCertificateAuditAvailable_of_package
    (Params : Type)
    (ClosureData : Params -> Type)
    (CertificateMainPackage : forall P : Params, ClosureData P -> Type)
    (CaseCCertificateAuditRouting :
      forall P : Params, ClosureData P -> Type)
    (InCaseC : Nat -> Prop)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCCertificateAuditRouting_of_inCaseC :
      forall {n : Nat}
        (hC : InCaseC n)
        (X :
          CertificateMainPackage
            (auditCaseCParamsOf hC)
            (auditCaseCClosureDataOf hC)),
        CaseCCertificateAuditRouting
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    {n : Nat}
    (hC : InCaseC n)
    (X :
      CertificateMainPackage
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC)) :
    CaseCCertificateAuditAvailable
      Params
      ClosureData
      CertificateMainPackage
      CaseCCertificateAuditRouting
      InCaseC
      auditCaseCParamsOf
      auditCaseCClosureDataOf
      hC := by
  exact Nonempty.intro
    (caseCCertificateAuditRouting_of_inCaseC hC X)