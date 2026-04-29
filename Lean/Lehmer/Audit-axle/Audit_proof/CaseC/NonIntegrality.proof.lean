-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseC/NonIntegrality.proof.lean
import Mathlib

theorem caseCNonIntegralityAuditRouting_sound
    (Params : Type)
    (ClosureData : Params -> Type)
    (NonIntegralityFamilyPackage : forall P : Params, ClosureData P -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (routing_package :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> NonIntegralityFamilyPackage P D)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D) :
    Exists fun _X : NonIntegralityFamilyPackage P D => True := by
  exact Exists.intro (routing_package R) True.intro

theorem exists_caseCNonIntegralityAuditRouting_of_inCaseC
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (Routing : forall P : Params, ClosureData P -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCNonIntegralityAuditRouting_of_inCaseC :
      forall {n : Nat} (hC : InCaseC n),
        Routing
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    {n : Nat}
    (hC : InCaseC n) :
    Exists fun _R :
      Routing
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) => True := by
  exact Exists.intro
    (caseCNonIntegralityAuditRouting_of_inCaseC hC)
    True.intro

namespace CaseCNonIntegralityAuditRouting

theorem mem_hasWitness
    (Params : Type)
    (ClosureData : Params -> Type)
    (NonIntegralityFamilyPackage : forall P : Params, ClosureData P -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (SupportProfile : Type)
    (routing_package :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> NonIntegralityFamilyPackage P D)
    (routing_family :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> SupportProfile -> Prop)
    (hasNonIntegralityWitness :
      forall (P : Params) (D : ClosureData P),
        SupportProfile -> Prop)
    (package_mem_hasWitness :
      forall {P : Params} {D : ClosureData P}
        (R : Routing P D)
        (S : SupportProfile),
        routing_family R S ->
        hasNonIntegralityWitness P D S)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D)
    (S : SupportProfile)
    (hS : routing_family R S) :
    hasNonIntegralityWitness P D S := by
  exact package_mem_hasWitness R S hS

end CaseCNonIntegralityAuditRouting

theorem caseCNonIntegralityAuditRouting_of_inCaseC_mem_hasWitness
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (Routing : forall P : Params, ClosureData P -> Type)
    (SupportProfile : Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCNonIntegralityAuditRouting_of_inCaseC :
      forall {n : Nat} (hC : InCaseC n),
        Routing
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    (routing_family :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> SupportProfile -> Prop)
    (hasNonIntegralityWitness :
      forall (P : Params) (D : ClosureData P),
        SupportProfile -> Prop)
    (routing_mem_hasWitness :
      forall {P : Params} {D : ClosureData P}
        (R : Routing P D)
        (S : SupportProfile),
        routing_family R S ->
        hasNonIntegralityWitness P D S)
    {n : Nat}
    (hC : InCaseC n)
    (S : SupportProfile)
    (hS :
      routing_family
        (caseCNonIntegralityAuditRouting_of_inCaseC hC)
        S) :
    hasNonIntegralityWitness
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC)
      S := by
  exact routing_mem_hasWitness
    (caseCNonIntegralityAuditRouting_of_inCaseC hC)
    S
    hS

def CaseCNonIntegralityAuditAvailable
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (Routing : forall P : Params, ClosureData P -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    {n : Nat}
    (hC : InCaseC n) :
    Prop :=
  Nonempty
    (Routing
      (auditCaseCParamsOf hC)
      (auditCaseCClosureDataOf hC))

theorem caseCNonIntegralityAuditAvailable
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (Routing : forall P : Params, ClosureData P -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCNonIntegralityAuditRouting_of_inCaseC :
      forall {n : Nat} (hC : InCaseC n),
        Routing
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    {n : Nat}
    (hC : InCaseC n) :
    CaseCNonIntegralityAuditAvailable
      Params
      ClosureData
      InCaseC
      Routing
      auditCaseCParamsOf
      auditCaseCClosureDataOf
      hC := by
  exact Nonempty.intro
    (caseCNonIntegralityAuditRouting_of_inCaseC hC)