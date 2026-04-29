-- FILE: Lean/Lehmer/Audit-axle/Audit_proof/CaseC/KmaxGap.proof.lean
import Mathlib

def CaseCKmaxGapAuditReconstructible
    (InCaseC : Nat -> Prop)
    (AuditCaseCKmaxGapReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    {n : Nat}
    (hC : InCaseC n) :
    Prop :=
  Nonempty (AuditCaseCKmaxGapReconstruction hC)

theorem caseCKmaxGapAuditRouting_sound
    (Params : Type)
    (ClosureData : Params -> Type)
    (KmaxGapPackage : forall P : Params, ClosureData P -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (routing_package :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> KmaxGapPackage P D)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D) :
    Exists fun _X : KmaxGapPackage P D => True := by
  exact Exists.intro (routing_package R) True.intro

theorem exists_caseCKmaxGapAuditRouting_of_inCaseC
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (AuditCaseCKmaxGapReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCKmaxGapAuditRouting_of_inCaseC :
      forall {n : Nat}
        (hC : InCaseC n)
        (R : AuditCaseCKmaxGapReconstruction hC),
        Routing
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    {n : Nat}
    (hC : InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    Exists fun _T :
      Routing
        (auditCaseCParamsOf hC)
        (auditCaseCClosureDataOf hC) => True := by
  exact Exists.intro
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)
    True.intro

namespace CaseCKmaxGapAuditRouting

theorem gapValue_pos
    (Params : Type)
    (ClosureData : Params -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (routing_gapValue :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> Rat)
    (routing_gapValue_positive :
      forall {P : Params} {D : ClosureData P}
        (R : Routing P D),
        0 < routing_gapValue R)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D) :
    0 < routing_gapValue R := by
  exact routing_gapValue_positive R

theorem kmaxValue_pos
    (Params : Type)
    (ClosureData : Params -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (routing_kmaxValue :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> Rat)
    (routing_kmaxValue_positive :
      forall {P : Params} {D : ClosureData P}
        (R : Routing P D),
        0 < routing_kmaxValue R)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D) :
    0 < routing_kmaxValue R := by
  exact routing_kmaxValue_positive R

theorem closureCapValue_pos
    (Params : Type)
    (ClosureData : Params -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (routing_closureCapValue :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> Nat)
    (routing_closureCapValue_positive :
      forall {P : Params} {D : ClosureData P}
        (R : Routing P D),
        0 < routing_closureCapValue R)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D) :
    0 < routing_closureCapValue R := by
  exact routing_closureCapValue_positive R

theorem mem_hasWitness
    (Params : Type)
    (ClosureData : Params -> Type)
    (KmaxGapPackage : forall P : Params, ClosureData P -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (SupportProfile : Type)
    (routing_package :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> KmaxGapPackage P D)
    (routing_family :
      forall {P : Params} {D : ClosureData P},
        KmaxGapPackage P D -> SupportProfile -> Prop)
    (hasNonIntegralityWitness :
      forall (P : Params) (D : ClosureData P),
        SupportProfile -> Prop)
    (routing_mem_hasWitness :
      forall {P : Params} {D : ClosureData P}
        (R : Routing P D)
        (S : SupportProfile),
        routing_family (routing_package R) S ->
        hasNonIntegralityWitness P D S)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D) :
    forall S : SupportProfile,
      routing_family (routing_package R) S ->
      hasNonIntegralityWitness P D S := by
  intro S hS
  exact routing_mem_hasWitness R S hS

def mem_rigid
    (Params : Type)
    (ClosureData : Params -> Type)
    (KmaxGapPackage : forall P : Params, ClosureData P -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (SupportProfile : Type)
    (routing_package :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> KmaxGapPackage P D)
    (routing_family :
      forall {P : Params} {D : ClosureData P},
        KmaxGapPackage P D -> SupportProfile -> Prop)
    (RigidProfile :
      forall (P : Params) (D : ClosureData P),
        SupportProfile -> Prop)
    (routing_mem_rigid :
      forall {P : Params} {D : ClosureData P}
        (R : Routing P D)
        (S : SupportProfile),
        routing_family (routing_package R) S ->
        RigidProfile P D S)
    (P : Params)
    (D : ClosureData P)
    (R : Routing P D) :
    forall S : SupportProfile,
      routing_family (routing_package R) S ->
      RigidProfile P D S := by
  intro S hS
  exact routing_mem_rigid R S hS

end CaseCKmaxGapAuditRouting

theorem caseCKmaxGapAuditRouting_of_inCaseC_gapValue_pos
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (AuditCaseCKmaxGapReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCKmaxGapAuditRouting_of_inCaseC :
      forall {n : Nat}
        (hC : InCaseC n)
        (R : AuditCaseCKmaxGapReconstruction hC),
        Routing
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    (routing_gapValue :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> Rat)
    (routing_gapValue_positive :
      forall {P : Params} {D : ClosureData P}
        (T : Routing P D),
        0 < routing_gapValue T)
    {n : Nat}
    (hC : InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 < routing_gapValue (caseCKmaxGapAuditRouting_of_inCaseC hC R) := by
  exact routing_gapValue_positive
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

theorem caseCKmaxGapAuditRouting_of_inCaseC_kmaxValue_pos
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (AuditCaseCKmaxGapReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCKmaxGapAuditRouting_of_inCaseC :
      forall {n : Nat}
        (hC : InCaseC n)
        (R : AuditCaseCKmaxGapReconstruction hC),
        Routing
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    (routing_kmaxValue :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> Rat)
    (routing_kmaxValue_positive :
      forall {P : Params} {D : ClosureData P}
        (T : Routing P D),
        0 < routing_kmaxValue T)
    {n : Nat}
    (hC : InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 < routing_kmaxValue (caseCKmaxGapAuditRouting_of_inCaseC hC R) := by
  exact routing_kmaxValue_positive
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

theorem caseCKmaxGapAuditRouting_of_inCaseC_closureCapValue_pos
    (Params : Type)
    (ClosureData : Params -> Type)
    (InCaseC : Nat -> Prop)
    (AuditCaseCKmaxGapReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    (Routing : forall P : Params, ClosureData P -> Type)
    (auditCaseCParamsOf :
      forall {n : Nat}, InCaseC n -> Params)
    (auditCaseCClosureDataOf :
      forall {n : Nat} (hC : InCaseC n),
        ClosureData (auditCaseCParamsOf hC))
    (caseCKmaxGapAuditRouting_of_inCaseC :
      forall {n : Nat}
        (hC : InCaseC n)
        (R : AuditCaseCKmaxGapReconstruction hC),
        Routing
          (auditCaseCParamsOf hC)
          (auditCaseCClosureDataOf hC))
    (routing_closureCapValue :
      forall {P : Params} {D : ClosureData P},
        Routing P D -> Nat)
    (routing_closureCapValue_positive :
      forall {P : Params} {D : ClosureData P}
        (T : Routing P D),
        0 < routing_closureCapValue T)
    {n : Nat}
    (hC : InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    0 < routing_closureCapValue (caseCKmaxGapAuditRouting_of_inCaseC hC R) := by
  exact routing_closureCapValue_positive
    (caseCKmaxGapAuditRouting_of_inCaseC hC R)

theorem caseCKmaxGapAuditReconstructible_of
    (InCaseC : Nat -> Prop)
    (AuditCaseCKmaxGapReconstruction :
      forall {n : Nat}, InCaseC n -> Type)
    {n : Nat}
    (hC : InCaseC n)
    (R : AuditCaseCKmaxGapReconstruction hC) :
    CaseCKmaxGapAuditReconstructible
      InCaseC
      AuditCaseCKmaxGapReconstruction
      hC := by
  exact Nonempty.intro R