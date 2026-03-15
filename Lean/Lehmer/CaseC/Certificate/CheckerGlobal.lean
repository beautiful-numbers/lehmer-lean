-- FILE: Lean/Lehmer/CaseC/Certificate/CheckerGlobal.lean
import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Record
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.CheckerLocal

namespace Lehmer
namespace CaseC
namespace Certificate

/--
Lookup of a record by identifier inside a certificate list.

For MVP-4 this is the basic retrieval mechanism used by the global checker.
-/
def findRecord? (cid : ℕ) : List Record → Option Record
  | [] => none
  | R :: Rs => if recordId R = cid then some R else findRecord? cid Rs

@[simp] theorem findRecord?_nil (cid : ℕ) :
    findRecord? cid [] = none := rfl

@[simp] theorem findRecord?_cons_eq (cid : ℕ) (R : Record) (Rs : List Record)
    (h : recordId R = cid) :
    findRecord? cid (R :: Rs) = some R := by
  simp [findRecord?, h]

@[simp] theorem findRecord?_cons_ne (cid : ℕ) (R : Record) (Rs : List Record)
    (h : recordId R ≠ cid) :
    findRecord? cid (R :: Rs) = findRecord? cid Rs := by
  simp [findRecord?, h]

/--
Resolve a list of child ids into records using a certificate environment.
If one child id is missing, resolution fails.
-/
def resolveChildren? (cert : List Record) : List ℕ → Option (List Record)
  | [] => some []
  | cid :: cids =>
      match findRecord? cid cert, resolveChildren? cert cids with
      | some R, some Rs => some (R :: Rs)
      | _, _ => none

@[simp] theorem resolveChildren?_nil (cert : List Record) :
    resolveChildren? cert [] = some [] := rfl

/--
The local child environment attached to a record inside a certificate.
-/
def localChildren? (cert : List Record) (R : Record) : Option (List Record) :=
  resolveChildren? cert (recordChildren R)

@[simp] theorem localChildren?_def (cert : List Record) (R : Record) :
    localChildren? cert R = resolveChildren? cert (recordChildren R) := rfl

/--
Boolean global check for a single record against a certificate environment.
It succeeds iff the child references can be resolved and the local checker
accepts the resulting child list.
-/
def checkRecordGlobal (cert : List Record) (R : Record) : Bool :=
  match localChildren? cert R with
  | some children => checkRecordLocal R children
  | none => false

/--
Boolean global checker for an entire certificate list.
-/
def checkCertificate : List Record → Bool
  | [] => true
  | R :: Rs => checkRecordGlobal (R :: Rs) R && checkCertificate Rs

@[simp] theorem checkRecordGlobal_none (cert : List Record) (R : Record)
    (h : localChildren? cert R = none) :
    checkRecordGlobal cert R = false := by
  unfold checkRecordGlobal
  rw [h]

@[simp] theorem checkRecordGlobal_some (cert : List Record) (R : Record)
    (children : List Record)
    (h : localChildren? cert R = some children) :
    checkRecordGlobal cert R = checkRecordLocal R children := by
  unfold checkRecordGlobal
  rw [h]

@[simp] theorem checkCertificate_nil :
    checkCertificate [] = true := rfl

@[simp] theorem checkCertificate_cons (R : Record) (Rs : List Record) :
    checkCertificate (R :: Rs) =
      (checkRecordGlobal (R :: Rs) R && checkCertificate Rs) := rfl

/--
A certificate is locally coherent if each record is well-covered by the
children resolved from the ambient certificate list.
-/
def GloballyCoherent : List Record → Prop
  | [] => True
  | R :: Rs =>
      (∃ children, localChildren? (R :: Rs) R = some children ∧ WellCovered R children)
        ∧ GloballyCoherent Rs

@[simp] theorem GloballyCoherent_nil :
    GloballyCoherent [] := by
  trivial

@[simp] theorem GloballyCoherent_cons (R : Record) (Rs : List Record) :
    GloballyCoherent (R :: Rs) ↔
      (∃ children, localChildren? (R :: Rs) R = some children ∧ WellCovered R children)
        ∧ GloballyCoherent Rs := by
  rfl

/--
If a record has no children, then resolving its children succeeds with the
empty list.
-/
theorem localChildren?_nil_of_no_children
    (cert : List Record) (R : Record)
    (h : recordChildren R = []) :
    localChildren? cert R = some [] := by
  simp [localChildren?, h]

/--
A terminal record with no children passes the global check in any environment
where its children resolve trivially.
-/
theorem checkRecordGlobal_terminal_nil
    (cert : List Record)
    (i : ℕ) (g : Guard) (p : Priority) (j : Justification) (m : Measure) :
    checkRecordGlobal cert
      { id := i
        data :=
          { kind := NodeKind.terminal
            guard := g
            priority := p
            children := []
            justification := j
            measure := m } } = true := by
  simp [checkRecordGlobal, localChildren?, resolveChildren?, checkRecordLocal,
    checkRecordShape, checkFormat, checkLocalChildren, checkPrioritySorted]

/--
Stable MVP-4 placeholder: a globally coherent certificate should be accepted by
the global checker.
-/
theorem checkCertificate_true_placeholder
    (cert : List Record)
    (h : GloballyCoherent cert) :
    checkCertificate cert = true := by
  sorry

end Certificate
end CaseC
end Lehmer