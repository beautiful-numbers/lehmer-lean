-- FILE: Lean/Lehmer/CaseC/Certificate/SoundnessGlobal.lean
import Lehmer.Prelude
import Lehmer.CaseC.Certificate.Coverage
import Lehmer.CaseC.Certificate.CheckerGlobal
import Lehmer.CaseC.Certificate.SoundnessLocal

namespace Lehmer
namespace CaseC
namespace Certificate

/--
A semantic global-validity predicate for a certificate list.

For MVP-4, global validity is stated recursively:
- each head record resolves to a child list,
- that local instance is semantically valid,
- and the tail is globally valid.
-/
def ValidCertificate : List Record → Prop
  | [] => True
  | R :: Rs =>
      (∃ children,
        localChildren? (R :: Rs) R = some children ∧
        ValidLocalRecord R children) ∧
      ValidCertificate Rs

@[simp] theorem ValidCertificate_nil :
    ValidCertificate [] := by
  trivial

@[simp] theorem ValidCertificate_cons (R : Record) (Rs : List Record) :
    ValidCertificate (R :: Rs) ↔
      (∃ children,
        localChildren? (R :: Rs) R = some children ∧
        ValidLocalRecord R children) ∧
      ValidCertificate Rs := by
  rfl

/--
If the global checker succeeds on a head record because its children resolve
to `children`, and the local checker is sound, then the head record is
semantically valid.
-/
theorem checkRecordGlobal_sound_of_resolved
    (cert : List Record) (R : Record) (children : List Record)
    (hres : localChildren? cert R = some children)
    (hchk : checkRecordGlobal cert R = true) :
    ValidLocalRecord R children := by
  have hlocal : checkRecordLocal R children = true := by
    rw [checkRecordGlobal_some cert R children hres] at hchk
    exact hchk
  exact checkRecordLocal_sound R children hlocal

/--
Stable MVP-4 placeholder: if the global checker accepts a nonempty certificate,
then the head record's children can be resolved.
-/
theorem checkCertificate_head_resolves_placeholder
    (R : Record) (Rs : List Record)
    (h : checkCertificate (R :: Rs) = true) :
    ∃ children, localChildren? (R :: Rs) R = some children := by
  sorry

/--
Main global soundness theorem for MVP-4:
if the global checker returns `true`, then the certificate is semantically valid.
-/
theorem checkCertificate_sound : ∀ cert : List Record,
    checkCertificate cert = true → ValidCertificate cert
  | [] , _ => by
      simp [ValidCertificate]
  | R :: Rs, h => by
      have hsplit : checkRecordGlobal (R :: Rs) R = true ∧ checkCertificate Rs = true := by
        simpa [checkCertificate] using h
      rcases checkCertificate_head_resolves_placeholder R Rs h with ⟨children, hres⟩
      refine ⟨?_, ?_⟩
      · refine ⟨children, hres, ?_⟩
        exact checkRecordGlobal_sound_of_resolved (R :: Rs) R children hres hsplit.1
      · exact checkCertificate_sound Rs hsplit.2

/--
A globally coherent certificate is semantically valid once the global checker
is known to accept it.
-/
theorem globallyCoherent_implies_valid_of_checker
    (cert : List Record)
    (_hcoh : GloballyCoherent cert)
    (hchk : checkCertificate cert = true) :
    ValidCertificate cert := by
  exact checkCertificate_sound cert hchk

end Certificate
end CaseC
end Lehmer