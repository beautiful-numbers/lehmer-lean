-- FILE: Lean/Lehmer/CaseB/TerminalExport.lean
/-
IMPORT CLASSIFICATION
- Lehmer.CaseB.Main : def thm
- Lehmer.CaseB.CaseBClass : def
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.CaseB.Saturation.SaturatedSupportBound : def thm
- Lehmer.CaseB.Saturation.SupplyBound : def thm
- Lehmer.CaseB.Dominance.ClosedMajorantBound : def thm
-/

import Lehmer.CaseB.Main
import Lehmer.CaseB.CaseBClass
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.CaseB.Saturation.SaturatedSupportBound
import Lehmer.CaseB.Saturation.SupplyBound
import Lehmer.CaseB.Dominance.ClosedMajorantBound

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
High-level terminal export for the principal Case B pipeline.

For every Lehmer candidate in the exact Case B class, the main Case B pipeline
canonically produces a closed supply package on the canonical candidate
context.

This is the correct candidate-side export level for downstream terminal bridge
and audit files: they should consume this theorem instead of reconstructing the
low-level routing through explicit generic chains, raw saturated-support bounds,
and closed witness-side majorants.
-/
theorem caseB_supplyPackage_candidate
    {n : ℕ}
    (hL : LehmerComposite n)
    (hB : InCaseB n) :
    ∃ P : SupplyPackage (candidateContext n),
      ClosedWitnessBound P.accounting := by
  let G : GenericChainToSSLock (candidateContext n) :=
    genericChainToSSLock_candidate hL hB
  have hbound :
      supportCard (candidateContext n).S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G) := by
    simpa [G] using
      raw_saturatedSupportBound_of_genericChainToSSLock_candidate hL hB
  have hclosed :
      ClosedWitnessBound
        (witnessAccountingOfGenericChainToSSLock G) := by
    simpa [G] using
      closedWitnessBound_candidate hL hB
  refine ⟨supplyPackage_of_genericChainToSSLock G hbound, ?_⟩
  simpa [supplyPackage_of_genericChainToSSLock, G] using hclosed

end CaseB
end Lehmer