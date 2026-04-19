-- FILE: Lean/Lehmer/CaseB/Saturation/SupplyBound.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Parameters : def
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
- Lehmer.CaseB.Saturation.GenericChains : def thm
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
- Lehmer.CaseB.Saturation.SSLock : def thm
- Lehmer.CaseB.Saturation.EntanglementScarcity : def thm
- Lehmer.CaseB.Saturation.SaturatedSupportBound : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Parameters
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.GenericChains
import Lehmer.CaseB.Saturation.WitnessAccounting
import Lehmer.CaseB.Saturation.SSLock
import Lehmer.CaseB.Saturation.EntanglementScarcity
import Lehmer.CaseB.Saturation.SaturatedSupportBound

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Paper-style scarcity bound `W(y)` for terminal `ε_B`-saturated supports.

At the present stage, this is represented abstractly by a witness-budget-side
parameter. The later dominance layer will replace this with a closed-form
majorant.
-/
def Wbound (_y : ℕ) (w : ℕ) : ℕ :=
  w

@[simp] theorem Wbound_def (y w : ℕ) :
    Wbound y w = w := rfl

/--
Paper-style global Case B support bound:
`M(y) = W(y) + Kmax,B(y)`.
-/
noncomputable def Mbound (y : ℕ) (w : ℕ) : ℕ :=
  Wbound y w + KmaxB y

@[simp] theorem Mbound_def (y w : ℕ) :
    Mbound y w = Wbound y w + KmaxB y := rfl

/--
Expanded form of `M(y)` with the current abstract `W(y)` interface.
-/
theorem Mbound_eq (y w : ℕ) :
    Mbound y w = w + KmaxB y := by
  simp [Mbound, Wbound]

/--
Witness-budget-specialized `W(y)` attached to a witness accounting datum.
-/
noncomputable def WboundOfAccounting {C : Context} (A : WitnessAccounting C) : ℕ :=
  Wbound C.y (witnessBudget A)

@[simp] theorem WboundOfAccounting_def {C : Context} (A : WitnessAccounting C) :
    WboundOfAccounting A = Wbound C.y (witnessBudget A) := rfl

/--
Witness-budget-specialized `M(y)` attached to a witness accounting datum.
-/
noncomputable def MboundOfAccounting {C : Context} (A : WitnessAccounting C) : ℕ :=
  Mbound C.y (witnessBudget A)

@[simp] theorem MboundOfAccounting_def {C : Context} (A : WitnessAccounting C) :
    MboundOfAccounting A = Mbound C.y (witnessBudget A) := rfl

/--
Expanded accounting form:
`M = witnessBudget + KmaxB`.
-/
theorem MboundOfAccounting_eq {C : Context} (A : WitnessAccounting C) :
    MboundOfAccounting A = witnessBudget A + KmaxB C.y := by
  simp [MboundOfAccounting, Mbound, Wbound]

/--
The terminal witness-side scarcity estimate.

At the current stage this says exactly that the entangled-witness budget is
bounded by the abstract witness-side majorant `W(y)`.
-/
def HasScarcityBound (C : Context) (A : WitnessAccounting C) : Prop :=
  witnessBudget A ≤ WboundOfAccounting A

@[simp] theorem HasScarcityBound_def (C : Context) (A : WitnessAccounting C) :
    HasScarcityBound C A = (witnessBudget A ≤ WboundOfAccounting A) := rfl

/--
The paper-style Case B supply bound on a support.
-/
def HasSupplyBound (C : Context) (A : WitnessAccounting C) : Prop :=
  supportCard C.S ≤ MboundOfAccounting A

@[simp] theorem HasSupplyBound_def (C : Context) (A : WitnessAccounting C) :
    HasSupplyBound C A = (supportCard C.S ≤ MboundOfAccounting A) := rfl

/--
`W(y)` is bounded by `M(y)`.
-/
theorem Wbound_le_Mbound (y w : ℕ) :
    Wbound y w ≤ Mbound y w := by
  rw [Mbound_eq, Wbound_def]
  exact Nat.le_add_right _ _

/--
`KmaxB(y)` is bounded by `M(y)`.
-/
theorem KmaxB_le_Mbound (y w : ℕ) :
    KmaxB y ≤ Mbound y w := by
  rw [Mbound_eq]
  exact Nat.le_add_left _ _

/--
The current abstract witness budget satisfies the abstract scarcity estimate.
-/
theorem hasScarcityBound_of_accounting
    (C : Context) (A : WitnessAccounting C) :
    HasScarcityBound C A := by
  simp [HasScarcityBound_def, WboundOfAccounting_def, Wbound_def]

/--
Core transport lemma:
the accounting-based saturated-support bound immediately implies the
accounting-based `M` bound, because both expand to the same numerical majorant.
-/
theorem supportCard_le_Mbound_of_accounting
    (C : Context) (A : WitnessAccounting C)
    (hbound : supportCard C.S ≤ saturatedSupportBoundOfAccounting A) :
    supportCard C.S ≤ MboundOfAccounting A := by
  simpa [saturatedSupportBoundOfAccounting_eq, MboundOfAccounting_eq, witnessBudget_def] using hbound

/--
A scarcity bound immediately yields the paper-style supply bound once one also
has the descent-budget contribution available through the accounting-based
majorant.
-/
theorem hasSupplyBound_of_hasScarcityBound
    (C : Context) (A : WitnessAccounting C)
    (_hscarce : HasScarcityBound C A)
    (hbound : supportCard C.S ≤ saturatedSupportBoundOfAccounting A) :
    HasSupplyBound C A := by
  exact supportCard_le_Mbound_of_accounting C A hbound

/--
Support-bounded witness accounting gives the canonical witness-side scarcity
estimate.
-/
theorem witnessBudget_is_scarce {C : Context} (A : WitnessAccounting C) :
    HasScarcityBound C A := by
  exact hasScarcityBound_of_accounting C A

/--
If a support satisfies the explicit saturated-support bound, then it satisfies
the paper-style supply bound.
-/
theorem hasSupplyBound_of_saturatedSupportBound
    (C : Context) (A : WitnessAccounting C)
    (hbound : HasSaturatedSupportBound C A) :
    HasSupplyBound C A := by
  exact supportCard_le_Mbound_of_accounting C A hbound

/--
A generic chain to lock induces the paper-style supply bound on its initial
context whenever the corresponding saturated-support bound has been established
for the induced accounting datum.

Note: `witnessAccountingOfGenericChainToSSLock G` is an accounting datum on the
initial context of the chain, not on the terminal context.
-/
theorem supplyBound_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    HasSupplyBound C (witnessAccountingOfGenericChainToSSLock G) := by
  exact supportCard_le_Mbound_of_accounting
    C
    (witnessAccountingOfGenericChainToSSLock G)
    hbound

/--
Expanded supply inequality for the initial context of a generic chain to lock.
-/
theorem supportCard_le_Mbound_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    supportCard C.S ≤
      MboundOfAccounting (witnessAccountingOfGenericChainToSSLock G) := by
  exact supportCard_le_Mbound_of_accounting
    C
    (witnessAccountingOfGenericChainToSSLock G)
    hbound

/--
The accounting-specialized `M(y)` induced by a generic chain to lock expands as
`witnessBudget + KmaxB`.
-/
theorem MboundOf_genericChainToSSLock_eq
    {C : Context} (G : GenericChainToSSLock C) :
    MboundOfAccounting (witnessAccountingOfGenericChainToSSLock G) =
      witnessBudget (witnessAccountingOfGenericChainToSSLock G) + KmaxB C.y := by
  exact MboundOfAccounting_eq (witnessAccountingOfGenericChainToSSLock G)

/--
Honest cumulative witness-side scarcity bound.
-/
noncomputable def cumulativeWbound (_y : ℕ) (w : ℕ) : ℕ :=
  w

@[simp] theorem cumulativeWbound_def (y w : ℕ) :
    cumulativeWbound y w = w := rfl

/--
Honest cumulative supply majorant.
-/
noncomputable def cumulativeMbound (y : ℕ) (w : ℕ) : ℕ :=
  cumulativeWbound y w + KmaxB y

@[simp] theorem cumulativeMbound_def (y w : ℕ) :
    cumulativeMbound y w = cumulativeWbound y w + KmaxB y := rfl

theorem cumulativeMbound_eq (y w : ℕ) :
    cumulativeMbound y w = w + KmaxB y := by
  simp [cumulativeMbound, cumulativeWbound]

/--
Cumulative honest scarcity bound on a witness set.
-/
def HasCumulativeScarcityBound (C : Context) (W : Finset ℕ) : Prop :=
  supportCard W ≤ cumulativeWbound C.y (supportCard W)

@[simp] theorem HasCumulativeScarcityBound_def
    (C : Context) (W : Finset ℕ) :
    HasCumulativeScarcityBound C W =
      (supportCard W ≤ cumulativeWbound C.y (supportCard W)) := rfl

/--
Cumulative honest supply bound on a witness set.
-/
def HasCumulativeSupplyBound (C : Context) (W : Finset ℕ) : Prop :=
  supportCard C.S ≤ cumulativeMbound C.y (supportCard W)

@[simp] theorem HasCumulativeSupplyBound_def
    (C : Context) (W : Finset ℕ) :
    HasCumulativeSupplyBound C W =
      (supportCard C.S ≤ cumulativeMbound C.y (supportCard W)) := rfl

/--
The cumulative witness-side majorant is bounded by the cumulative supply
majorant.
-/
theorem cumulativeWbound_le_cumulativeMbound (y w : ℕ) :
    cumulativeWbound y w ≤ cumulativeMbound y w := by
  rw [cumulativeMbound_eq, cumulativeWbound_def]
  exact Nat.le_add_right _ _

/--
`KmaxB` is bounded by the cumulative supply majorant.
-/
theorem KmaxB_le_cumulativeMbound (y w : ℕ) :
    KmaxB y ≤ cumulativeMbound y w := by
  rw [cumulativeMbound_eq]
  exact Nat.le_add_left _ _

/--
Every witness set satisfies the tautological cumulative scarcity estimate.
-/
theorem hasCumulativeScarcityBound_of_witnessSet
    (C : Context) (W : Finset ℕ) :
    HasCumulativeScarcityBound C W := by
  simp [HasCumulativeScarcityBound_def, cumulativeWbound_def]

/--
Transport from the cumulative saturated-support bound to the cumulative `M`
bound.
-/
theorem supportCard_le_cumulativeMbound_of_cumulativeWitnesses
    (C : Context) (W : Finset ℕ)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y (supportCard W)) :
    supportCard C.S ≤ cumulativeMbound C.y (supportCard W) := by
  simpa [saturatedSupportBoundOfCumulativeWitnesses,
    cumulativeMbound, cumulativeWbound]
    using hbound

/--
A cumulative saturated-support bound immediately yields a cumulative supply
bound.
-/
theorem hasCumulativeSupplyBound_of_cumulativeSaturatedSupportBound
    (C : Context) (W : Finset ℕ)
    (hbound : HasCumulativeSaturatedSupportBound C W) :
    HasCumulativeSupplyBound C W := by
  exact supportCard_le_cumulativeMbound_of_cumulativeWitnesses C W hbound

/--
A lock chain induces the honest cumulative supply bound once the corresponding
cumulative saturated-support bound is available.
-/
theorem cumulativeSupplyBound_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y
          (supportCard (genericChainWitnessSet G.chain))) :
    HasCumulativeSupplyBound C (genericChainWitnessSet G.chain) := by
  exact supportCard_le_cumulativeMbound_of_cumulativeWitnesses
    C
    (genericChainWitnessSet G.chain)
    hbound

/--
Expanded cumulative supply inequality for a lock chain.
-/
theorem supportCard_le_cumulativeMbound_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y
          (supportCard (genericChainWitnessSet G.chain))) :
    supportCard C.S ≤
      cumulativeMbound C.y
        (supportCard (genericChainWitnessSet G.chain)) := by
  exact supportCard_le_cumulativeMbound_of_cumulativeWitnesses
    C
    (genericChainWitnessSet G.chain)
    hbound

/--
Expanded cumulative `M`-bound for a lock chain.
-/
theorem cumulativeMbound_of_genericChainToSSLock_eq
    {C : Context} (G : GenericChainToSSLock C) :
    cumulativeMbound C.y
      (supportCard (genericChainWitnessSet G.chain)) =
        supportCard (genericChainWitnessSet G.chain) + KmaxB C.y := by
  exact cumulativeMbound_eq C.y (supportCard (genericChainWitnessSet G.chain))

/--
Local classified supply-bound profile.
-/
structure SupplyBoundProfile (C : Context) where
  accounting : WitnessAccounting C
  hsupply : HasSupplyBound C accounting

/--
Build a local classified supply-bound profile.
-/
def supplyBoundProfile_of_accounting
    {C : Context} (A : WitnessAccounting C)
    (hsupply : HasSupplyBound C A) :
    SupplyBoundProfile C :=
  { accounting := A
    hsupply := hsupply }

/--
Honest cumulative supply-bound profile.
-/
structure CumulativeSupplyBoundProfile (C : Context) where
  cumulativeWitnessSet : Finset ℕ
  hsub : cumulativeWitnessSet ⊆ C.S
  hcard : supportCard cumulativeWitnessSet ≤ supportCard C.S
  hsupply :
    HasCumulativeSupplyBound C cumulativeWitnessSet

/--
Build a cumulative supply-bound profile from a lock chain.
-/
def cumulativeSupplyBoundProfile_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hsupply :
      HasCumulativeSupplyBound C (genericChainWitnessSet G.chain)) :
    CumulativeSupplyBoundProfile C :=
  { cumulativeWitnessSet := genericChainWitnessSet G.chain
    hsub := genericChainWitnessSet_subset_support G.chain
    hcard := card_genericChainWitnessSet_le_supportCard G.chain
    hsupply := hsupply }

/--
Mixed bridge profile carrying both the local classified supply reading and the
honest cumulative supply reading.
-/
structure SupplyBridgeProfile (C : Context) where
  localAccounting : WitnessAccounting C
  entangledLocalSet : Finset ℕ
  cumulativeWitnessSet : Finset ℕ
  hlocalCard : supportCard entangledLocalSet ≤ supportCard C.S
  hcumulativeCard : supportCard cumulativeWitnessSet ≤ supportCard C.S
  hlocalSupply : HasSupplyBound C localAccounting
  hcumulativeSupply : HasCumulativeSupplyBound C cumulativeWitnessSet

/--
Canonical mixed bridge profile associated to a lock chain.
-/
noncomputable def supplyBridgeProfile_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hlocal :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G))
    (hcumulative :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y
          (supportCard (genericChainWitnessSet G.chain))) :
    SupplyBridgeProfile C :=
  { localAccounting := witnessAccountingOfGenericChainToSSLock G
    entangledLocalSet :=
      entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)
    cumulativeWitnessSet := genericChainWitnessSet G.chain
    hlocalCard :=
      card_entangledWitnessSet_of_genericChainToSSLock_le_supportCard G
    hcumulativeCard :=
      card_genericChainWitnessSet_le_supportCard G.chain
    hlocalSupply :=
      supplyBound_of_genericChainToSSLock G hlocal
    hcumulativeSupply :=
      cumulativeSupplyBound_of_genericChainToSSLock G hcumulative }

/--
Current paper-facing supply package for the Case B saturation layer.

Interpretation:
after descending to a locked (`ε_B`-saturated) terminal support, one controls
the initial support by a witness-side scarcity term `W(y)` plus the uniform
descent budget `KmaxB(y)`, hence by `M(y)`.
-/
structure SupplyPackage (C : Context) where
  terminal : Context
  hlevel : terminal.y = C.y
  hlock : SSLock terminal
  accounting : WitnessAccounting C
  hsupply : HasSupplyBound C accounting

/--
Enriched supply bridge package carrying both:
- the local classified supply output,
- the honest cumulative supply output.
-/
structure SupplyBridgePackage (C : Context) where
  terminal : Context
  hlevel : terminal.y = C.y
  hlock : SSLock terminal
  localAccounting : WitnessAccounting C
  cumulativeWitnessSet : Finset ℕ
  hlocalCard :
    supportCard (entangledWitnessSet localAccounting) ≤ supportCard C.S
  hcumulativeCard :
    supportCard cumulativeWitnessSet ≤ supportCard C.S
  hlocalSupply : HasSupplyBound C localAccounting
  hcumulativeSupply : HasCumulativeSupplyBound C cumulativeWitnessSet

/--
A generic chain to lock produces a supply package once the corresponding
saturated-support bound is available for the induced accounting datum.
-/
def supplyPackage_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    SupplyPackage C where
  terminal := G.terminal
  hlevel := GenericChain_preserves_level G.chain
  hlock := G.hlock
  accounting := witnessAccountingOfGenericChainToSSLock G
  hsupply := supplyBound_of_genericChainToSSLock G hbound

/--
A generic chain to lock produces the enriched bridge package once both the
local classified bound and the honest cumulative bound are available.
-/
noncomputable def supplyBridgePackage_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hlocal :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G))
    (hcumulative :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y
          (supportCard (genericChainWitnessSet G.chain))) :
    SupplyBridgePackage C :=
  { terminal := G.terminal
    hlevel := GenericChain_preserves_level G.chain
    hlock := G.hlock
    localAccounting := witnessAccountingOfGenericChainToSSLock G
    cumulativeWitnessSet := genericChainWitnessSet G.chain
    hlocalCard :=
      card_entangledWitnessSet_of_genericChainToSSLock_le_supportCard G
    hcumulativeCard :=
      card_genericChainWitnessSet_le_supportCard G.chain
    hlocalSupply := supplyBound_of_genericChainToSSLock G hlocal
    hcumulativeSupply := cumulativeSupplyBound_of_genericChainToSSLock G hcumulative }

/--
Forget the cumulative side of an enriched bridge package and recover the legacy
local classified supply package.
-/
def supplyPackage_of_supplyBridgePackage
    {C : Context} (P : SupplyBridgePackage C) :
    SupplyPackage C :=
  { terminal := P.terminal
    hlevel := P.hlevel
    hlock := P.hlock
    accounting := P.localAccounting
    hsupply := P.hlocalSupply }

end CaseB
end Lehmer