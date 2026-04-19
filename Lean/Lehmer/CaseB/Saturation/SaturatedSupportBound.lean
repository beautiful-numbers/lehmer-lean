-- FILE: Lean/Lehmer/CaseB/Saturation/SaturatedSupportBound.lean
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

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
Abstract saturated-support majorant.

This is the support-side target bound for a terminal `ε_B`-saturated context.
At the current stage it is defined as the Case B descent budget plus the
cardinality of the entangled witness set, matching the paper logic that the
terminal saturated support is controlled by the scarcity side plus the descent
window.
-/
noncomputable def saturatedSupportBound (y : ℕ) (w : ℕ) : ℕ :=
  w + KmaxB y

@[simp] theorem saturatedSupportBound_def (y w : ℕ) :
    saturatedSupportBound y w = w + KmaxB y := rfl

/--
Context-level witness budget extracted from a witness accounting datum.
-/
noncomputable def witnessBudget {C : Context} (A : WitnessAccounting C) : ℕ :=
  supportCard (entangledWitnessSet A)

@[simp] theorem witnessBudget_def {C : Context} (A : WitnessAccounting C) :
    witnessBudget A = supportCard (entangledWitnessSet A) := rfl

/--
The witness budget is support-bounded.
-/
theorem witnessBudget_le_supportCard {C : Context} (A : WitnessAccounting C) :
    witnessBudget A ≤ supportCard C.S := by
  exact card_entangledWitnessSet_le_supportCard A

/--
Saturated-support bound attached to a witness accounting datum.
-/
noncomputable def saturatedSupportBoundOfAccounting {C : Context}
    (A : WitnessAccounting C) : ℕ :=
  saturatedSupportBound C.y (witnessBudget A)

@[simp] theorem saturatedSupportBoundOfAccounting_def {C : Context}
    (A : WitnessAccounting C) :
    saturatedSupportBoundOfAccounting A = saturatedSupportBound C.y (witnessBudget A) := rfl

/--
Expanded form of the accounting-based saturated-support bound.
-/
theorem saturatedSupportBoundOfAccounting_eq {C : Context}
    (A : WitnessAccounting C) :
    saturatedSupportBoundOfAccounting A =
      supportCard (entangledWitnessSet A) + KmaxB C.y := by
  simp [saturatedSupportBoundOfAccounting, saturatedSupportBound, witnessBudget]

/--
A saturated context together with witness accounting satisfies the paper-facing
support bound when its support cardinality is bounded by the accounting-based
majorant.
-/
def HasSaturatedSupportBound (C : Context) (A : WitnessAccounting C) : Prop :=
  supportCard C.S ≤ saturatedSupportBoundOfAccounting A

@[simp] theorem HasSaturatedSupportBound_def (C : Context) (A : WitnessAccounting C) :
    HasSaturatedSupportBound C A =
      (supportCard C.S ≤ saturatedSupportBoundOfAccounting A) := rfl

/--
Monotonicity in the witness budget argument.
-/
theorem saturatedSupportBound_mono_right {y w₁ w₂ : ℕ}
    (hw : w₁ ≤ w₂) :
    saturatedSupportBound y w₁ ≤ saturatedSupportBound y w₂ := by
  dsimp [saturatedSupportBound]
  omega

/--
The saturated-support bound dominates the descent budget.
-/
theorem KmaxB_le_saturatedSupportBound (y w : ℕ) :
    KmaxB y ≤ saturatedSupportBound y w := by
  dsimp [saturatedSupportBound]
  exact Nat.le_add_left _ _

/--
The saturated-support bound dominates the witness budget.
-/
theorem witnessBudget_le_saturatedSupportBound (y w : ℕ) :
    w ≤ saturatedSupportBound y w := by
  dsimp [saturatedSupportBound]
  exact Nat.le_add_right _ _

/--
A trivial saturated-support bound from a direct support-cardinality assumption.
-/
theorem hasSaturatedSupportBound_of_assumption
    (C : Context) (A : WitnessAccounting C)
    (hbound : supportCard C.S ≤ saturatedSupportBoundOfAccounting A) :
    HasSaturatedSupportBound C A := by
  exact hbound

/--
Every saturated context with witness accounting satisfies a weak support bound
as soon as its support is bounded by the accounting majorant.
This is just the packaged form of the previous theorem.
-/
theorem saturatedSupportBound_of_lock_and_accounting
    (C : Context) (A : WitnessAccounting C)
    (_hlock : SSLock C)
    (hbound : supportCard C.S ≤ saturatedSupportBoundOfAccounting A) :
    HasSaturatedSupportBound C A := by
  exact hasSaturatedSupportBound_of_assumption C A hbound

/--
A generic chain to lock induces an accounting-based saturated-support bound on
its initial context whenever that initial support is bounded by the induced
majorant.

Note: `witnessAccountingOfGenericChainToSSLock G` is accounting on the initial
context of the chain, not on the terminal context.
-/
theorem saturatedSupportBound_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    HasSaturatedSupportBound C
      (witnessAccountingOfGenericChainToSSLock G) := by
  exact hbound

/--
The induced accounting majorant for a generic chain to lock expands as the sum
of the entangled-witness budget and the descent budget.
-/
theorem saturatedSupportBoundOf_genericChainToSSLock_eq
    {C : Context} (G : GenericChainToSSLock C) :
    saturatedSupportBoundOfAccounting
      (witnessAccountingOfGenericChainToSSLock G) =
        supportCard
          (entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)) +
        KmaxB C.y := by
  exact saturatedSupportBoundOfAccounting_eq
    (witnessAccountingOfGenericChainToSSLock G)

/--
The induced accounting majorant for a generic chain to lock is at least the
entangled-witness budget.
-/
theorem entangledWitnessBudget_le_saturatedSupportBoundOf_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C) :
    supportCard (entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)) ≤
      saturatedSupportBoundOfAccounting
        (witnessAccountingOfGenericChainToSSLock G) := by
  have h :
      supportCard (entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)) ≤
        supportCard (entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)) +
          KmaxB C.y := by
    exact Nat.le_add_right _ _
  exact (saturatedSupportBoundOf_genericChainToSSLock_eq G).symm ▸ h

/--
The induced accounting majorant for a generic chain to lock is at least the
descent budget `KmaxB`.
-/
theorem KmaxB_le_saturatedSupportBoundOf_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C) :
    KmaxB C.y ≤
      saturatedSupportBoundOfAccounting
        (witnessAccountingOfGenericChainToSSLock G) := by
  have h :
      KmaxB C.y ≤
        supportCard (entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)) +
          KmaxB C.y := by
    exact Nat.le_add_left _ _
  exact (saturatedSupportBoundOf_genericChainToSSLock_eq G).symm ▸ h

/--
Cumulative honest saturated-support majorant.

This uses the cumulative witness-side reading of a chain rather than the local
classified entangled witness budget.
-/
noncomputable def saturatedSupportBoundOfCumulativeWitnesses
    (y w : ℕ) : ℕ :=
  w + KmaxB y

@[simp] theorem saturatedSupportBoundOfCumulativeWitnesses_def
    (y w : ℕ) :
    saturatedSupportBoundOfCumulativeWitnesses y w = w + KmaxB y := rfl

/--
Cumulative witness budget attached to an arbitrary finite witness set.
-/
noncomputable def cumulativeWitnessBudget
    (W : Finset ℕ) : ℕ :=
  supportCard W

@[simp] theorem cumulativeWitnessBudget_def
    (W : Finset ℕ) :
    cumulativeWitnessBudget W = supportCard W := rfl

/--
Cumulative honest saturated-support bound.
-/
def HasCumulativeSaturatedSupportBound (C : Context) (W : Finset ℕ) : Prop :=
  supportCard C.S ≤ saturatedSupportBoundOfCumulativeWitnesses C.y (supportCard W)

@[simp] theorem HasCumulativeSaturatedSupportBound_def
    (C : Context) (W : Finset ℕ) :
    HasCumulativeSaturatedSupportBound C W =
      (supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y (supportCard W)) := rfl

/--
Profile of a local classifed saturated-support bound.
-/
structure SaturatedSupportBoundProfile (C : Context) where
  witnessBudget0 : ℕ
  hbound : supportCard C.S ≤ saturatedSupportBound C.y witnessBudget0

/--
Build a local classified saturated-support profile from accounting data.
-/
noncomputable def saturatedSupportBoundProfile_of_accounting
    {C : Context} (A : WitnessAccounting C)
    (hbound : HasSaturatedSupportBound C A) :
    SaturatedSupportBoundProfile C :=
  { witnessBudget0 := witnessBudget A
    hbound := by
      simpa [HasSaturatedSupportBound, saturatedSupportBoundOfAccounting]
        using hbound }

/--
Profile of an honest cumulative saturated-support bound.
-/
structure CumulativeSaturatedSupportBoundProfile (C : Context) where
  cumulativeWitnessSet : Finset ℕ
  hsub : cumulativeWitnessSet ⊆ C.S
  hcard : supportCard cumulativeWitnessSet ≤ supportCard C.S
  hbound :
    supportCard C.S ≤
      saturatedSupportBoundOfCumulativeWitnesses C.y
        (supportCard cumulativeWitnessSet)

/--
Build a cumulative saturated-support profile from an explicit assumption.
-/
def cumulativeSaturatedSupportBoundProfile_of_assumption
    {C : Context} (W : Finset ℕ)
    (hsub : W ⊆ C.S)
    (hcard : supportCard W ≤ supportCard C.S)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y (supportCard W)) :
    CumulativeSaturatedSupportBoundProfile C :=
  { cumulativeWitnessSet := W
    hsub := hsub
    hcard := hcard
    hbound := hbound }

/--
Build a cumulative saturated-support profile from a lock chain once the
corresponding cumulative bound is available.
-/
def cumulativeSaturatedSupportBoundProfile_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y
          (supportCard (genericChainWitnessSet G.chain))) :
    CumulativeSaturatedSupportBoundProfile C :=
  { cumulativeWitnessSet := genericChainWitnessSet G.chain
    hsub := genericChainWitnessSet_subset_support G.chain
    hcard := card_genericChainWitnessSet_le_supportCard G.chain
    hbound := hbound }

/--
Build a local classified saturated-support profile from a lock chain once the
corresponding classified accounting bound is available.
-/
noncomputable def saturatedSupportBoundProfile_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    SaturatedSupportBoundProfile C :=
  { witnessBudget0 := witnessBudget (witnessAccountingOfGenericChainToSSLock G)
    hbound := by
      simpa [witnessBudget, saturatedSupportBoundOfAccounting, saturatedSupportBound]
        using hbound }

/--
Mixed bridge profile carrying both:
- the local classified accounting-side bound,
- the honest cumulative witness-side bound.
-/
structure SaturatedSupportBridgeProfile (C : Context) where
  localAccounting : WitnessAccounting C
  entangledLocalSet : Finset ℕ
  cumulativeWitnessSet : Finset ℕ
  hlocalCard : supportCard entangledLocalSet ≤ supportCard C.S
  hcumulativeCard : supportCard cumulativeWitnessSet ≤ supportCard C.S
  hlocalBound :
    supportCard C.S ≤
      saturatedSupportBoundOfAccounting localAccounting
  hcumulativeBound :
    supportCard C.S ≤
      saturatedSupportBoundOfCumulativeWitnesses C.y
        (supportCard cumulativeWitnessSet)

/--
Canonical mixed bridge profile associated to a lock chain, once the two
corresponding bounds are supplied.
-/
noncomputable def saturatedSupportBridgeProfile_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hlocal :
      supportCard C.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G))
    (hcumulative :
      supportCard C.S ≤
        saturatedSupportBoundOfCumulativeWitnesses C.y
          (supportCard (genericChainWitnessSet G.chain))) :
    SaturatedSupportBridgeProfile C :=
  { localAccounting := witnessAccountingOfGenericChainToSSLock G
    entangledLocalSet :=
      entangledWitnessSet (witnessAccountingOfGenericChainToSSLock G)
    cumulativeWitnessSet := genericChainWitnessSet G.chain
    hlocalCard :=
      card_entangledWitnessSet_of_genericChainToSSLock_le_supportCard G
    hcumulativeCard :=
      card_genericChainWitnessSet_le_supportCard G.chain
    hlocalBound := hlocal
    hcumulativeBound := hcumulative }

/--
The cumulative saturated-support bound dominates `KmaxB`.
-/
theorem KmaxB_le_saturatedSupportBoundOfCumulativeWitnesses
    (y w : ℕ) :
    KmaxB y ≤ saturatedSupportBoundOfCumulativeWitnesses y w := by
  simp [saturatedSupportBoundOfCumulativeWitnesses]

/--
The cumulative saturated-support bound dominates its witness-budget argument.
-/
theorem cumulativeWitnessBudget_le_saturatedSupportBoundOfCumulativeWitnesses
    (y w : ℕ) :
    w ≤ saturatedSupportBoundOfCumulativeWitnesses y w := by
  simp [saturatedSupportBoundOfCumulativeWitnesses]

/--
The cumulative saturated-support bound attached to a lock chain dominates the
cumulative witness budget of that chain.
-/
theorem cumulativeWitnessBudget_le_saturatedSupportBoundOf_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C) :
    supportCard (genericChainWitnessSet G.chain) ≤
      saturatedSupportBoundOfCumulativeWitnesses C.y
        (supportCard (genericChainWitnessSet G.chain)) := by
  simp [saturatedSupportBoundOfCumulativeWitnesses]

/--
The cumulative saturated-support bound attached to a lock chain dominates the
descent budget `KmaxB`.
-/
theorem KmaxB_le_saturatedSupportBoundOf_genericChainToSSLock_cumulative
    {C : Context} (G : GenericChainToSSLock C) :
    KmaxB C.y ≤
      saturatedSupportBoundOfCumulativeWitnesses C.y
        (supportCard (genericChainWitnessSet G.chain)) := by
  simp [saturatedSupportBoundOfCumulativeWitnesses]

end CaseB
end Lehmer