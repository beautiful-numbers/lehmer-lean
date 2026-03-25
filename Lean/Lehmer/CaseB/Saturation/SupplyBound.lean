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

At the present stage, this is represented by the witness-budget-side quantity
coming from the saturation/accounting layer. The later dominance layer will
replace this with a closed-form majorant.
-/
noncomputable def Wbound (y : ℕ) (w : ℕ) : ℕ :=
  w

@[simp] theorem Wbound_def (y w : ℕ) :
    Wbound y w = w := rfl

/--
Paper-style global Case B support bound:
`M(y) = W(y) + Kmax,B(y)`.

At the current stage, `W(y)` is represented abstractly by the witness-budget
parameter.
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
def WboundOfAccounting {C : Context} (A : WitnessAccounting C) : ℕ :=
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
  simp [MboundOfAccounting, Mbound_eq]

/--
The terminal saturated support is bounded by `W(y)` once one has an explicit
scarcity estimate on the witness budget.
-/
def HasScarcityBound (C : Context) (A : WitnessAccounting C) : Prop :=
  supportCard C.S ≤ WboundOfAccounting A

@[simp] theorem HasScarcityBound_def (C : Context) (A : WitnessAccounting C) :
    HasScarcityBound C A = (supportCard C.S ≤ WboundOfAccounting A) := rfl

/--
The paper-style Case B supply bound on a terminal saturated support.
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
  simp [Mbound, Wbound]
  exact Nat.le_add_right _ _

/--
`KmaxB(y)` is bounded by `M(y)`.
-/
theorem KmaxB_le_Mbound (y w : ℕ) :
    KmaxB y ≤ Mbound y w := by
  simp [Mbound, Wbound]
  exact Nat.le_add_left _ _

/--
A scarcity bound immediately yields the paper-style supply bound.
-/
theorem hasSupplyBound_of_hasScarcityBound
    (C : Context) (A : WitnessAccounting C)
    (hscarce : HasScarcityBound C A) :
    HasSupplyBound C A := by
  have hmono : WboundOfAccounting A ≤ MboundOfAccounting A := by
    simp [WboundOfAccounting, MboundOfAccounting]
    exact Wbound_le_Mbound C.y (witnessBudget A)
  exact le_trans hscarce hmono

/--
Support-bounded witness accounting gives the canonical abstract scarcity
estimate on the witness side.
-/
theorem witnessBudget_is_scarce {C : Context} (A : WitnessAccounting C) :
    witnessBudget A ≤ supportCard C.S := by
  exact witnessBudget_le_supportCard A

/--
If a terminal saturated context satisfies the explicit saturated-support bound,
then it satisfies the paper-style supply bound.
-/
theorem hasSupplyBound_of_saturatedSupportBound
    (C : Context) (A : WitnessAccounting C)
    (_hlock : SSLock C)
    (hbound : HasSaturatedSupportBound C A) :
    HasSupplyBound C A := by
  rw [HasSaturatedSupportBound_def] at hbound
  rw [HasSupplyBound_def]
  simpa [saturatedSupportBoundOfAccounting_eq, MboundOfAccounting_eq, witnessBudget_def]

/--
Package form of the paper inequality
`|S| ≤ W(y) + Kmax,B(y) = M(y)`.
-/
theorem supportCard_le_Mbound_of_lock_and_accounting
    (C : Context) (A : WitnessAccounting C)
    (_hlock : SSLock C)
    (hbound : supportCard C.S ≤ saturatedSupportBoundOfAccounting A) :
    supportCard C.S ≤ MboundOfAccounting A := by
  have hs : HasSaturatedSupportBound C A := hbound
  exact hasSupplyBound_of_saturatedSupportBound C A ‹SSLock C› hs

/--
A generic chain to lock induces the paper-style supply bound on its terminal
context whenever the terminal saturated-support bound has been established.
-/
theorem supplyBound_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard G.terminal.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    HasSupplyBound G.terminal (witnessAccountingOfGenericChainToSSLock G) := by
  exact hasSupplyBound_of_saturatedSupportBound
    G.terminal
    (witnessAccountingOfGenericChainToSSLock G)
    G.hlock
    hbound

/--
Expanded terminal supply inequality for a generic chain to lock.
-/
theorem supportCard_terminal_le_Mbound_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard G.terminal.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    supportCard G.terminal.S ≤
      MboundOfAccounting (witnessAccountingOfGenericChainToSSLock G) := by
  exact supplyBound_of_genericChainToSSLock G hbound

/--
The accounting-specialized `M(y)` induced by a generic chain to lock expands as
`witnessBudget + KmaxB`.
-/
theorem MboundOf_genericChainToSSLock_eq
    {C : Context} (G : GenericChainToSSLock C) :
    MboundOfAccounting (witnessAccountingOfGenericChainToSSLock G) =
      witnessBudget (witnessAccountingOfGenericChainToSSLock G) + KmaxB C.y := by
  have hlevel : G.terminal.y = C.y := GenericChain_preserves_level G.chain
  rw [MboundOfAccounting_eq]
  simpa [witnessBudget, hlevel]

/--
Current paper-facing supply package for the Case B saturation layer.

Interpretation:
after descending to a locked (`ε_B`-saturated) terminal support, one controls
its size by a witness-side scarcity term `W(y)` plus the uniform descent budget
`KmaxB(y)`, hence by `M(y)`.
-/
structure SupplyPackage (C : Context) where
  terminal : Context
  hlevel : terminal.y = C.y
  hlock : SSLock terminal
  accounting : WitnessAccounting terminal
  hsupply : HasSupplyBound terminal accounting

/--
A generic chain to lock produces a supply package once the terminal
saturated-support bound is available.
-/
def supplyPackage_of_genericChainToSSLock
    {C : Context} (G : GenericChainToSSLock C)
    (hbound :
      supportCard G.terminal.S ≤
        saturatedSupportBoundOfAccounting
          (witnessAccountingOfGenericChainToSSLock G)) :
    SupplyPackage C where
  terminal := G.terminal
  hlevel := GenericChain_preserves_level G.chain
  hlock := G.hlock
  accounting := witnessAccountingOfGenericChainToSSLock G
  hsupply := supplyBound_of_genericChainToSSLock G hbound

end CaseB
end Lehmer