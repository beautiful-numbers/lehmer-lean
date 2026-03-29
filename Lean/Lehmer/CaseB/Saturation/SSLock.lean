-- FILE: Lean/Lehmer/CaseB/Saturation/SSLock.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Basic.Defs : def
- Lehmer.CaseB.Spec : struct spec def
- Lehmer.CaseB.Descent.ControlledRemoval : def thm
- Lehmer.CaseB.Descent.Gain : def thm
- Lehmer.CaseB.Descent.P2Decrease : thm
- Lehmer.CaseB.Descent.KmaxB : param thm
- Lehmer.CaseB.Descent.DescentSkeleton : def thm
- Lehmer.CaseB.Saturation.GenericChains : def thm
- Lehmer.CaseB.Saturation.WitnessAccounting : def thm
-/

import Lehmer.Prelude
import Lehmer.Basic.Defs
import Lehmer.CaseB.Spec
import Lehmer.CaseB.Descent.ControlledRemoval
import Lehmer.CaseB.Descent.Gain
import Lehmer.CaseB.Descent.P2Decrease
import Lehmer.CaseB.Descent.KmaxB
import Lehmer.CaseB.Descent.DescentSkeleton
import Lehmer.CaseB.Saturation.GenericChains
import Lehmer.CaseB.Saturation.WitnessAccounting

namespace Lehmer
namespace CaseB

open Lehmer.Basic

/--
`SSLock C` is the saturation-side lock predicate attached to a Case B context.

At the current stage of the refactor, the lock is the assertion that the
context is already `ε_B`-saturated. This is the exact terminal condition that
the descent window is designed to reach before the scarcity/supply layers are
applied.
-/
def SSLock (C : Context) : Prop :=
  EpsBSaturated C

@[simp] theorem SSLock_def (C : Context) :
    SSLock C = EpsBSaturated C := rfl

/--
A locked context is saturated.
-/
theorem epsBSaturated_of_SSLock (C : Context)
    (hlock : SSLock C) :
    EpsBSaturated C := by
  simpa [SSLock] using hlock

/--
A saturated context is locked.
-/
theorem SSLock_of_epsBSaturated (C : Context)
    (hsat : EpsBSaturated C) :
    SSLock C := by
  simpa [SSLock] using hsat

/--
The lock predicate is equivalent to saturation.
-/
theorem SSLock_iff_epsBSaturated (C : Context) :
    SSLock C ↔ EpsBSaturated C := by
  simp [SSLock]

/--
A locked context is not in the descent regime.
-/
theorem not_ContextNonSaturated_of_SSLock (C : Context)
    (hlock : SSLock C) :
    ¬ ContextNonSaturated C := by
  simpa [SSLock, EpsBSaturated, ContextSaturated, Saturated] using hlock

/--
A locked context cannot be descent-eligible.
-/
theorem not_ContextDescentEligible_of_SSLock (C : Context)
    (hlock : SSLock C) :
    ¬ ContextDescentEligible C := by
  intro hdes
  exact (not_ContextNonSaturated_of_SSLock C hlock) hdes.1

/--
Every locked context gives a trivial descent window of length `0`.
-/
def descentWindow_of_SSLock (C : Context)
    (hlock : SSLock C)
    (hbound : supportCard C.S ≤ KmaxB C.y) :
    DescentWindow C :=
  descent_window_of_saturated C (epsBSaturated_of_SSLock C hlock) hbound

/--
A generic chain to a locked terminal context packages the generic-side lock
interface needed by later scarcity arguments.
-/
structure GenericChainToSSLock (C : Context) where
  terminal : Context
  chain : GenericChain C terminal
  hbudget : GenericChainWithinBudget chain
  hlock : SSLock terminal

/--
A trivial generic chain to lock exists when the starting context is already
locked.
-/
def trivialGenericChainToSSLock (C : Context)
    (hlock : SSLock C) :
    GenericChainToSSLock C where
  terminal := C
  chain := GenericChain.nil C
  hbudget := genericChainWithinBudget_nil C
  hlock := hlock

/--
A generic chain to saturation gives a generic chain to lock.
-/
def genericChainToSSLock_of_saturated {C : Context}
    (G : GenericChainToSaturated C) :
    GenericChainToSSLock C where
  terminal := G.terminal
  chain := G.chain
  hbudget := G.hbudget
  hlock := SSLock_of_epsBSaturated G.terminal G.hsaturated

/--
Witness accounting attached to a generic chain reaching a locked terminal
context.
-/
def witnessAccountingOfGenericChainToSSLock {C : Context}
    (G : GenericChainToSSLock C) :
    WitnessAccounting C :=
  witnessAccountingOfGenericChain G.chain

/--
The witness accounting induced by a generic chain to lock is support-bounded.
-/
theorem card_witnessAccountingOfGenericChainToSSLock_le_supportCard
    {C : Context} (G : GenericChainToSSLock C) :
    supportCard (witnessSet C (witnessAccountingOfGenericChainToSSLock G)) ≤ supportCard C.S := by
  exact card_witnessAccountingOfGenericChain_le_supportCard G.chain

/--
If the descent window has already reached a saturated terminal context, then
that terminal context is locked.
-/
theorem SSLock_terminal_of_descentWindow {C : Context}
    (W : DescentWindow C) :
    SSLock W.terminal := by
  exact SSLock_of_epsBSaturated W.terminal W.hterminal_saturated

/--
Any descent window induces a trivial lock package at its terminal context.
-/
def terminalLockWitness_of_descentWindow {C : Context}
    (W : DescentWindow C) :
    GenericChainToSSLock W.terminal :=
  trivialGenericChainToSSLock W.terminal (SSLock_of_epsBSaturated W.terminal W.hterminal_saturated)

/--
A locked context still satisfies the same Case B level as itself.
This theorem is only a normalization lemma for later saturation files.
-/
theorem SSLock_preserves_level_trivially (C : Context)
    (_hlock : SSLock C) :
    C.y = C.y := by
  rfl

end CaseB
end Lehmer