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
A locked context is exactly a context that is no longer non-saturated.
-/
theorem SSLock_iff_not_ContextNonSaturated (C : Context) :
    SSLock C ↔ ¬ ContextNonSaturated C := by
  simp [SSLock, EpsBSaturated, ContextSaturated, Saturated]

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
On a nonempty support, being locked is equivalent to not being
descent-eligible.
-/
theorem SSLock_iff_not_ContextDescentEligible_of_nonempty
    (C : Context)
    (hS : C.S.Nonempty) :
    SSLock C ↔ ¬ ContextDescentEligible C := by
  constructor
  · intro hlock
    exact not_ContextDescentEligible_of_SSLock C hlock
  · intro hnot
    have hns : ¬ ContextNonSaturated C := by
      intro hctx
      exact hnot ⟨hctx, hS⟩
    simpa [SSLock, EpsBSaturated, ContextSaturated, Saturated] using hns

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

@[simp] theorem GenericChainToSSLock_terminal_level
    {C : Context} (G : GenericChainToSSLock C) :
    G.terminal.y = C.y := by
  exact GenericChain_preserves_level G.chain

@[simp] theorem GenericChainToSSLock_budget
    {C : Context} (G : GenericChainToSSLock C) :
    genericChainLength G.chain ≤ KmaxB C.y := by
  simpa [GenericChainWithinBudget_def] using G.hbudget

@[simp] theorem GenericChainToSSLock_terminal_locked
    {C : Context} (G : GenericChainToSSLock C) :
    SSLock G.terminal := by
  exact G.hlock

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
Explicit terminal profile exported by the local strategy-1 lock layer.
-/
structure SSLockTerminalProfile (C : Context) where
  terminal : Context
  hlevel : terminal.y = C.y
  hlock : SSLock terminal
  hbudget : ℕ
  hk : hbudget ≤ KmaxB C.y

/--
Canonical terminal profile induced by a generic chain to lock.
-/
def ssLockTerminalProfile_of_genericChainToSSLock
    {C : Context}
    (G : GenericChainToSSLock C) :
    SSLockTerminalProfile C :=
  { terminal := G.terminal
    hlevel := GenericChain_preserves_level G.chain
    hlock := G.hlock
    hbudget := genericChainLength G.chain
    hk := by
      simpa [GenericChainWithinBudget_def] using G.hbudget }

/--
Explicit bridge seed from the local strategy-1 lock output to the common
strategy-1/strategy-2 spec interface.
-/
def caseBStrategyBridgeSeed_of_genericChainToSSLock
    {C : Context}
    (_G : GenericChainToSSLock C) :
    CaseBStrategyBridgeSeed C :=
  caseBStrategyBridgeSeed_of_context C

@[simp] theorem caseBStrategyBridgeSeed_of_genericChainToSSLock_y
    {C : Context}
    (G : GenericChainToSSLock C) :
    (caseBStrategyBridgeSeed_of_genericChainToSSLock G).y0 = C.y := by
  rfl

@[simp] theorem caseBStrategyBridgeSeed_of_genericChainToSSLock_omega
    {C : Context}
    (G : GenericChainToSSLock C) :
    (caseBStrategyBridgeSeed_of_genericChainToSSLock G).omega0 = supportCard C.S := by
  rfl

/--
A richer profile view of a generic chain to lock.
-/
structure GenericChainToSSLockProfile (C : Context) where
  terminal : Context
  chain : GenericChain C terminal
  hlevel : terminal.y = C.y
  hbudget : genericChainLength chain ≤ KmaxB C.y
  hlock : SSLock terminal

/--
Canonical profile associated to a generic chain to lock.
-/
def genericChainToSSLockProfile_of_lockChain
    {C : Context}
    (G : GenericChainToSSLock C) :
    GenericChainToSSLockProfile C :=
  { terminal := G.terminal
    chain := G.chain
    hlevel := GenericChain_preserves_level G.chain
    hbudget := by
      simpa [GenericChainWithinBudget_def] using G.hbudget
    hlock := G.hlock }

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
Accounting-side profile exported from a lock chain.
-/
structure SSLockAccountingProfile (C : Context) where
  lockChain : GenericChainToSSLock C
  accounting : WitnessAccounting C
  hwitness :
    supportCard (witnessSet C accounting) ≤ supportCard C.S

/--
Canonical accounting profile induced by a generic chain to lock.
-/
def ssLockAccountingProfile_of_genericChainToSSLock
    {C : Context}
    (G : GenericChainToSSLock C) :
    SSLockAccountingProfile C :=
  { lockChain := G
    accounting := witnessAccountingOfGenericChainToSSLock G
    hwitness := card_witnessAccountingOfGenericChainToSSLock_le_supportCard G }

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
  trivialGenericChainToSSLock W.terminal
    (SSLock_of_epsBSaturated W.terminal W.hterminal_saturated)

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