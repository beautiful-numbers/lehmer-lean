-- FILE: Lean/Lehmer/CaseB/Dominance/AnalyticNoCrossing.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.CaseB.Dominance.NoCrossing : def thm
- Lehmer.Pivot.MreqAnalyticBridge : thm

FILE ROLE
This file is the paper-friendly decomposition of the Case B no-crossing step.

Architecture note:
- The main closure of Case B may already be closed elsewhere by certificates.
  Accordingly, this file is NOT required to be the primary main-closing proof.
- Its role here is audit-facing / expository: it re-exposes the no-crossing
  chain in the paper vocabulary.

Public audit-facing API (paper chain):
  A. `M(y) ≤ Mc(y)`
  B. `Mc(y) < C1 * y^2 / log y`
  C. `C1 * y^2 / log y < mreq(y)`
  then `M(y) < mreq(y)`.

Internal Lean plumbing may still use:
- `analyticBarrier`,
- `Nat.ceil`,
- casts between `ℕ` and `ℝ`,
- bridge-shape pivot lemmas.

These internal bridge lemmas are kept because they remain useful for the Lean
implementation, but they are not the public paper-facing API of this file.
-/

import Lehmer.Prelude
import Lehmer.CaseB.Dominance.NoCrossing
import Lehmer.Pivot.MreqAnalyticBridge

namespace Lehmer
namespace CaseB

open Lehmer.Pivot

/-- Internal alias: the paper pivot barrier `C1 * t^2 / log t`. -/
noncomputable def pivotBarrier (t : ℝ) : ℝ :=
  C1 * t^2 / Real.log t

@[simp] theorem pivotBarrier_def (t : ℝ) :
    pivotBarrier t = C1 * t^2 / Real.log t := rfl

/--
Case B-facing internal pivot bridge.

This is the exact Lean bridge used to compare the discretized analytic barrier
with `mreq`, rewritten in the Case B notation where the same real function is
named `analyticBarrier`.

Important:
- this is internal Lean plumbing;
- it is not the public paper-facing statement of Lemma 3.4.
-/
theorem barrierCeil_le_mreq
    {y : ℕ}
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y := by
  simpa [analyticBarrier] using
    (analyticBarrierCeil_le_mreq (y := y) h_exists hbelow)

/--
Non-curried Case B-facing form of the same internal bridge.
-/
theorem barrierCeil_le_mreq_of_ge_Y0
    (y : ℕ)
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y := by
  simpa [analyticBarrier] using
    (analyticBarrierCeil_le_mreq_of_ge_Y0 y h_exists hbelow)

/-!
## Public paper-facing API
The four theorems below are the intended audit-facing decomposition matching the
paper:

1. `M_le_Mc`
2. `Mc_lt_pivotBarrier_of_ge_TB`
3. `pivotBarrier_lt_mreq_of_ge_Y0`
4. `analytic_noCrossing`

The proof bodies of (1) and (2) must be connected to the exact structural /
certificate lemmas already present in the repository.
-/

/--
Paper-facing structural majorant step.

This is the Case B structural facade corresponding to equation (27) in the
paper: for every prime `y ≥ 3`, one has `M(y) ≤ Mc(y)`.
-/
theorem M_le_Mc
    (y : ℕ)
    (hp : Nat.Prime y) :
    M y ≤ Mc y := by
  /-
  Connect this to the exact structural lemma already present in the repo.

  Paper source:
    M(y) ≤ Mc(y)   (equation (27))

  Expected implementation style:
  - either a direct proof by unfolding `M` and `Mc`,
  - or a wrapper over the structural majorant lemma already proved elsewhere.
  -/
  sorry

/--
Paper-facing uniform analytic dominance beyond `TB`.

This is the Case B analytic step corresponding to Lemma 5.7 in the paper,
specialized to natural pivot values:
  `Mc(y) < C1 * y^2 / log y`
for every prime `y ≥ TB`.
-/
theorem Mc_lt_pivotBarrier_of_ge_TB
    (y : ℕ)
    (hy : TB ≤ (y : ℝ))
    (hp : Nat.Prime y) :
    Mc y < pivotBarrier (y : ℝ) := by
  /-
  Connect this to the exact certified / analytic lemma already present in the
  repo for the closed majorant `Mc`.

  Paper source:
    Lemma 5.7: for every real t ≥ TB,
      Mc(t) < C1 * t^2 / log t.

  Since the current Lean `Mc` is indexed by `ℕ`, this theorem is the natural
  paper-facing specialization to `t = y`.
  -/
  sorry

/--
Paper-facing pivot lower bound.

This is the public audit-facing form corresponding to the large-range pivot
bound from Lemma 3.4:
  `C1 * y^2 / log y < mreq(y)` for primes `y ≥ Y0`.

Internal Lean proofs may use the discretized bridge
`Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y`, but that plumbing is not the
public API.
-/
theorem pivotBarrier_lt_mreq_of_ge_Y0
    (y : ℕ)
    (hy : Y0 ≤ y)
    (hp : Nat.Prime y)
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    pivotBarrier (y : ℝ) < (mreq y : ℝ) := by
  have hceil_nat : Nat.ceil (analyticBarrier (y : ℝ)) ≤ mreq y :=
    barrierCeil_le_mreq_of_ge_Y0 y h_exists hbelow
  have hceil : (Nat.ceil (analyticBarrier (y : ℝ)) : ℝ) ≤ (mreq y : ℝ) := by
    exact_mod_cast hceil_nat
  have hbar : analyticBarrier (y : ℝ) ≤ (Nat.ceil (analyticBarrier (y : ℝ)) : ℝ) := by
    exact Nat.le_ceil _
  have hbar' : pivotBarrier (y : ℝ) ≤ (Nat.ceil (analyticBarrier (y : ℝ)) : ℝ) := by
    simpa [pivotBarrier, analyticBarrier] using hbar

  /-
  At this stage the bridge gives a clean paper-facing lower bound in weak form.
  To obtain the strict `<` stated in the paper-facing API, one should connect
  here to the exact large-range analytic input already available in the pivot
  layer (or its endpoint-certified propagation), rather than stopping at the
  discretized inequality.

  If the upstream pivot layer already exports the strict paper-facing form of
  Lemma 3.4, replace this proof by a direct wrapper.
  -/
  exact lt_of_le_of_lt hbar' (lt_of_le_of_ne hceil (by
    intro hEq
    /-
    This remaining strictness step must be discharged by the exact upstream
    large-range pivot theorem / certificate package.
    -/
    sorry))

/--
Paper-facing no-crossing decomposition.

This theorem matches the paper chain
  `M(y) ≤ Mc(y) < C1 * y^2 / log y < mreq(y)`
for every prime `y ≥ Ystar`.
-/
theorem analytic_noCrossing
    (y : ℕ)
    (hy : Ystar ≤ y)
    (hp : Nat.Prime y)
    (h_exists : ∃ k : ℕ, (2 : ℚ) < UBm y k)
    (hbelow :
      ∀ m : ℕ, m < Nat.ceil (barrier (y : ℝ)) → UBm y m ≤ 2) :
    M y < (mreq y : ℝ) := by
  have hA : M y ≤ Mc y :=
    M_le_Mc y hp

  have hyTB : TB ≤ (y : ℝ) := by
    have hTB : TB ≤ (Ystar : ℝ) := TB_le_Ystar
    exact le_trans hTB (by exact_mod_cast hy)

  have hB : Mc y < pivotBarrier (y : ℝ) :=
    Mc_lt_pivotBarrier_of_ge_TB y hyTB hp

  have hy0 : Y0 ≤ y := by
    exact le_trans Y0_le_Ystar hy

  have hC : pivotBarrier (y : ℝ) < (mreq y : ℝ) :=
    pivotBarrier_lt_mreq_of_ge_Y0 y hy0 hp h_exists hbelow

  exact lt_of_le_of_lt hA (lt_trans hB hC)

end CaseB
end Lehmer