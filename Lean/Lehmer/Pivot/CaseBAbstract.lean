-- FILE: Lean/Lehmer/Pivot/CaseBAbstract.lean
/-
IMPORT CLASSIFICATION
- Mathlib.Data.Nat.Prime : def thm
- Mathlib.Data.Nat.Totient : def thm
-/

import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Totient

namespace Lehmer
namespace Pivot

/-!
# Abstract pivot-side closure skeleton for Case B

This file is a local abstract skeleton for the terminal pivot-side contradiction.

Scope:
* local prototype definitions only;
* no dependency on the full project DAG;
* no axioms;
* demand / supply / no-crossing are modeled as abstract interfaces.
-/

/--
Local prototype definition of a Lehmer composite:
`n` is non-prime, strictly greater than `1`, and `φ(n)` divides `n - 1`.
-/
def IsLehmerComposite (n : ℕ) : Prop :=
  ¬ Nat.Prime n ∧ 1 < n ∧ Nat.totient n ∣ (n - 1)

/-- `P_minus n` : the least prime factor of `n`. -/
noncomputable def PMinus (n : ℕ) : ℕ :=
  n.minFac

/--
Semantic definition of `y`-rough:
every prime divisor of `n` is at least `y`.
-/
def YRough (n y : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → y ≤ p

/--
Equivalence between the semantic `y`-rough definition and the inequality
`y ≤ PMinus n`, under the hypothesis `1 < n`.
-/
theorem yrough_iff_le_PMinus
    {n y : ℕ} (hn : 1 < n) :
    YRough n y ↔ y ≤ PMinus n := by
  constructor
  · intro h
    exact h (PMinus n) (Nat.minFac_prime (ne_of_gt hn)) (Nat.minFac_dvd n)
  · intro h
    intro p hp hpd
    have hmin : PMinus n ≤ p := Nat.minFac_le_of_dvd hp.two_le hpd
    exact le_trans h hmin

/-- Directional form: `y`-rough implies `y ≤ PMinus n`. -/
theorem le_PMinus_of_yrough
    {n y : ℕ}
    (hn : 1 < n) (hrough : YRough n y) :
    y ≤ PMinus n := by
  exact (yrough_iff_le_PMinus hn).mp hrough

/-- Converse directional form: `y ≤ PMinus n` implies `y`-rough. -/
theorem yrough_of_le_PMinus
    {n y : ℕ}
    (hn : 1 < n) (h : y ≤ PMinus n) :
    YRough n y := by
  exact (yrough_iff_le_PMinus hn).mpr h

section AbstractCaseB

variable (omegaFn : ℕ → ℕ)
variable (mreqFn : ℕ → ℕ)
variable (MFn : ℕ → ℕ)
variable (YstarVal : ℕ)

/-- DAG node: pivot demand gives a lower bound. -/
def MeetsPivotDemand (n : ℕ) : Prop :=
  mreqFn (PMinus n) ≤ omegaFn n

/-- DAG node: structural supply gives an upper bound. -/
def HasSupplyBound (n : ℕ) : Prop :=
  omegaFn n ≤ MFn (PMinus n)

/-- DAG node: analytic no-crossing beyond `Y^*`. -/
def NoCrossingBeyondYstar : Prop :=
  ∀ y : ℕ, YstarVal ≤ y → Nat.Prime y → MFn y < mreqFn y

/--
Terminal pivot-side contradiction:
if demand, supply, and no-crossing all hold at the pivot `PMinus n`,
then one gets a contradiction.
-/
theorem contradiction_of_pivot_demand_supply_noCrossing
    {n : ℕ}
    (hLehmer : IsLehmerComposite n)
    (hBound : YstarVal ≤ PMinus n)
    (hDemand : MeetsPivotDemand omegaFn mreqFn n)
    (hSupply : HasSupplyBound omegaFn MFn n)
    (hNoCross : NoCrossingBeyondYstar mreqFn MFn YstarVal) :
    False := by
  have hn : 1 < n := hLehmer.2.1
  have hPPrime : Nat.Prime (PMinus n) := Nat.minFac_prime (ne_of_gt hn)

  have hMltMreq : MFn (PMinus n) < mreqFn (PMinus n) := by
    exact hNoCross (PMinus n) hBound hPPrime

  have h1 : mreqFn (PMinus n) ≤ omegaFn n := hDemand
  have h2 : omegaFn n ≤ MFn (PMinus n) := hSupply
  have h3 : mreqFn (PMinus n) ≤ MFn (PMinus n) := le_trans h1 h2
  have h4 : mreqFn (PMinus n) < mreqFn (PMinus n) := lt_of_le_of_lt h3 hMltMreq

  exact (Nat.lt_irrefl (mreqFn (PMinus n))) h4

/--
Paper-facing form:
if `n` is `Y^*`-rough and satisfies the three DAG nodes,
then one gets a contradiction.
-/
theorem contradiction_of_yrough_pivot_demand_supply_noCrossing
    {n : ℕ}
    (hLehmer : IsLehmerComposite n)
    (hRough : YRough n YstarVal)
    (hDemand : MeetsPivotDemand omegaFn mreqFn n)
    (hSupply : HasSupplyBound omegaFn MFn n)
    (hNoCross : NoCrossingBeyondYstar mreqFn MFn YstarVal) :
    False := by
  have hn : 1 < n := hLehmer.2.1
  have hBound : YstarVal ≤ PMinus n := le_PMinus_of_yrough hn hRough
  exact contradiction_of_pivot_demand_supply_noCrossing
    omegaFn mreqFn MFn YstarVal
    hLehmer hBound hDemand hSupply hNoCross

/--
Terminal exclusion corollary:
every candidate satisfying the three DAG nodes must lie below `Y^*`.
-/
theorem pminus_lt_Ystar_of_demand_supply_noCrossing
    {n : ℕ}
    (hLehmer : IsLehmerComposite n)
    (hDemand : MeetsPivotDemand omegaFn mreqFn n)
    (hSupply : HasSupplyBound omegaFn MFn n)
    (hNoCross : NoCrossingBeyondYstar mreqFn MFn YstarVal) :
    PMinus n < YstarVal := by
  by_contra hNotLt
  have hBound : YstarVal ≤ PMinus n := le_of_not_lt hNotLt
  exact contradiction_of_pivot_demand_supply_noCrossing
    omegaFn mreqFn MFn YstarVal
    hLehmer hBound hDemand hSupply hNoCross

end AbstractCaseB

end Pivot
end Lehmer