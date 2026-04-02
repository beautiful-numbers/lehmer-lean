-- FILE: Lean/Lehmer/Pivot/AppendixB/Endpoint.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.LargeRangeExplicit : def thm
- Lehmer.Pivot.UBm : def thm
- Lehmer.Data.Pivot.Log2Enclosure : def
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.LargeRangeExplicit
import Lehmer.Pivot.UBm
import Lehmer.Data.Pivot.Log2Enclosure

open scoped BigOperators
open Finset

namespace Lehmer
namespace Pivot

/-!
# Appendix B endpoint: integer-layer packaging only

This file is intentionally **scope-reduced**.

It contains only the endpoint-local Appendix B objects that can be introduced
without any new axioms and without any incomplete proof:
* the official numerical constants,
* the fixed integer enclosure data for `log 2`,
* the integer truncation payload (`uL`, `uU`, `u2L`, ...),
* the integer block aggregators `UP60` / `LO60`,
* the consecutive-prime-block packaging,
* the endpoint packaging `y = p_i`, `m = j - i`,
* and the endpoint-local prime-index bridge payload toward `nthPrimeFrom`.

It does **not** yet prove:
* integer block -> sum of logs,
* sum of logs -> product,
* endpoint block = `UBm y m`,
* the endpoint theorem on `UBm`,
* the local corollary on `mreq`.

Those belong in later proved layers once the integer certificate data and the
prime-index bridge are fully internalized.
-/

/-! ## B.1 Official constants -/

/--
Appendix B decimal precision parameter `D = 40`.
-/
def appendixBD : ℕ := 40

/--
Appendix B fixed decimal denominator `S = 10^D`.
-/
def appendixBS : ℕ := 10 ^ appendixBD

/--
Appendix B common denominator `DEN60 = 60 * S = 60 * 10^40`.
-/
def appendixBDEN60 : ℕ := 60 * appendixBS

@[simp] theorem appendixBD_eq : appendixBD = 40 := rfl

@[simp] theorem appendixBS_eq : appendixBS = 10 ^ 40 := by
  rfl

@[simp] theorem appendixBDEN60_eq :
    appendixBDEN60 = 60 * 10 ^ 40 := by
  rfl

/-! ## B.2 Fixed rational enclosure of `log 2` packaged at integer level -/

/--
Common denominator used in the paper for the rational enclosure
`L_-`, `L_+` of `log 2`.
-/
def appendixBLog2RatDen : ℕ := 10 ^ 80

/--
Numerator of the lower rational enclosure `L_-` of `log 2`.
-/
def appendixBLog2LowerNum : ℤ :=
  69314718055994530941723212145817656807550013436025525412068000949339362196969471

/--
Numerator of the upper rational enclosure `L_+` of `log 2`.
-/
def appendixBLog2UpperNum : ℤ :=
  69314718055994530941723212145817656807550013436025525412068000949339362196969472

/--
Appendix B lower integer enclosure `L(60)_-`.
-/
def appendixBL60minus : ℤ :=
  4158883083359671856503392728749059408459

/--
Appendix B upper integer enclosure `L(60)_+`.
-/
def appendixBL60plus : ℤ :=
  4158883083359671856503392728749059408460

@[simp] theorem appendixBLog2RatDen_eq :
    appendixBLog2RatDen = 10 ^ 80 := by
  rfl

@[simp] theorem appendixBL60minus_eq :
    appendixBL60minus =
      4158883083359671856503392728749059408459 := by
  rfl

@[simp] theorem appendixBL60plus_eq :
    appendixBL60plus =
      4158883083359671856503392728749059408460 := by
  rfl

@[simp] theorem appendixBL60_gap :
    appendixBL60plus - appendixBL60minus = 1 := by
  norm_num [appendixBL60plus, appendixBL60minus]

/--
Integer-level packaging of the fixed `log 2` enclosure used by Appendix B.
-/
structure AppendixBLog2IntegerEnclosure where
  ratDen : ℕ
  lowerNum : ℤ
  upperNum : ℤ
  den60 : ℕ
  L60minus : ℤ
  L60plus : ℤ

/--
Canonical integer enclosure package extracted from Appendix B.
-/
def appendixBLog2IntegerEnclosure : AppendixBLog2IntegerEnclosure where
  ratDen := appendixBLog2RatDen
  lowerNum := appendixBLog2LowerNum
  upperNum := appendixBLog2UpperNum
  den60 := appendixBDEN60
  L60minus := appendixBL60minus
  L60plus := appendixBL60plus

@[simp] theorem appendixBLog2IntegerEnclosure_den60 :
    appendixBLog2IntegerEnclosure.den60 = appendixBDEN60 := by
  rfl

@[simp] theorem appendixBLog2IntegerEnclosure_L60minus :
    appendixBLog2IntegerEnclosure.L60minus = appendixBL60minus := by
  rfl

@[simp] theorem appendixBLog2IntegerEnclosure_L60plus :
    appendixBLog2IntegerEnclosure.L60plus = appendixBL60plus := by
  rfl

/-! ## B.3 Integer truncation payload -/

/--
Appendix B integer truncation payload over the fixed denominator `S = 10^40`.

These are **data objects**, not axioms: a later data file can instantiate this
structure with the actual integer tables/certificate values.
-/
structure AppendixBIntegerEncodings where
  uL  : ℕ → ℤ
  uU  : ℕ → ℤ
  u2L : ℕ → ℤ
  u2U : ℕ → ℤ
  u3L : ℕ → ℤ
  u3U : ℕ → ℤ
  u4L : ℕ → ℤ
  u4U : ℕ → ℤ
  u5U : ℕ → ℤ

namespace AppendixBIntegerEncodings

/--
Upper block numerator
`UP60(i,j)` for a consecutive prime block `[i,j)`.
-/
def UP60
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) : ℤ :=
    60 * ∑ t in Finset.Icc i (j - 1), enc.uU (primeAt t)
  - 30 * ∑ t in Finset.Icc i (j - 1), enc.u2L (primeAt t)
  + 20 * ∑ t in Finset.Icc i (j - 1), enc.u3U (primeAt t)
  - 15 * ∑ t in Finset.Icc i (j - 1), enc.u4L (primeAt t)
  + 12 * ∑ t in Finset.Icc i (j - 1), enc.u5U (primeAt t)

/--
Lower block numerator
`LO60(i,j)` for a consecutive prime block `[i,j)`.
-/
def LO60
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) : ℤ :=
    60 * ∑ t in Finset.Icc i (j - 1), enc.uL (primeAt t)
  - 30 * ∑ t in Finset.Icc i (j - 1), enc.u2U (primeAt t)
  + 20 * ∑ t in Finset.Icc i (j - 1), enc.u3L (primeAt t)
  - 15 * ∑ t in Finset.Icc i (j - 1), enc.u4U (primeAt t)

/--
Upper block packaged with the fixed denominator `DEN60`.
-/
def UP60WithDen
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) : ℤ × ℕ :=
  (UP60 enc primeAt i j, appendixBDEN60)

/--
Lower block packaged with the fixed denominator `DEN60`.
-/
def LO60WithDen
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) : ℤ × ℕ :=
  (LO60 enc primeAt i j, appendixBDEN60)

@[simp] theorem UP60WithDen_fst
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (UP60WithDen enc primeAt i j).1 = UP60 enc primeAt i j := by
  rfl

@[simp] theorem UP60WithDen_snd
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (UP60WithDen enc primeAt i j).2 = appendixBDEN60 := by
  rfl

@[simp] theorem LO60WithDen_fst
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (LO60WithDen enc primeAt i j).1 = LO60 enc primeAt i j := by
  rfl

@[simp] theorem LO60WithDen_snd
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (LO60WithDen enc primeAt i j).2 = appendixBDEN60 := by
  rfl

end AppendixBIntegerEncodings

/-! ## B.4 Consecutive-prime-block packaging -/

/--
Consecutive prime block `[i,j)` in a global prime list `primeAt`.
-/
structure AppendixBPrimeBlock where
  primeAt : ℕ → ℕ
  i : ℕ
  j : ℕ

namespace AppendixBPrimeBlock

/--
Block length `m = j - i`.
-/
def length (B : AppendixBPrimeBlock) : ℕ :=
  B.j - B.i

/--
Block starting value `y = p_i`.
-/
def startPrime (B : AppendixBPrimeBlock) : ℕ :=
  B.primeAt B.i

/--
Product kernel attached to the block.
This is only a packaging definition; no identification with `UBm` is made here.
-/
def primeBlockProd (B : AppendixBPrimeBlock) : ℚ :=
  ∏ t in Finset.Icc B.i (B.j - 1),
    ((B.primeAt t : ℚ) / ((B.primeAt t : ℚ) - 1))

@[simp] theorem length_eq (B : AppendixBPrimeBlock) :
    B.length = B.j - B.i := by
  rfl

@[simp] theorem startPrime_eq (B : AppendixBPrimeBlock) :
    B.startPrime = B.primeAt B.i := by
  rfl

end AppendixBPrimeBlock

/-! ## B.5 Endpoint-local packaging `y = p_i`, `m = j - i` -/

/--
Endpoint-local package for the Appendix B certificate line shape.

This packages exactly the indexing information used later for the bridge
toward the endpoint theorem:
* `y = p_i`,
* `m = j - i`,
* block `[i,j)`,
* and the local identification of the block indexing with `nthPrimeFrom y`.
-/
structure AppendixBEndpointIndexData where
  primeAt : ℕ → ℕ
  i : ℕ
  j : ℕ
  y : ℕ
  m : ℕ
  hy : y = primeAt i
  hm : m = j - i
  hj : j = i + m
  hindex : ∀ k, k < m → primeAt (i + k) = nthPrimeFrom y k

namespace AppendixBEndpointIndexData

/--
Underlying consecutive block associated to the endpoint data.
-/
def toPrimeBlock (E : AppendixBEndpointIndexData) : AppendixBPrimeBlock where
  primeAt := E.primeAt
  i := E.i
  j := E.j

/--
The start prime of the underlying block is `y`.
-/
theorem startPrime_eq_y (E : AppendixBEndpointIndexData) :
    E.toPrimeBlock.startPrime = E.y := by
  simp [AppendixBPrimeBlock.startPrime, toPrimeBlock, E.hy]

/--
The block length is `m`.
-/
theorem length_eq_m (E : AppendixBEndpointIndexData) :
    E.toPrimeBlock.length = E.m := by
  simp [AppendixBPrimeBlock.length, toPrimeBlock, E.hj]

/--
Every indexed point inside the endpoint block agrees with `nthPrimeFrom y`.
-/
theorem primeAt_add_eq_nthPrimeFrom
    (E : AppendixBEndpointIndexData)
    {k : ℕ} (hk : k < E.m) :
    E.primeAt (E.i + k) = nthPrimeFrom E.y k := by
  exact E.hindex k hk

end AppendixBEndpointIndexData

/-! ## B.6 Canonical endpoint-local constants from the large-range endpoint -/

/--
Endpoint-local `y0` used by the explicit large-range endpoint certificate.
-/
def appendixBEndpointY0 : ℕ := Y0

/--
Endpoint-local lower index `m`.
-/
def appendixBEndpointM : ℕ := largeRangeEndpointM

/--
Endpoint-local upper index `n = m + y - 1` recorded in the endpoint certificate.
This is packaged here only as data imported from the explicit endpoint layer.
-/
def appendixBEndpointN : ℕ := largeRangeEndpointN

@[simp] theorem appendixBEndpointY0_eq :
    appendixBEndpointY0 = Y0 := by
  rfl

@[simp] theorem appendixBEndpointM_eq :
    appendixBEndpointM = 87302 := by
  exact largeRangeEndpointM_eq

@[simp] theorem appendixBEndpointN_eq :
    appendixBEndpointN = 117301 := by
  exact largeRangeEndpointN_eq

/--
Endpoint-local package containing only the data that are already available
without any new theorem.
-/
structure AppendixBEndpointData where
  y0 : ℕ
  m : ℕ
  n : ℕ
  log2Int : AppendixBLog2IntegerEnclosure

/--
Canonical endpoint-local package.
-/
def appendixBEndpointData : AppendixBEndpointData where
  y0 := appendixBEndpointY0
  m := appendixBEndpointM
  n := appendixBEndpointN
  log2Int := appendixBLog2IntegerEnclosure

@[simp] theorem appendixBEndpointData_y0 :
    appendixBEndpointData.y0 = Y0 := by
  rfl

@[simp] theorem appendixBEndpointData_m :
    appendixBEndpointData.m = 87302 := by
  rfl

@[simp] theorem appendixBEndpointData_n :
    appendixBEndpointData.n = 117301 := by
  rfl

@[simp] theorem appendixBEndpointData_den60 :
    appendixBEndpointData.log2Int.den60 = appendixBDEN60 := by
  rfl

@[simp] theorem appendixBEndpointData_L60minus :
    appendixBEndpointData.log2Int.L60minus = appendixBL60minus := by
  rfl

@[simp] theorem appendixBEndpointData_L60plus :
    appendixBEndpointData.log2Int.L60plus = appendixBL60plus := by
  rfl

end Pivot
end Lehmer