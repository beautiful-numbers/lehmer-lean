-- FILE: Lean/Lehmer/Pivot/AppendixB/BlockBounds.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AppendixB.Endpoint : def
-/

import Lehmer.Prelude
import Lehmer.Pivot.AppendixB.Endpoint

open scoped BigOperators
open Finset
open Real

namespace Lehmer
namespace Pivot

noncomputable section

/-!
# Appendix B block bounds

This file proves the clean summation bridge

`termwise integer/log bounds  ->  blockwise integer/log bounds`

for the Appendix B endpoint machinery.

Important scope:
* this file does **not** prove the termwise Taylor inequalities;
* it does **not** identify the endpoint block with `UBm`;
* it does **not** mention `mreq`.

Instead, it formalizes the mathematically exact next layer:
once termwise lower/upper bounds are available for the Appendix B truncated
numerators, the corresponding block inequalities for `LO60(i,j)` / `UP60(i,j)`
follow by summation.
-/

/-! ## Real log-factor attached to a prime -/

/--
The logarithmic factor used in Appendix B:
`log (p / (p - 1))`.
-/
def appendixBLogFactor (p : ℕ) : ℝ :=
  Real.log ((p : ℝ) / ((p : ℝ) - 1))

/-! ## Termwise integer numerators -/

namespace AppendixBIntegerEncodings

/--
Upper termwise integer numerator attached to a prime `p`.
This is the integer numerator corresponding to the truncated upper Taylor bound.
-/
def UP60Term (enc : AppendixBIntegerEncodings) (p : ℕ) : ℤ :=
    60 * enc.uU p
  - 30 * enc.u2L p
  + 20 * enc.u3U p
  - 15 * enc.u4L p
  + 12 * enc.u5U p

/--
Lower termwise integer numerator attached to a prime `p`.
This is the integer numerator corresponding to the truncated lower Taylor bound.
-/
def LO60Term (enc : AppendixBIntegerEncodings) (p : ℕ) : ℤ :=
    60 * enc.uL p
  - 30 * enc.u2U p
  + 20 * enc.u3L p
  - 15 * enc.u4U p

/--
Real upper termwise bound over the fixed denominator `DEN60`.
-/
def UP60TermRat (enc : AppendixBIntegerEncodings) (p : ℕ) : ℝ :=
  ((UP60Term enc p : ℤ) : ℝ) / (appendixBDEN60 : ℝ)

/--
Real lower termwise bound over the fixed denominator `DEN60`.
-/
def LO60TermRat (enc : AppendixBIntegerEncodings) (p : ℕ) : ℝ :=
  ((LO60Term enc p : ℤ) : ℝ) / (appendixBDEN60 : ℝ)

@[simp] theorem UP60_eq_sum_UP60Term
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    AppendixBIntegerEncodings.UP60 enc primeAt i j
      = ∑ t in Finset.Icc i (j - 1), UP60Term enc (primeAt t) := by
  simp [AppendixBIntegerEncodings.UP60, UP60Term,
    Finset.mul_sum, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem LO60_eq_sum_LO60Term
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    AppendixBIntegerEncodings.LO60 enc primeAt i j
      = ∑ t in Finset.Icc i (j - 1), LO60Term enc (primeAt t) := by
  simp [AppendixBIntegerEncodings.LO60, LO60Term,
    Finset.mul_sum, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem UP60Rat_eq_sum_UP60TermRat
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (((AppendixBIntegerEncodings.UP60 enc primeAt i j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ))
      = ∑ t in Finset.Icc i (j - 1), UP60TermRat enc (primeAt t) := by
  rw [UP60_eq_sum_UP60Term]
  simp [UP60TermRat, div_eq_mul_inv, Finset.sum_mul]

@[simp] theorem LO60Rat_eq_sum_LO60TermRat
    (enc : AppendixBIntegerEncodings)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (((AppendixBIntegerEncodings.LO60 enc primeAt i j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ))
      = ∑ t in Finset.Icc i (j - 1), LO60TermRat enc (primeAt t) := by
  rw [LO60_eq_sum_LO60Term]
  simp [LO60TermRat, div_eq_mul_inv, Finset.sum_mul]

end AppendixBIntegerEncodings

/-! ## Consecutive-block log sum -/

/--
The sum of log-factors over a consecutive prime block `[i,j)`.
-/
def appendixBBlockLogSum (primeAt : ℕ → ℕ) (i j : ℕ) : ℝ :=
  ∑ t in Finset.Icc i (j - 1), appendixBLogFactor (primeAt t)

/-! ## Termwise certificate interface -/

/--
Certificate interface for the termwise Appendix B inequalities.

This is the precise place where the future Taylor/truncation proof layer plugs
into the summation layer proved in this file.
-/
structure AppendixBTermwiseLogBounds
    (enc : AppendixBIntegerEncodings) where
  lower :
    ∀ p : ℕ,
      AppendixBIntegerEncodings.LO60TermRat enc p ≤ appendixBLogFactor p
  upper :
    ∀ p : ℕ,
      appendixBLogFactor p ≤ AppendixBIntegerEncodings.UP60TermRat enc p

namespace AppendixBTermwiseLogBounds

/--
Summed lower bound over a consecutive prime block.
-/
theorem block_lower
    {enc : AppendixBIntegerEncodings}
    (cert : AppendixBTermwiseLogBounds enc)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (((AppendixBIntegerEncodings.LO60 enc primeAt i j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ))
      ≤ appendixBBlockLogSum primeAt i j := by
  calc
    (((AppendixBIntegerEncodings.LO60 enc primeAt i j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ))
      = ∑ t in Finset.Icc i (j - 1),
          AppendixBIntegerEncodings.LO60TermRat enc (primeAt t) := by
          simpa using
            AppendixBIntegerEncodings.LO60Rat_eq_sum_LO60TermRat enc primeAt i j
    _ ≤ ∑ t in Finset.Icc i (j - 1), appendixBLogFactor (primeAt t) := by
          exact Finset.sum_le_sum (fun t _ht => cert.lower (primeAt t))
    _ = appendixBBlockLogSum primeAt i j := by
          rfl

/--
Summed upper bound over a consecutive prime block.
-/
theorem block_upper
    {enc : AppendixBIntegerEncodings}
    (cert : AppendixBTermwiseLogBounds enc)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    appendixBBlockLogSum primeAt i j
      ≤ (((AppendixBIntegerEncodings.UP60 enc primeAt i j : ℤ) : ℝ) /
          (appendixBDEN60 : ℝ)) := by
  calc
    appendixBBlockLogSum primeAt i j
      = ∑ t in Finset.Icc i (j - 1), appendixBLogFactor (primeAt t) := by
          rfl
    _ ≤ ∑ t in Finset.Icc i (j - 1),
          AppendixBIntegerEncodings.UP60TermRat enc (primeAt t) := by
          exact Finset.sum_le_sum (fun t _ht => cert.upper (primeAt t))
    _ = (((AppendixBIntegerEncodings.UP60 enc primeAt i j : ℤ) : ℝ) /
          (appendixBDEN60 : ℝ)) := by
          symm
          simpa using
            AppendixBIntegerEncodings.UP60Rat_eq_sum_UP60TermRat enc primeAt i j

/--
The full block inequality, matching the shape of Appendix B:
`LO60 / DEN60 ≤ Σ log(pt/(pt-1)) ≤ UP60 / DEN60`.
-/
theorem block_bounds
    {enc : AppendixBIntegerEncodings}
    (cert : AppendixBTermwiseLogBounds enc)
    (primeAt : ℕ → ℕ)
    (i j : ℕ) :
    (((AppendixBIntegerEncodings.LO60 enc primeAt i j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ))
      ≤ appendixBBlockLogSum primeAt i j
      ∧
      appendixBBlockLogSum primeAt i j
        ≤ (((AppendixBIntegerEncodings.UP60 enc primeAt i j : ℤ) : ℝ) /
            (appendixBDEN60 : ℝ)) := by
  exact ⟨block_lower cert primeAt i j, block_upper cert primeAt i j⟩

end AppendixBTermwiseLogBounds

/-! ## Endpoint-specialized packaging -/

/--
Endpoint-specialized certificate package:
* integer encodings,
* termwise proof layer,
* endpoint indexing data.
-/
structure AppendixBEndpointBlockBoundsData where
  enc : AppendixBIntegerEncodings
  termCert : AppendixBTermwiseLogBounds enc
  endpoint : AppendixBEndpointIndexData

namespace AppendixBEndpointBlockBoundsData

/--
The endpoint block log sum.
-/
def endpointLogSum (D : AppendixBEndpointBlockBoundsData) : ℝ :=
  appendixBBlockLogSum D.endpoint.primeAt D.endpoint.i D.endpoint.j

/--
Endpoint lower block bound.
-/
theorem endpoint_lower
    (D : AppendixBEndpointBlockBoundsData) :
    (((AppendixBIntegerEncodings.LO60 D.enc D.endpoint.primeAt
          D.endpoint.i D.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ))
      ≤ D.endpointLogSum := by
  exact AppendixBTermwiseLogBounds.block_lower
    D.termCert D.endpoint.primeAt D.endpoint.i D.endpoint.j

/--
Endpoint upper block bound.
-/
theorem endpoint_upper
    (D : AppendixBEndpointBlockBoundsData) :
    D.endpointLogSum
      ≤ (((AppendixBIntegerEncodings.UP60 D.enc D.endpoint.primeAt
            D.endpoint.i D.endpoint.j : ℤ) : ℝ) /
          (appendixBDEN60 : ℝ)) := by
  exact AppendixBTermwiseLogBounds.block_upper
    D.termCert D.endpoint.primeAt D.endpoint.i D.endpoint.j

/--
Endpoint full block inequality.
-/
theorem endpoint_bounds
    (D : AppendixBEndpointBlockBoundsData) :
    (((AppendixBIntegerEncodings.LO60 D.enc D.endpoint.primeAt
          D.endpoint.i D.endpoint.j : ℤ) : ℝ) /
        (appendixBDEN60 : ℝ))
      ≤ D.endpointLogSum
      ∧
      D.endpointLogSum
        ≤ (((AppendixBIntegerEncodings.UP60 D.enc D.endpoint.primeAt
              D.endpoint.i D.endpoint.j : ℤ) : ℝ) /
            (appendixBDEN60 : ℝ)) := by
  exact AppendixBTermwiseLogBounds.block_bounds
    D.termCert D.endpoint.primeAt D.endpoint.i D.endpoint.j

/--
The endpoint block length is exactly the packaged `m`.
-/
theorem endpoint_length_eq_m
    (D : AppendixBEndpointBlockBoundsData) :
    D.endpoint.toPrimeBlock.length = D.endpoint.m := by
  exact D.endpoint.length_eq_m

/--
The endpoint block starts at the packaged `y`.
-/
theorem endpoint_startPrime_eq_y
    (D : AppendixBEndpointBlockBoundsData) :
    D.endpoint.toPrimeBlock.startPrime = D.endpoint.y := by
  exact D.endpoint.startPrime_eq_y

end AppendixBEndpointBlockBoundsData

end

end Pivot
end Lehmer