-- FILE: Lean/Lehmer/Pivot/FiniteTableBridge.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Data.Pivot.MreqTable : def
-/

import Lehmer.Prelude
import Lehmer.Data.Pivot.MreqTable

namespace Lehmer
namespace Pivot

/--
Choice-2 bridge:
this file does not claim a complete certified finite table in Lean.

It only exposes the exact visible prefix that has been internalized at the
data layer, together with the corresponding lookup function.
-/
def finiteMreqPrefix : List (ℕ × ℕ) :=
  Lehmer.Data.Pivot.mreqPrimeTablePrefix

/--
Lookup into the exact visible prefix internalized in `Data.Pivot.MreqTable`.
-/
def finiteMreqPrefixLookup (y : ℕ) : Option ℕ :=
  Lehmer.Data.Pivot.mreqPrimeTablePrefixLookup y

/--
Predicate expressing that `(y, m)` is certified by the visible finite prefix.
-/
def FiniteMreqCertified (y m : ℕ) : Prop :=
  finiteMreqPrefixLookup y = some m

@[simp] theorem finiteMreqPrefixLookup_3 :
    finiteMreqPrefixLookup 3 = some 3 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_5 :
    finiteMreqPrefixLookup 5 = some 7 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_7 :
    finiteMreqPrefixLookup 7 = some 15 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_11 :
    finiteMreqPrefixLookup 11 = some 27 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_13 :
    finiteMreqPrefixLookup 13 = some 41 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_17 :
    finiteMreqPrefixLookup 17 = some 62 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_19 :
    finiteMreqPrefixLookup 19 = some 85 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_23 :
    finiteMreqPrefixLookup 23 = some 115 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_29 :
    finiteMreqPrefixLookup 29 = some 150 := by
  rfl

@[simp] theorem finiteMreqPrefixLookup_31 :
    finiteMreqPrefixLookup 31 = some 186 := by
  rfl

theorem finiteMreqCertified_3 : FiniteMreqCertified 3 3 := by
  rfl

theorem finiteMreqCertified_5 : FiniteMreqCertified 5 7 := by
  rfl

theorem finiteMreqCertified_7 : FiniteMreqCertified 7 15 := by
  rfl

theorem finiteMreqCertified_11 : FiniteMreqCertified 11 27 := by
  rfl

theorem finiteMreqCertified_13 : FiniteMreqCertified 13 41 := by
  rfl

theorem finiteMreqCertified_17 : FiniteMreqCertified 17 62 := by
  rfl

theorem finiteMreqCertified_19 : FiniteMreqCertified 19 85 := by
  rfl

theorem finiteMreqCertified_23 : FiniteMreqCertified 23 115 := by
  rfl

theorem finiteMreqCertified_29 : FiniteMreqCertified 29 150 := by
  rfl

theorem finiteMreqCertified_31 : FiniteMreqCertified 31 186 := by
  rfl

/--
The currently internalized finite table is only a prefix.
This is recorded explicitly to avoid overstating coverage.
-/
def finiteMreqPrefixOnly : Bool :=
  !Lehmer.Data.Pivot.mreqPrimeTableInternalizedCompletely

@[simp] theorem finiteMreqPrefixOnly_eq_true :
    finiteMreqPrefixOnly = true := by
  rfl

end Pivot
end Lehmer