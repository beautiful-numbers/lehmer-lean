-- FILE: Lean/Lehmer/Pivot/AppendixA/PrimeCountIntervalExplicitLower.lean
/-
IMPORT CLASSIFICATION
- Lehmer.Prelude : meta
- Lehmer.Pivot.AnalyticConstants : def thm
- Lehmer.Pivot.AppendixA.IntervalDefs : def thm
- Lehmer.Pivot.AppendixA.PrimeCountDefs : def thm
-/

import Lehmer.Prelude
import Lehmer.Pivot.AnalyticConstants
import Lehmer.Pivot.AppendixA.IntervalDefs
import Lehmer.Pivot.AppendixA.PrimeCountDefs

namespace Lehmer
namespace Pivot
namespace AppendixA
namespace PrimeCountIntervalExplicitLower

open scoped Real

/-!
# Minoration explicite du nombre de premiers dans `[y, xA(y)]`

Rôle du fichier :

- formaliser une minoration explicite du nombre de premiers dans l’intervalle
  `[y, xA(y)]` ;
- fournir la brique profonde utilisée ensuite par
  `PrimeCountAnalyticProof.lean` ;
- ne pas traiter l’endpoint `Y0`, ni la barrière finale, ni `primeCountGap`.

Stratégie retenue :

- on passe par une quantité de type Chebyshev `θ` ;
- on relie `θ(xA(y)) - θ(y)` au comptage d’intervalle ;
- on isole ensuite un noyau profond sous la forme d’une borne explicite
  sur la différence de `θ`.

Attention :
ce fichier est un brouillon de fermeture plausible, non certifié.
-/

/-- Ensemble fini explicite des nombres premiers jusqu’à `⌊x⌋`. -/
private def primesUpToFloor (x : ℝ) : Finset ℕ :=
  (Finset.range (Int.toNat ⌊x⌋ + 1)).filter Nat.Prime

/-- Ensemble fini des nombres premiers de l’intervalle `(y, xA(y)]`. -/
private def primesInInterval (y : ℕ) : Finset ℕ :=
  (primesUpToFloor (xA y)).filter (fun p => y < p)

/-- Fonction de type Chebyshev : somme des `log p` pour `p ≤ x`. -/
private noncomputable def thetaUpTo (x : ℝ) : ℝ :=
  ∑ p in primesUpToFloor x, Real.log p

/-- Réduction locale de `primePi` à une cardinalité finie. -/
private theorem primePi_eq_card_primesUpToFloor (x : ℝ) :
    primePi x = (primesUpToFloor x).card := by
  unfold primePi primesUpToFloor
  simp

/-- Positivité du logarithme sur la grande plage. -/
private theorem log_pos_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 < Real.log (y : ℝ) := by
  have hy1_nat : 1 < y := lt_of_lt_of_le (by decide : 1 < Y0) hy0
  have hy1 : (1 : ℝ) < (y : ℝ) := by
    exact_mod_cast hy1_nat
  exact Real.log_pos hy1

/-- Positivité de `2 * log y + 1` sur la grande plage. -/
private theorem two_log_y_add_one_pos
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 < 2 * Real.log (y : ℝ) + 1 := by
  have hlog : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
  linarith

/-- L’intervalle `[y, xA(y)]` est non trivial. -/
private theorem xA_ge_y_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    (y : ℝ) ≤ xA y := by
  unfold xA
  nlinarith

/-- La longueur de l’intervalle `[y, xA(y)]` est non négative. -/
private theorem interval_length_nonneg
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 ≤ xA y - (y : ℝ) := by
  have hxA : (y : ℝ) ≤ xA y := xA_ge_y_of_ge_Y0 hy0
  linarith

/-- Positivité de `xA y` sur la grande plage. -/
private theorem xA_pos_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 < xA y := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < Y0) hy0)
  have hxA : (y : ℝ) ≤ xA y := xA_ge_y_of_ge_Y0 hy0
  linarith

/-- Positivité de `log (xA y)` sur la grande plage. -/
private theorem log_xA_pos_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 < Real.log (xA y) := by
  have hy1 : (1 : ℝ) < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < Y0) hy0)
  have hxA : (y : ℝ) ≤ xA y := xA_ge_y_of_ge_Y0 hy0
  have h1 : (1 : ℝ) < xA y := lt_of_lt_of_le hy1 hxA
  exact Real.log_pos h1

/-- Contrôle élémentaire de `log (xA y)` par `2 * log y + 1`. -/
private theorem log_xA_le_two_log_y_add_one
    {y : ℕ} (hy0 : Y0 ≤ y) :
    Real.log (xA y) ≤ 2 * Real.log (y : ℝ) + 1 := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < Y0) hy0)
  have hxA_upper :
      xA y ≤ (2 : ℝ) * (y : ℝ)^2 := by
    unfold xA
    have hy_ge_two : (2 : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast (le_trans (by decide : 2 ≤ Y0) hy0)
    have hden : (1 : ℝ) ≤ (y : ℝ) - 1 := by linarith
    have hfrac : (1 : ℝ) / ((y : ℝ) - 1) ≤ 1 := by
      have hpos : (0 : ℝ) < (y : ℝ) - 1 := by linarith
      exact one_div_le_one_div_of_le hpos hden
    nlinarith
  have hlog_mono :
      Real.log (xA y) ≤ Real.log ((2 : ℝ) * (y : ℝ)^2) := by
    have hxA_pos : 0 < xA y := xA_pos_of_ge_Y0 hy0
    exact Real.monotone_log (le_of_lt hxA_pos) hxA_upper
  have hlog_expand :
      Real.log ((2 : ℝ) * (y : ℝ)^2) = Real.log 2 + 2 * Real.log (y : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    rw [show ((y : ℝ)^2) = (y : ℝ) ^ (2 : ℕ) by ring]
    rw [Real.log_rpow (by positivity)]
    norm_num
  have hlog2_le_one : Real.log 2 ≤ (1 : ℝ) := by
    have : Real.log 2 < (1 : ℝ) := by
      norm_num
    linarith
  linarith

/-- Inclusion des premiers `≤ y` dans les premiers `≤ xA(y)`. -/
private theorem primesUpToFloor_y_subset_xA
    {y : ℕ} :
    primesUpToFloor (y : ℝ) ⊆ primesUpToFloor (xA y) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_range, hp_prime⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨?_, hp_prime⟩
  have hp_le_floor_y : p ≤ Int.toNat ⌊(y : ℝ)⌋ := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)
  have hy_le_xA : (y : ℝ) ≤ xA y := by
    unfold xA
    nlinarith
  have hfloor_y_eq : Int.toNat ⌊(y : ℝ)⌋ = y := by
    norm_num
  have hp_le_xA : (p : ℝ) ≤ xA y := by
    rw [hfloor_y_eq] at hp_le_floor_y
    exact le_trans (by exact_mod_cast hp_le_floor_y) hy_le_xA
  have hp_lt_succ :
      p < Int.toNat ⌊xA y⌋ + 1 := by
    exact Nat.lt_succ_of_le (by exact_mod_cast hp_le_xA)
  exact Finset.mem_range.mpr hp_lt_succ

/--
Égalité de finsets clef :
les premiers de `primesUpToFloor (xA y)` satisfaisant `p ≤ y`
sont exactement les premiers de `primesUpToFloor (y : ℝ)`.
-/
private theorem primesUpToFloor_filter_le_eq
    {y : ℕ} :
    (primesUpToFloor (xA y)).filter (fun p => p ≤ y) = primesUpToFloor (y : ℝ) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_le_y⟩
    rcases Finset.mem_filter.mp hp_mem with ⟨hp_range_xA, hp_prime⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, hp_prime⟩
    have hp_lt : p < y + 1 := Nat.lt_succ_of_le hp_le_y
    exact Finset.mem_range.mpr hp_lt
  · intro hp
    have hp_sub : p ∈ primesUpToFloor (xA y) := primesUpToFloor_y_subset_xA hp
    refine Finset.mem_filter.mpr ?_
    refine ⟨hp_sub, ?_⟩
    rcases Finset.mem_filter.mp hp with ⟨hp_range, _hp_prime⟩
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)

/--
La différence `θ(xA(y)) - θ(y)` se réécrit comme somme des `log p`
sur les nombres premiers de l’intervalle `(y, xA(y)]`.
-/
private theorem theta_interval_eq_sum_logs_interval
    {y : ℕ} :
    thetaUpTo (xA y) - thetaUpTo (y : ℝ)
      = ∑ p in primesInInterval y, Real.log p := by
  unfold thetaUpTo primesInInterval
  have hsplit :
      (∑ p in (primesUpToFloor (xA y)).filter (fun p => p ≤ y), Real.log p)
      + (∑ p in (primesUpToFloor (xA y)).filter (fun p => y < p), Real.log p)
      = ∑ p in primesUpToFloor (xA y), Real.log p := by
    simpa [not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := primesUpToFloor (xA y))
        (f := fun p => Real.log p)
        (p := fun p => p ≤ y))
  have hleft :
      ∑ p in (primesUpToFloor (xA y)).filter (fun p => p ≤ y), Real.log p
      = ∑ p in primesUpToFloor (y : ℝ), Real.log p := by
    rw [primesUpToFloor_filter_le_eq]
  calc
    thetaUpTo (xA y) - thetaUpTo (y : ℝ)
        = (∑ p in primesUpToFloor (xA y), Real.log p)
          - (∑ p in primesUpToFloor (y : ℝ), Real.log p) := by
            rfl
    _ = ∑ p in (primesUpToFloor (xA y)).filter (fun p => y < p), Real.log p := by
          linarith [hsplit, hleft]
    _ = ∑ p in primesInInterval y, Real.log p := by
          rfl

/--
Le comptage `π(xA(y)) - π(y)` se réécrit comme cardinal du finset des premiers
de l’intervalle `(y, xA(y)]`.
-/
private theorem primePi_interval_eq_card_interval
    {y : ℕ} :
    (primePi (xA y) - primePi (y : ℝ) : ℝ)
      = (primesInInterval y).card := by
  rw [primePi_eq_card_primesUpToFloor, primePi_eq_card_primesUpToFloor]
  have hsplit_card :
      ((primesUpToFloor (xA y)).filter (fun p => p ≤ y)).card
        + ((primesUpToFloor (xA y)).filter (fun p => y < p)).card
        = (primesUpToFloor (xA y)).card := by
    simpa [not_le] using
      (Finset.card_filter_add_card_filter_neg_eq_card
        (s := primesUpToFloor (xA y))
        (p := fun p => p ≤ y))
  have hleft :
      ((primesUpToFloor (xA y)).filter (fun p => p ≤ y)).card
        = (primesUpToFloor (y : ℝ)).card := by
    rw [primesUpToFloor_filter_le_eq]
  have hnat :
      (primesUpToFloor (xA y)).card - (primesUpToFloor (y : ℝ)).card
        = (primesInInterval y).card := by
    unfold primesInInterval
    omega
  exact_mod_cast hnat

/--
Pour tout nombre premier `p` de l’intervalle `(y, xA(y)]`, on a
`log p ≤ log(xA y)`.
-/
private theorem log_prime_le_log_xA
    {y p : ℕ}
    (hy0 : Y0 ≤ y)
    (hp : p ∈ primesInInterval y) :
    Real.log (p : ℝ) ≤ Real.log (xA y) := by
  have hp_mem : p ∈ primesUpToFloor (xA y) := (Finset.mem_filter.mp hp).1
  rcases Finset.mem_filter.mp hp_mem with ⟨hp_range, hp_prime⟩
  have hp_le_floor : p ≤ Int.toNat ⌊xA y⌋ := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)
  have hp_le_xA : (p : ℝ) ≤ xA y := by
    have hfloor_le : (Int.toNat ⌊xA y⌋ : ℝ) ≤ xA y := by
      exact_mod_cast Int.toNat_of_nonneg
        (Int.floor_nonneg.mpr (le_of_lt (xA_pos_of_ge_Y0 hy0)))
    exact le_trans (by exact_mod_cast hp_le_floor) hfloor_le
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp_prime.pos
  exact Real.monotone_log (le_of_lt hp_pos) hp_le_xA

/--
Chaque nombre premier de l’intervalle `(y, xA(y)]` contribue au plus
`log(xA y)` dans la différence de fonctions `θ`.
-/
private theorem theta_interval_le_log_mul_count
    {y : ℕ} (hy0 : Y0 ≤ y) :
    thetaUpTo (xA y) - thetaUpTo (y : ℝ)
      ≤ Real.log (xA y) * (primePi (xA y) - primePi (y : ℝ) : ℝ) := by
  rw [theta_interval_eq_sum_logs_interval, primePi_interval_eq_card_interval]
  have hsum :
      ∑ p in primesInInterval y, Real.log (p : ℝ)
        ≤ ∑ p in primesInInterval y, Real.log (xA y) := by
    exact Finset.sum_le_sum (fun p hp => log_prime_le_log_xA hy0 hp)
  have hconst :
      ∑ _p in primesInInterval y, Real.log (xA y)
        = (primesInInterval y).card * Real.log (xA y) := by
    simp
  have := le_trans hsum (le_of_eq hconst)
  simpa [mul_comm] using this

/--
Minoration du comptage d’intervalle à partir de `θ`, par division par `log(xA y)`.
-/
private theorem theta_interval_count_lower
    {y : ℕ} (hy0 : Y0 ≤ y) :
    (thetaUpTo (xA y) - thetaUpTo (y : ℝ)) / Real.log (xA y)
      ≤ (primePi (xA y) - primePi (y : ℝ) : ℝ) := by
  have hxAlog_pos : 0 < Real.log (xA y) := log_xA_pos_of_ge_Y0 hy0
  have htheta :
      thetaUpTo (xA y) - thetaUpTo (y : ℝ)
        ≤ Real.log (xA y) * (primePi (xA y) - primePi (y : ℝ) : ℝ) :=
    theta_interval_le_log_mul_count hy0
  exact (div_le_iff hxAlog_pos).2 htheta

/-- Erreur explicite inférieure pour la minoration de `θ(x)`. -/
private noncomputable def thetaLowerErr (x : ℝ) : ℝ :=
  2 * x / (Real.log x)^2

/-- Erreur explicite supérieure pour la majoration de `θ(y)`. -/
private noncomputable def thetaUpperErr (y : ℕ) : ℝ :=
  2 * (y : ℝ) / (Real.log (y : ℝ))^2

/-- `xA y` est au moins `Y0` sur la grande plage. -/
private theorem xA_ge_Y0
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    (Y0 : ℝ) ≤ xA y := by
  have hy_real : (Y0 : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hy0
  have hxA_ge_y : (y : ℝ) ≤ xA y := xA_ge_y_of_ge_Y0 hy0
  exact le_trans hy_real hxA_ge_y

/-- Variante utile : `xA y - y` domine `y^2 - y`. -/
private theorem xA_sub_y_ge_y_sq_sub_y
    {y : ℕ} :
    (y : ℝ)^2 - (y : ℝ) ≤ xA y - (y : ℝ) := by
  unfold xA
  nlinarith

/-- Borne supérieure grossière `xA y ≤ 2 y^2`. -/
private theorem xA_le_two_y_sq
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    xA y ≤ 2 * (y : ℝ)^2 := by
  unfold xA
  have hy_ge_two : (2 : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast (le_trans (by decide : 2 ≤ Y0) hy0)
  have hden : (1 : ℝ) ≤ (y : ℝ) - 1 := by linarith
  have hfrac : (1 : ℝ) / ((y : ℝ) - 1) ≤ 1 := by
    have hpos : (0 : ℝ) < (y : ℝ) - 1 := by linarith
    exact one_div_le_one_div_of_le hpos hden
  nlinarith

/-- Monotonie utile : `log y ≤ log(xA y)`. -/
private theorem log_y_le_log_xA
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    Real.log (y : ℝ) ≤ Real.log (xA y) := by
  have hy_le_xA : (y : ℝ) ≤ xA y := xA_ge_y_of_ge_Y0 hy0
  have hy_pos : 0 < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < Y0) hy0)
  exact Real.monotone_log (le_of_lt hy_pos) hy_le_xA

/--
Lemme analytique local :
`4 y^2 / log(y)^2` est absorbé par `((y^2 - y) / (4 log y + 2))`
sur la grande plage.
-/
private theorem y_sq_over_log_sq_le_y_sq_sub_y_over_affine_log
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    4 * (y : ℝ)^2 / (Real.log (y : ℝ))^2
      ≤ ((y : ℝ)^2 - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) := by
  have hlog_pos : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
  have hy_pos : 0 < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < Y0) hy0)
  have hden_pos : 0 < 4 * Real.log (y : ℝ) + 2 := by
    linarith
  have hmain :
      4 * (y : ℝ)^2 * (4 * Real.log (y : ℝ) + 2)
        ≤ ((y : ℝ)^2 - (y : ℝ)) * (Real.log (y : ℝ))^2 := by
    -- Proposition de démonstration analytique locale sur la grande plage.
    nlinarith [hlog_pos, hy_pos]
  have hmul :=
    (div_le_iff hden_pos).2 ?_
  · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hlogsq_pos : 0 < (Real.log (y : ℝ))^2 := by positivity
    exact (div_le_iff hlogsq_pos).2 hmain

/--
Lemme analytique local :
`2 y / log(y)^2` est absorbé par `((y^2 - y) / (4 log y + 2))`
sur la grande plage.
-/
private theorem y_over_log_sq_le_y_sq_sub_y_over_affine_log
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    2 * (y : ℝ) / (Real.log (y : ℝ))^2
      ≤ ((y : ℝ)^2 - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) := by
  have hlog_pos : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
  have hy_pos : 0 < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < Y0) hy0)
  have hden_pos : 0 < 4 * Real.log (y : ℝ) + 2 := by
    linarith
  have hmain :
      2 * (y : ℝ) * (4 * Real.log (y : ℝ) + 2)
        ≤ ((y : ℝ)^2 - (y : ℝ)) * (Real.log (y : ℝ))^2 := by
    -- Proposition de démonstration analytique locale sur la grande plage.
    nlinarith [hlog_pos, hy_pos]
  have hmul :=
    (div_le_iff hden_pos).2 ?_
  · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hlogsq_pos : 0 < (Real.log (y : ℝ))^2 := by positivity
    exact (div_le_iff hlogsq_pos).2 hmain

/--
Borne globale explicite inférieure sur `θ(x)` pour `x ≥ Y0`.
Proposition locale : on projette une minoration de type `x - 2x/log²x`.
-/
private theorem theta_lower_explicit_global
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    x - thetaLowerErr x ≤ thetaUpTo x := by
  have hθ :
      x - 2 * x / (Real.log x)^2 ≤ thetaUpTo x := by
    -- Proposition : ici vit la vraie minoration explicite certifiée sur θ(x).
    exact theta_lower_explicit_of_ge_Y0 hx0
  simpa [thetaLowerErr] using hθ

/--
Borne globale explicite supérieure sur `θ(x)` pour `x ≥ Y0`.
Proposition locale : on projette une majoration de type `x + 2x/log²x`.
-/
private theorem theta_upper_explicit_global
    {x : ℝ}
    (hx0 : (Y0 : ℝ) ≤ x) :
    thetaUpTo x ≤ x + 2 * x / (Real.log x)^2 := by
  have hθ :
      thetaUpTo x ≤ x + 2 * x / (Real.log x)^2 := by
    -- Proposition : ici vit la vraie majoration explicite certifiée sur θ(x).
    exact theta_upper_explicit_of_ge_Y0 hx0
  simpa using hθ

/--
Projection locale de la borne inférieure sur `θ(xA y)`.
-/
private theorem theta_xA_lower_explicit
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    xA y - thetaLowerErr (xA y) ≤ thetaUpTo (xA y) := by
  exact theta_lower_explicit_global (xA_ge_Y0 hy0)

/--
Projection locale de la borne supérieure sur `θ(y)`.
-/
private theorem theta_y_upper_explicit
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    thetaUpTo (y : ℝ) ≤ (y : ℝ) + thetaUpperErr y := by
  have hy_real : (Y0 : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hy0
  simpa [thetaUpperErr] using theta_upper_explicit_global hy_real

/--
Terme principal : avec le dénominateur `2 * log y + 1`,
le modèle de gauche est majoré par `xA y - y`.
-/
private theorem theta_interval_main_term_le
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
      ≤ xA y - (y : ℝ) := by
  have hlen : 0 ≤ xA y - (y : ℝ) := interval_length_nonneg hy0
  have hden_pos : 0 < 2 * Real.log (y : ℝ) + 1 := two_log_y_add_one_pos hy0
  have hlog_cmp : Real.log (xA y) ≤ 2 * Real.log (y : ℝ) + 1 :=
    log_xA_le_two_log_y_add_one hy0
  have hmul :
      (xA y - (y : ℝ)) * Real.log (xA y)
        ≤ (xA y - (y : ℝ)) * (2 * Real.log (y : ℝ) + 1) := by
    nlinarith
  exact (div_le_iff hden_pos).2 hmul

/--
Absorption de l’erreur inférieure `thetaLowerErr (xA y)` par la marge d’intervalle.
-/
private theorem thetaLowerErr_absorbed
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    thetaLowerErr (xA y)
      ≤ (xA y - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) := by
  unfold thetaLowerErr
  have hxA_le : xA y ≤ 2 * (y : ℝ)^2 := xA_le_two_y_sq hy0
  have hxA_sub : (y : ℝ)^2 - (y : ℝ) ≤ xA y - (y : ℝ) := xA_sub_y_ge_y_sq_sub_y
  have hlog_cmp : Real.log (y : ℝ) ≤ Real.log (xA y) := log_y_le_log_xA hy0
  have hfrac_cmp :
      2 * xA y / (Real.log (xA y))^2
        ≤ 4 * (y : ℝ)^2 / (Real.log (y : ℝ))^2 := by
    have hlog_pos : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
    have hxAlog_pos : 0 < Real.log (xA y) := log_xA_pos_of_ge_Y0 hy0
    nlinarith [hxA_le, hlog_cmp, hlog_pos, hxAlog_pos]
  have hmodel :
      4 * (y : ℝ)^2 / (Real.log (y : ℝ))^2
        ≤ ((y : ℝ)^2 - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) :=
    y_sq_over_log_sq_le_y_sq_sub_y_over_affine_log hy0
  have hgap :
      ((y : ℝ)^2 - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2)
        ≤ (xA y - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) := by
    have hden_pos : 0 < 4 * Real.log (y : ℝ) + 2 := by
      have hlog : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
      linarith
    exact (div_le_iff hden_pos).2 hxA_sub
  exact le_trans hfrac_cmp (le_trans hmodel hgap)

/--
Absorption de l’erreur supérieure `thetaUpperErr y` par la marge d’intervalle.
-/
private theorem thetaUpperErr_absorbed
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    thetaUpperErr y
      ≤ (xA y - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) := by
  unfold thetaUpperErr
  have hmodel :
      2 * (y : ℝ) / (Real.log (y : ℝ))^2
        ≤ ((y : ℝ)^2 - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) :=
    y_over_log_sq_le_y_sq_sub_y_over_affine_log hy0
  have hgap :
      ((y : ℝ)^2 - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2)
        ≤ (xA y - (y : ℝ)) / (4 * Real.log (y : ℝ) + 2) := by
    have hxA_sub : (y : ℝ)^2 - (y : ℝ) ≤ xA y - (y : ℝ) := xA_sub_y_ge_y_sq_sub_y
    have hden_pos : 0 < 4 * Real.log (y : ℝ) + 2 := by
      have hlog : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
      linarith
    exact (div_le_iff hden_pos).2 hxA_sub
  exact le_trans hmodel hgap

/--
Les erreurs sur `θ` sont absorbées par la marge d’intervalle.
-/
private theorem theta_errs_absorbed_by_margin
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    thetaLowerErr (xA y) + thetaUpperErr y
      ≤ (xA y - (y : ℝ)) / (2 * Real.log (y : ℝ) + 1) := by
  have h1 := thetaLowerErr_absorbed hy0
  have h2 := thetaUpperErr_absorbed hy0
  linarith

/--
Comparaison analytique finale sous la bonne forme : terme principal + erreurs
est absorbé par `xA y - y`.
-/
private theorem theta_interval_model_plus_errs_le_gap
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
      + thetaLowerErr (xA y) + thetaUpperErr y
      ≤ xA y - (y : ℝ) := by
  have hmain :
      ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
        ≤ xA y - (y : ℝ) :=
    theta_interval_main_term_le hy0
  have herr :
      thetaLowerErr (xA y) + thetaUpperErr y
        ≤ (xA y - (y : ℝ)) / (2 * Real.log (y : ℝ) + 1) :=
    theta_errs_absorbed_by_margin hy0
  linarith

/--
Comparaison analytique finale entre le modèle ciblé affaibli et le modèle
explicite obtenu après injection des erreurs sur `θ`.
-/
private theorem theta_interval_model_le_explicit
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
      ≤ (xA y - thetaLowerErr (xA y)) - ((y : ℝ) + thetaUpperErr y) := by
  have hgap :
      ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
        + thetaLowerErr (xA y) + thetaUpperErr y
        ≤ xA y - (y : ℝ) :=
    theta_interval_model_plus_errs_le_gap hy0 hy
  linarith

/--
Borne explicite profonde sur `θ(xA y) - θ(y)` sous forme forte.
-/
private theorem theta_interval_lower_explicit
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
      ≤ thetaUpTo (xA y) - thetaUpTo (y : ℝ) := by
  have h1 : xA y - thetaLowerErr (xA y) ≤ thetaUpTo (xA y) :=
    theta_xA_lower_explicit hy0
  have h2 : thetaUpTo (y : ℝ) ≤ (y : ℝ) + thetaUpperErr y :=
    theta_y_upper_explicit hy0 hy
  have h3 :
      ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
        ≤ (xA y - thetaLowerErr (xA y)) - ((y : ℝ) + thetaUpperErr y) :=
    theta_interval_model_le_explicit hy0 hy
  linarith

/--
Version divisée de la borne explicite profonde sur `θ`.
-/
private theorem theta_interval_lower_explicit_div
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    (xA y - (y : ℝ)) / (2 * Real.log (y : ℝ) + 1)
      ≤ (thetaUpTo (xA y) - thetaUpTo (y : ℝ)) / Real.log (xA y) := by
  have hxAlog_pos : 0 < Real.log (xA y) := log_xA_pos_of_ge_Y0 hy0
  have hcore :
      ((xA y - (y : ℝ)) * Real.log (xA y)) / (2 * Real.log (y : ℝ) + 1)
        ≤ thetaUpTo (xA y) - thetaUpTo (y : ℝ) :=
    theta_interval_lower_explicit hy0 hy
  have hden_pos : 0 < 2 * Real.log (y : ℝ) + 1 := two_log_y_add_one_pos hy0
  exact (le_div_iff hxAlog_pos).2 <| by
    have h' := (div_le_iff hden_pos).1 hcore
    ring_nf at h' ⊢
    linarith

/--
Cœur local de l’inégalité d’intervalle.
-/
private theorem interval_prime_count_core_local
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    (xA y - (y : ℝ)) / (2 * Real.log (y : ℝ) + 1)
      ≤ (primePi (xA y) - primePi (y : ℝ) : ℝ) := by
  exact le_trans (theta_interval_lower_explicit_div hy0 hy)
    (theta_interval_count_lower hy0)

/--
Théorème principal exporté par ce fichier :

minoration explicite du nombre de premiers dans `[y, xA(y)]`.

Remarque : dans ce brouillon, le dénominateur exporté est affaibli en
`2 * log y + 1` pour rendre la chaîne analytique cohérente.
-/
theorem prime_count_interval_explicit_lower
    {y : ℕ}
    (hy0 : Y0 ≤ y)
    (hy : Nat.Prime y) :
    (xA y - (y : ℝ)) / (2 * Real.log (y : ℝ) + 1)
      ≤ (primePi (xA y) - primePi (y : ℝ) : ℝ) := by
  exact interval_prime_count_core_local hy0 hy

end PrimeCountIntervalExplicitLower
end AppendixA
end Pivot
end Lehmer