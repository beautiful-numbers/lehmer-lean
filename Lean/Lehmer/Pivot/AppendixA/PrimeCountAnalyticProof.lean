-- FILE: Lean/Lehmer/Pivot/AppendixA/PrimeCountAnalyticProof.lean
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
namespace PrimeCountAnalyticProof

open scoped Real

/-!
# Preuves analytiques locales pour le gap de comptage des nombres premiers

Ce fichier contient les lemmes locaux fermés utilisés autour du point
`Y0 = 30000` et les réductions algébriques élémentaires sur la grande plage.

Les résultats qui nécessitent une minoration analytique profonde du nombre
de premiers dans `[y, xA(y)]` ont été retirés de ce fichier, afin que le fichier
reste entièrement fermé.
-/

/-- Gap entre le terme de comptage des nombres premiers et la barrière analytique. -/
private def primeCountGap (y : ℕ) : ℝ :=
  (primePi (xA y) - primePi y + 1 : ℝ) - barrier (y : ℝ)

@[simp] private theorem primeCountGap_def (y : ℕ) :
    primeCountGap y = (primePi (xA y) - primePi y + 1 : ℝ) - barrier (y : ℝ) := rfl


/-! ### 1. Lemmes locaux pour l’endpoint (`Y0 = 30000`) -/

/-- Ensemble fini explicite des nombres premiers jusqu’à `n`. -/
private def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/--
Réduction locale de `primePi` à un comptage fini des nombres premiers jusqu’à `⌊x⌋`.
-/
private theorem primePi_eq_card_primesUpTo_floor (x : ℝ) :
    primePi x = (primesUpTo (Int.toNat ⌊x⌋)).card := by
  unfold primePi primesUpTo
  simp

/-- Évaluation algébrique locale de `xA Y0`. -/
private theorem xA_Y0_eval :
    xA Y0 = (((1 : ℝ) + 1 / 29999) * (30000 : ℝ)^2) := by
  unfold xA Y0
  ring

/-- Borne inférieure locale sur `xA Y0`. -/
private theorem xA_Y0_lower_bound :
    (1657432 : ℝ) ≤ xA Y0 := by
  rw [xA_Y0_eval]
  norm_num

/-- Projection locale de la borne inférieure certifiée sur `log 30000`. -/
private theorem log_30000_lower :
    (10.3089 : ℝ) < Real.log (30000 : ℝ) := by
  simpa using log_30000_interval_lower

/-- Projection locale de la borne supérieure certifiée sur `log 30000`. -/
private theorem log_30000_upper :
    Real.log (30000 : ℝ) < (10.3090 : ℝ) := by
  have h :
      (10.3089 : ℝ) < Real.log (30000 : ℝ) ∧
      Real.log (30000 : ℝ) < (10.3090 : ℝ) := by
    simpa using log_30000_interval
  exact h.2

/-- Minoration locale de `π(1657432)`. -/
private theorem primePi_1657432_lower :
    117301 ≤ primePi (1657432 : ℝ) := by
  rw [primePi_eq_card_primesUpTo_floor]
  native_decide

/-- Minoration locale de `π(xA Y0)` par monotonie. -/
private theorem primePi_xA_Y0_lower_bound :
    117301 ≤ primePi (xA Y0) := by
  have h165 : 117301 ≤ primePi (1657432 : ℝ) := primePi_1657432_lower
  have hxA : (1657432 : ℝ) ≤ xA Y0 := xA_Y0_lower_bound
  exact le_trans h165 (primePi_mono hxA)

/-- Valeur locale exacte de `π(30000)`. -/
private theorem primePi_Y0_eq :
    primePi Y0 = 3245 := by
  rw [primePi_eq_card_primesUpTo_floor]
  unfold Y0
  native_decide

/-- Majoration locale de la barrière à `Y0`. -/
private theorem barrier_Y0_bound :
    barrier (Y0 : ℝ) < 87303 := by
  unfold barrier C1 Y0
  have hlog : (10.3089 : ℝ) < Real.log (30000 : ℝ) := log_30000_lower
  have h10308_pos : (0 : ℝ) < 10.3089 := by
    norm_num
  have hrecip :
      (Real.log (30000 : ℝ))⁻¹ < (10.3089 : ℝ)⁻¹ := by
    exact one_div_lt_one_div_of_lt h10308_pos hlog
  have hdiv :
      (0.001 : ℝ) * (30000 : ℝ)^2 / Real.log (30000 : ℝ)
        < (0.001 : ℝ) * (30000 : ℝ)^2 / 10.3089 := by
    nlinarith
  have hnum :
      (0.001 : ℝ) * (30000 : ℝ)^2 / 10.3089 < 87303 := by
    norm_num
  linarith

/--
Inégalité endpoint au point `Y0`.
Preuve d’assemblage entièrement fermée par `linarith`.
-/
private theorem barrier_lt_primeCount_at_Y0 :
    barrier (Y0 : ℝ) < (primePi (xA Y0) - primePi Y0 + 1 : ℝ) := by
  have h_pi_xA : 117301 ≤ primePi (xA Y0) := primePi_xA_Y0_lower_bound
  have h_pi_Y0 : primePi Y0 = 3245 := primePi_Y0_eq
  have h_bar   : barrier (Y0 : ℝ) < 87303 := barrier_Y0_bound
  linarith


/-! ### 2. Lemmes analytiques locaux pour la plage infinie (`y ≥ Y0`) -/

/-- Positivité du logarithme sur la grande plage. -/
private theorem log_pos_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 < Real.log (y : ℝ) := by
  have hy1_nat : 1 < y := lt_of_lt_of_le (by decide : 1 < Y0) hy0
  have hy1 : (1 : ℝ) < (y : ℝ) := by
    exact_mod_cast hy1_nat
  exact Real.log_pos hy1

/-- Borne standard `log y < y` sur la grande plage. -/
private theorem log_lt_y_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    Real.log (y : ℝ) < (y : ℝ) := by
  have hy1_nat : 1 < y := lt_of_lt_of_le (by decide : 1 < Y0) hy0
  have hy1 : (1 : ℝ) < (y : ℝ) := by
    exact_mod_cast hy1_nat
  have hypos : (0 : ℝ) < (y : ℝ) := by
    linarith
  exact Real.log_lt_self hypos

/--
Petit lemme analytique local :
`log y < 0.499 * y` pour tout `y ≥ Y0`.
-/
private theorem log_lt_point499_mul_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    Real.log (y : ℝ) < (0.499 : ℝ) * (y : ℝ) := by
  have hy_real : (30000 : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hy0
  have hy_pos : (0 : ℝ) < (y : ℝ) := by
    have : (1 : ℝ) < (y : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < Y0) hy0)
    linarith
  have h30000_pos : (0 : ℝ) < (30000 : ℝ) := by norm_num
  have hratio_pos : (0 : ℝ) < (y : ℝ) / 30000 := by
    positivity
  have hlog_ratio :
      Real.log ((y : ℝ) / 30000) ≤ (y : ℝ) / 30000 - 1 := by
    exact Real.log_le_sub_one_of_pos hratio_pos
  have hdecomp :
      Real.log (y : ℝ) = Real.log (30000 : ℝ) + Real.log ((y : ℝ) / 30000) := by
    have hmul : (30000 : ℝ) * ((y : ℝ) / 30000) = (y : ℝ) := by
      field_simp
    calc
      Real.log (y : ℝ)
          = Real.log ((30000 : ℝ) * ((y : ℝ) / 30000)) := by rw [hmul]
      _ = Real.log (30000 : ℝ) + Real.log ((y : ℝ) / 30000) := by
            rw [Real.log_mul h30000_pos.ne' hratio_pos.ne']
  have hmain :
      Real.log (y : ℝ) < (10.3090 : ℝ) + ((y : ℝ) / 30000 - 1) := by
    have hup : Real.log (30000 : ℝ) < (10.3090 : ℝ) := log_30000_upper
    linarith
  have hnum :
      (10.3090 : ℝ) + ((y : ℝ) / 30000 - 1) ≤ (0.499 : ℝ) * (y : ℝ) := by
    nlinarith
  exact lt_of_lt_of_le hmain hnum

/--
Lemme auxiliaire de domination :
`y - 1 < 0.499 * y^2 / log y`.
-/
private theorem y_sub_one_lt_halfmain
    {y : ℕ} (hy0 : Y0 ≤ y) :
    (y : ℝ) - 1 < (0.499 : ℝ) * (y : ℝ)^2 / Real.log (y : ℝ) := by
  have hlog_pos : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
  have hy_pos : (0 : ℝ) < (y : ℝ) := by
    have : (1 : ℝ) < (y : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < Y0) hy0)
    linarith
  have h1 : (y : ℝ) * Real.log (y : ℝ) < (0.499 : ℝ) * (y : ℝ)^2 := by
    nlinarith [log_lt_point499_mul_of_ge_Y0 hy0, hy_pos]
  have h2 : ((y : ℝ) - 1) * Real.log (y : ℝ) < (y : ℝ) * Real.log (y : ℝ) := by
    nlinarith [hlog_pos]
  have h3 : ((y : ℝ) - 1) * Real.log (y : ℝ) < (0.499 : ℝ) * (y : ℝ)^2 := by
    exact lt_trans h2 h1
  exact (div_lt_iff hlog_pos).2 h3

/-- Domination algébrique locale de la barrière. -/
private theorem barrier_lt_analytic_bound
    {y : ℕ} (hy0 : Y0 ≤ y) :
    barrier (y : ℝ) <
      (y^2 : ℝ) / (2 * Real.log (y : ℝ)) - y + 1 := by
  unfold barrier C1
  have hlog_pos : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
  have hy_dom :
      (y : ℝ) - 1 < (0.499 : ℝ) * (y : ℝ)^2 / Real.log (y : ℝ) :=
    y_sub_one_lt_halfmain hy0
  have hsplit :
      (0.001 : ℝ) * (y : ℝ)^2 / Real.log (y : ℝ)
        < (0.5 : ℝ) * (y : ℝ)^2 / Real.log (y : ℝ) - ((y : ℝ) - 1) := by
    linarith
  have hhalf :
      (0.5 : ℝ) * (y : ℝ)^2 / Real.log (y : ℝ)
        = (y : ℝ)^2 / (2 * Real.log (y : ℝ)) := by
    field_simp [hlog_pos.ne']
    ring
  have hrew :
      (0.5 : ℝ) * (y : ℝ)^2 / Real.log (y : ℝ) - ((y : ℝ) - 1)
        = (y : ℝ)^2 / (2 * Real.log (y : ℝ)) - (y : ℝ) + 1 := by
    rw [hhalf]
    ring
  simpa [hrew] using hsplit

/-- L’intervalle `[y, xA(y)]` est non trivial sur la grande plage. -/
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

/-- Positivité de `log (xA y)` sur la grande plage. -/
private theorem log_xA_pos_of_ge_Y0
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 < Real.log (xA y) := by
  have hy1 : (1 : ℝ) < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < Y0) hy0)
  have hxA : (y : ℝ) ≤ xA y := xA_ge_y_of_ge_Y0 hy0
  have h1 : (1 : ℝ) < xA y := lt_of_lt_of_le hy1 hxA
  exact Real.log_pos h1

/-- Positivité du dénominateur `2 * log y - 1` sur la grande plage. -/
private theorem two_log_y_sub_one_pos
    {y : ℕ} (hy0 : Y0 ≤ y) :
    0 < 2 * Real.log (y : ℝ) - 1 := by
  have hlog : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
  linarith

/--
Comparaison entre le modèle d’intervalle brut et un auxiliaire explicite
au dénominateur `2 * log y - 1`.
-/
private theorem interval_model_le_explicit_aux
    {y : ℕ}
    (hy0 : Y0 ≤ y) :
    (xA y - (y : ℝ)) / (2 * Real.log (y : ℝ))
      ≤ (xA y - (y : ℝ)) / (2 * Real.log (y : ℝ) - 1) := by
  have hlen : 0 ≤ xA y - (y : ℝ) := interval_length_nonneg hy0
  have hden1 : 0 < 2 * Real.log (y : ℝ) - 1 := two_log_y_sub_one_pos hy0
  have hden2 : 0 < 2 * Real.log (y : ℝ) := by
    have hlog : 0 < Real.log (y : ℝ) := log_pos_of_ge_Y0 hy0
    linarith
  have hcmp : 2 * Real.log (y : ℝ) - 1 ≤ 2 * Real.log (y : ℝ) := by
    linarith
  exact div_le_div_of_nonneg_left hlen hden1 hcmp

end PrimeCountAnalyticProof
end AppendixA
end Pivot
end Lehmer