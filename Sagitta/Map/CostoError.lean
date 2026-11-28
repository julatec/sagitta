import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# El costo de equivocarse al elegir

Hasta aquí el «`1 + ε` por elección» suponía que la elección siempre acierta: es el no determinismo de NP, que se
queda con el único mundo, de los `2^c` posibles, donde todas salen bien. Aquí se le pone precio a equivocarse.

## El modelo

* Cada elección se equivoca con probabilidad **`ρ`** («riesgo»; no es el `δ` de los límites ni el `ε` del costo de
  elegir), independiente de las demás.
* Un error se detecta **`d`** elecciones después (la **demora**).
* Al detectarlo se rehace el tramo de `d` elecciones, eligiendo de nuevo sin memoria.

Un tramo sale bien con probabilidad `p = (1 − ρ)^d`. Los fracasos antes del primer éxito siguen la geométrica de
Mathlib (`geometricMeasure p`); los intentos son fracasos más uno. Con `m` tramos independientes (la medida producto) y
`c = m·d` elecciones, el costo total es `T = d · ∑ᵢ (Gᵢ + 1)`, una binomial negativa escalada.

## Lo que se prueba

* **La media de la geométrica** (`media_fracasos`): `(1 − p)/p`; los intentos, `1/p` (`media_intentos`). Mathlib trae
  la medida y su integral, no la media.
* **El costo esperado** (`costo_esperado`, `costo_esperado_rho`): `E[T] = c · (1 − ρ)^(−d)`. Lo que suma el error es
  `c · ((1 − ρ)^(−d) − 1)` (`error_esperado_rho`).
* **La frontera** (`frontera`): con `ρ ≤ 1/2`, el factor `(1 − ρ)^(−d)` es polinomial en `n` **si y solo si**
  `ρ · d = O(log n)`. Equivocarse poco o enterarse pronto: lo que cuenta es el producto.
* **A ciegas** (`a_ciegas`): con `ρ = 1/2`, el factor es `2^d`, las ramas del árbol.

## Lo que el modelo no dice

Los supuestos son fuertes: los errores reales no son independientes, y una vuelta atrás sistemática (que no repite lo
ya probado) corta los intentos en `2^d`. Que ninguna heurística polinomial logre `ρ · d = O(log n)` en todas las
instancias sería una forma de P ≠ NP; aquí no se prueba nada de eso.
-/

open MeasureTheory ProbabilityTheory Real

namespace Sagitta.Map
namespace Tiempo

/-! ## Un tramo: la geométrica -/

theorem integrable_fracasos {p : unitInterval} (hp : p ≠ 0) :
    Integrable (fun n : ℕ => (n : ℝ)) (geometricMeasure p) := by
  have hp0 : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  have hr : ‖(1 - p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith [p.2.2]
  rw [integrable_geometricMeasure_iff hp]
  refine ((hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.mul_left (p : ℝ)).congr fun n => ?_
  rw [Real.norm_natCast]; ring

/-- **La media de los fracasos** antes del primer éxito: `(1 − p)/p`. -/
theorem media_fracasos {p : unitInterval} (hp : p ≠ 0) :
    ∫ n, (n : ℝ) ∂geometricMeasure p = (1 - p) / p := by
  have hp0 : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  have hr : ‖(1 - p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith [p.2.2]
  rw [integral_geometricMeasure hp]
  simp only [smul_eq_mul]
  calc ∑' n : ℕ, (1 - p : ℝ) ^ n * p * n = ∑' n : ℕ, (p : ℝ) * (n * (1 - p) ^ n) := by
        congr 1; funext n; ring
    _ = p * ∑' n : ℕ, (n : ℝ) * (1 - p) ^ n := tsum_mul_left
    _ = p * ((1 - p) / (1 - (1 - p)) ^ 2) := by rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
    _ = (1 - p) / p := by rw [sub_sub_cancel]; field_simp

/-- **La media de los intentos**: `1/p`. -/
theorem media_intentos {p : unitInterval} (hp : p ≠ 0) :
    ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 1 / p := by
  have hp0 : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  rw [integral_add (integrable_fracasos hp) (integrable_const _), media_fracasos hp]
  simp only [integral_const, probReal_univ, one_smul]
  field_simp; ring

/-! ## `m` tramos independientes -/

/-- Los fracasos de `m` tramos independientes. -/
noncomputable def tramos (m : ℕ) (p : unitInterval) : Measure (Fin m → ℕ) :=
  Measure.pi fun _ => geometricMeasure p

/-- **El costo total**: cada intento de cada tramo cuesta sus `d` elecciones. -/
noncomputable def costo (d : ℕ) {m : ℕ} (x : Fin m → ℕ) : ℝ := d * ∑ i, ((x i : ℝ) + 1)

/-- **Lo que suma el error**: el trabajo tirado, `d` elecciones por cada intento fallido. -/
noncomputable def error (d : ℕ) {m : ℕ} (x : Fin m → ℕ) : ℝ := d * ∑ i, (x i : ℝ)

theorem integrable_intento {m : ℕ} {p : unitInterval} (hp : p ≠ 0) (i : Fin m) :
    Integrable (fun x : Fin m → ℕ => (x i : ℝ) + 1) (tramos m p) :=
  integrable_comp_eval (μ := fun _ => geometricMeasure p) (f := fun n : ℕ => (n : ℝ) + 1)
    ((integrable_fracasos hp).add (integrable_const 1))

theorem integrable_fracaso {m : ℕ} {p : unitInterval} (hp : p ≠ 0) (i : Fin m) :
    Integrable (fun x : Fin m → ℕ => (x i : ℝ)) (tramos m p) :=
  integrable_comp_eval (μ := fun _ => geometricMeasure p) (f := fun n : ℕ => (n : ℝ)) (integrable_fracasos hp)

/-- **El costo esperado de `m` tramos**: `d · m / p`. -/
theorem costo_esperado (d m : ℕ) {p : unitInterval} (hp : p ≠ 0) :
    ∫ x, costo d x ∂tramos m p = d * m / p := by
  unfold costo
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_intento hp i]
  have h : ∀ i : Fin m, ∫ x, ((x i : ℝ) + 1) ∂tramos m p = 1 / p := fun i => by
    rw [tramos, integral_comp_eval (μ := fun _ => geometricMeasure p) (f := fun n : ℕ => (n : ℝ) + 1)
      (measurable_from_nat.aestronglyMeasurable), media_intentos hp]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **El error esperado de `m` tramos**: `d · m · (1 − p)/p`. -/
theorem error_esperado (d m : ℕ) {p : unitInterval} (hp : p ≠ 0) :
    ∫ x, error d x ∂tramos m p = d * m * ((1 - p) / p) := by
  unfold error
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_fracaso hp i]
  have h : ∀ i : Fin m, ∫ x, (x i : ℝ) ∂tramos m p = (1 - p) / p := fun i => by
    rw [tramos, integral_comp_eval (μ := fun _ => geometricMeasure p) (f := fun n : ℕ => (n : ℝ))
      (measurable_from_nat.aestronglyMeasurable), media_fracasos hp]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## Con el riesgo `ρ` y la demora `d` -/

/-- La probabilidad de que un tramo de `d` elecciones salga bien: `(1 − ρ)^d`. -/
noncomputable def exito (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (d : ℕ) : unitInterval :=
  ⟨(1 - ρ) ^ d, pow_nonneg (by linarith) d, pow_le_one₀ (by linarith) (by linarith)⟩

theorem exito_ne_cero (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (d : ℕ) : exito ρ h0 h1 d ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp only [exito, Set.Icc.coe_zero] at this
  exact (pow_pos (by linarith : (0 : ℝ) < 1 - ρ) d).ne' this

/-- **El costo esperado**: con `c = m · d` elecciones, `E[T] = c · (1 − ρ)^(−d)`. -/
theorem costo_esperado_rho (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (d m : ℕ) :
    ∫ x, costo d x ∂tramos m (exito ρ h0 h1 d) = (m * d : ℕ) * (1 - ρ)⁻¹ ^ d := by
  rw [costo_esperado d m (exito_ne_cero ρ h0 h1 d)]
  simp only [exito, Nat.cast_mul, inv_pow]
  ring

/-- **Lo que suma el error**: `c · ((1 − ρ)^(−d) − 1)`. -/
theorem error_esperado_rho (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (d m : ℕ) :
    ∫ x, error d x ∂tramos m (exito ρ h0 h1 d) = (m * d : ℕ) * ((1 - ρ)⁻¹ ^ d - 1) := by
  rw [error_esperado d m (exito_ne_cero ρ h0 h1 d)]
  have hq : (0 : ℝ) < (1 - ρ) ^ d := pow_pos (by linarith) d
  simp only [exito, Nat.cast_mul, inv_pow]
  field_simp

/-- **A ciegas** (`ρ = 1/2`), el factor es `2^d`: las ramas del árbol. -/
theorem a_ciegas (d : ℕ) : (1 - (1 / 2 : ℝ))⁻¹ ^ d = 2 ^ d := by norm_num

/-! ## La frontera: `ρ · d = O(log n)` -/

/-- `ρ ≤ log (1/(1 − ρ))`. -/
theorem rho_le_log {ρ : ℝ} (h1 : ρ < 1) : ρ ≤ Real.log (1 - ρ)⁻¹ := by
  rw [Real.log_inv]
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - ρ)
  linarith

/-- `log (1/(1 − ρ)) ≤ 2ρ` si `ρ ≤ 1/2`. -/
theorem log_le_dos_rho {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) : Real.log (1 - ρ)⁻¹ ≤ 2 * ρ := by
  have hpos : (0 : ℝ) < (1 - ρ)⁻¹ := inv_pos.mpr (by linarith)
  have := Real.log_le_sub_one_of_pos hpos
  have h2 : (1 - ρ)⁻¹ - 1 ≤ 2 * ρ := by
    rw [inv_eq_one_div, div_sub_one (by linarith : (1 : ℝ) - ρ ≠ 0), div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- El factor, escrito como exponencial. -/
theorem factor_eq_exp (ρ : ℝ) (h1 : ρ < 1) (d : ℕ) : (1 - ρ)⁻¹ ^ d = Real.exp (d * Real.log (1 - ρ)⁻¹) := by
  rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr (by linarith))]

/-- **La frontera.** Con riesgo `ρ n ≤ 1/2` y demora `d n`, el factor `(1 − ρ)^(−d)` del costo esperado está acotado
por un polinomio en `n` **si y solo si** `ρ · d = O(log n)`. -/
theorem frontera (ρ : ℕ → ℝ) (h0 : ∀ n, 0 ≤ ρ n) (h1 : ∀ n, ρ n ≤ 1 / 2) (d : ℕ → ℕ) :
    (∃ C : ℝ, ∃ k : ℕ, ∀ n, (1 - ρ n)⁻¹ ^ d n ≤ C * ((n : ℝ) + 1) ^ k) ↔
      ∃ a b : ℝ, ∀ n, ρ n * d n ≤ a * Real.log ((n : ℝ) + 1) + b := by
  have hlt : ∀ n, ρ n < 1 := fun n => by linarith [h1 n]
  constructor
  · rintro ⟨C, k, h⟩
    have hC : 0 < C := by
      have := h 0
      have hpos : (0 : ℝ) < (1 - ρ 0)⁻¹ ^ d 0 := pow_pos (inv_pos.mpr (by linarith [hlt 0])) _
      simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at this
      linarith
    refine ⟨k, Real.log C, fun n => ?_⟩
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle := h n
    rw [factor_eq_exp (ρ n) (hlt n)] at hle
    have hlog := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp, Real.log_mul hC.ne' (pow_pos hn k).ne', Real.log_pow] at hlog
    have := mul_le_mul_of_nonneg_left (rho_le_log (hlt n)) (Nat.cast_nonneg (d n) : (0 : ℝ) ≤ d n)
    nlinarith
  · rintro ⟨a, b, h⟩
    set k : ℕ := ⌈max (2 * a) 0⌉₊
    refine ⟨Real.exp (2 * b), k, fun n => ?_⟩
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hlogn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hn1
    have hk : 2 * a ≤ k := (le_max_left _ _).trans (Nat.le_ceil _)
    rw [factor_eq_exp (ρ n) (hlt n)]
    have hd : (d n : ℝ) * Real.log (1 - ρ n)⁻¹ ≤ 2 * b + k * Real.log ((n : ℝ) + 1) := by
      have e1 := mul_le_mul_of_nonneg_left (log_le_dos_rho (h0 n) (h1 n)) (Nat.cast_nonneg (d n) : (0 : ℝ) ≤ d n)
      have e2 := mul_le_mul_of_nonneg_right hk hlogn
      nlinarith [h n]
    calc Real.exp (d n * Real.log (1 - ρ n)⁻¹) ≤ Real.exp (2 * b + k * Real.log ((n : ℝ) + 1)) :=
          Real.exp_le_exp.mpr hd
      _ = Real.exp (2 * b) * ((n : ℝ) + 1) ^ k := by
          rw [Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]

/-- **Control de la frontera**: a ciegas (`ρ = 1/2`) y enterándose al final (`d = n`), el factor no es polinomial. La
frontera deja algo afuera. -/
theorem a_ciegas_al_final_no_polinomial :
    ¬ ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, (1 - (1 / 2 : ℝ))⁻¹ ^ n ≤ C * ((n : ℝ) + 1) ^ k := by
  intro hpol
  obtain ⟨a, b, h⟩ := (frontera (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => le_rfl) id).mp hpol
  set t : ℕ := ⌈4 * |a| + |b| + 3⌉₊ with ht
  have ht' : 4 * |a| + |b| + 3 ≤ (t : ℝ) := Nat.le_ceil _
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ t := by linarith [abs_nonneg a, abs_nonneg b]
    exact_mod_cast this
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hcast : ((t * t - 1 : ℕ) : ℝ) = (t : ℝ) * t - 1 := by
    rw [Nat.cast_sub (by nlinarith), Nat.cast_mul, Nat.cast_one]
  have h' := h (t * t - 1)
  simp only [id] at h'
  rw [hcast, show (t : ℝ) * t - 1 + 1 = t * t by ring,
    Real.log_mul (by positivity) (by positivity)] at h'
  have hl : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg htr
  have ha : a * (Real.log t + Real.log t) ≤ |a| * (2 * (t - 1)) := by
    calc a * (Real.log t + Real.log t) ≤ |a| * (Real.log t + Real.log t) :=
          mul_le_mul_of_nonneg_right (le_abs_self a) (by linarith)
      _ ≤ |a| * (2 * (t - 1)) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg a)
  have hb := le_abs_self b
  nlinarith [abs_nonneg a, abs_nonneg b]

end Tiempo
end Sagitta.Map
