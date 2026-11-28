import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Lo que trae la física estadística, la parte rigurosa

Las notas del proyecto sobre lo que trae la física estadística y la demo de
`ejemplos/fisica-estadistica` miran 3-SAT al azar como un sistema de espines: la energía de una asignación es el número
de cláusulas falsas, y a temperatura cero la función de partición es `S`, el número de soluciones. Este archivo prueba
las cinco piezas que esa lectura usa y que sí tienen demostración.

Todo es probabilidad finita: un espacio `Ω` con `Fintype`, pesos `w ≥ 0` que suman `1`, `E[X] = ∑ w·X` y
`P(A) = ∑_{ω ∈ A} w`. No hace falta teoría de la medida.

## 1. El primer momento (`esperanza_soluciones`)

Una cláusula es una terna de variables (de un tipo finito `V` cualquiera, con `var : V → Fin 3 → Fin n`) y tres signos;
el literal `i` es verdadero si `x (var v i) = s i`. Para una asignación fija `x` y una terna fija, de los `8` juegos de
signos exactamente uno deja la cláusula falsa (`cuenta_no_satisface`), así que la satisfacen `7` de cada `8`
(`suma_satisface`), **con o sin variables repetidas**: no hace falta que la terna sea inyectiva. Una fórmula son `m`
cláusulas, `F : Fin m → V × (Fin 3 → Bool)`, y la ley es la uniforme sobre ese producto: eso **es** la independencia de
las cláusulas, escrito como suma explícita sobre las `m` copias (no se usa el aparato de independencia de Mathlib).
Intercambiando sumas y factorizando el producto (`Fintype.prod_sum`):

  `E[S] = 2ⁿ · (7/8)^m`.

## 2. Markov y el umbral (`markov`, `prob_sat_le`, `prob_sat_le_geom`, `prob_sat_tiende_cero`)

`P(S ≥ 1) ≤ E[S]` para `S` con valores en `ℕ` (el indicador de `S ≥ 1` es `≤ S`). Con `m ≥ c·n` y
`c > ln 2 / ln (8/7)` (≈ 5,19), `q = 2·(7/8)^c < 1` (`razon_lt_uno`) y `P(sat) ≤ qⁿ`, que tiende a `0`. Para que
`S` esté definida hace falta al menos una terna (`Nonempty V`); con `V = Fin 3 ↪ Fin n` (tres variables distintas) eso
vale desde `n = 3` (`prob_sat_tiende_cero_distintas`).

## 3. Recocido contra templado (`templada_le_recocida`, `templada_eq_recocida_iff`)

Para `Z > 0`: `E[log Z] ≤ log E[Z]` (Jensen, `ConcaveOn.le_map_sum` con `strictConcaveOn_log_Ioi`), y con pesos
positivos la igualdad vale si y solo si `Z` es constante (`StrictConcaveOn.map_sum_eq_iff_of_pos`). La brecha es la de
la demo: crece con `α`.

## 4. El segundo momento (`paley_zygmund`, `prob_sat_ge`)

Para `Z ≥ 0` con `E[Z] > 0`: `P(Z > 0) ≥ E[Z]² / E[Z²]`. Cauchy–Schwarz en la forma
`(∑ rᵢ)² ≤ (∑ fᵢ)(∑ gᵢ)` si `rᵢ² ≤ fᵢ gᵢ` (`sum_sq_le_sum_mul_sum_of_sq_le_mul`), con `rᵢ = wᵢ Zᵢ`, `fᵢ = wᵢ Zᵢ²`,
`gᵢ = wᵢ·[Zᵢ > 0]`; donde `Zᵢ = 0` las dos caras son `0`. Aplicado a `S`: `P(sat) ≥ E[S]²/E[S²]`.

## 5. El truco de las réplicas, la parte rigurosa (`replicas_deriv`, `replicas`, `enteros_no_bastan`)

Para `Z > 0`, `r ↦ E[Z^r] = ∑ w · exp (r log Z)` es derivable en `0` con derivada `E[log Z]`, y por eso
`lím_{r→0, r≠0} (E[Z^r] − 1)/r = E[log Z]`. Es la identidad que usan los físicos. **Lo que no se prueba**, porque no
es cierto en general, es el paso que ellos dan: calcular `E[Z^r]` solo para `r` entero y extrapolar a `r → 0`.
`enteros_no_bastan` lo muestra: `E[Z^r] + sin(π r)` coincide con `E[Z^r]` en todo entero y su derivada en `0` es
`E[log Z] + π`. Los valores en los enteros no determinan la derivada en `0` sin una hipótesis de crecimiento (Carlson);
esa hipótesis es justo lo que el método de réplicas no verifica.

## Controles

Un mutante por teorema central, fuera del repositorio, y cómo falló cada uno:

* `esperanza_soluciones` con `(3/4)^m`: queda la meta `7^m · 4^m = 8^m · 3^m`, falsa.
* `templada_le_recocida` con la desigualdad al revés: Jensen da el otro sentido y el `simpa` no cierra.
* `razon_lt_uno` con `5 ≤ c` en vez del umbral: la prueba ya no reescribe la hipótesis; y aparte se comprobó que
  `1 < 2 · (7/8)^5`, así que con `c = 5` (bajo el umbral ≈ 5,19) la razón no es `< 1` y la cota no decrece.
* `sq_esp_le` con `P(Z > 1)` en vez de `P(Z > 0)`: el caso `Z ≤ 1` no da `Z = 0` y `linarith` falla en
  `paley_zygmund`.
* `replicas_deriv` con `E[log Z] + 1`: la suma de derivadas no calza (y caen `replicas` y `enteros_no_bastan`).
-/

namespace Sagitta.Map.FisicaEstadistica

open Finset Real Filter Topology

/-! ## 0. Probabilidad finita -/

section Pesos

variable {Ω : Type*} [Fintype Ω]

/-- Una ley de probabilidad sobre un espacio finito. -/
structure Ley (Ω : Type*) [Fintype Ω] where
  w : Ω → ℝ
  no_neg : ∀ ω, 0 ≤ w ω
  suma : ∑ ω, w ω = 1

/-- `E[X]`. -/
def Ley.esp (P : Ley Ω) (X : Ω → ℝ) : ℝ := ∑ ω, P.w ω * X ω

/-- `P(A)`. -/
def Ley.prob (P : Ley Ω) (A : Ω → Prop) [DecidablePred A] : ℝ := ∑ ω, if A ω then P.w ω else 0

/-- La ley uniforme. -/
noncomputable def uniforme (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Ley Ω where
  w _ := (Fintype.card Ω : ℝ)⁻¹
  no_neg _ := by positivity
  suma := by
    simp [Finset.sum_const, Finset.card_univ]

lemma esp_uniforme [Nonempty Ω] (X : Ω → ℝ) :
    (uniforme Ω).esp X = (∑ ω, X ω) / Fintype.card Ω := by
  simp [Ley.esp, uniforme, ← Finset.mul_sum, div_eq_inv_mul]

end Pesos

/-! ## 1. 3-SAT al azar y el primer momento -/

section PrimerMomento

variable {n : ℕ} {V : Type*} [Fintype V] (var : V → Fin 3 → Fin n)

/-- Una cláusula: una terna de variables y tres signos. -/
abbrev Clausula (V : Type*) := V × (Fin 3 → Bool)

/-- `x` satisface la cláusula `(v, s)` si algún literal es verdadero: `x (var v i) = s i`. -/
def Satisface (x : Fin n → Bool) (c : Clausula V) : Prop := ∃ i, x (var c.1 i) = c.2 i

instance (x : Fin n → Bool) (c : Clausula V) : Decidable (Satisface var x c) := by
  unfold Satisface; infer_instance

omit [Fintype V] in
/-- De los `8` juegos de signos, uno solo deja la cláusula falsa: el que niega cada literal. -/
lemma cuenta_no_satisface (x : Fin n → Bool) (v : V) :
    (univ.filter (fun s : Fin 3 → Bool => ¬ Satisface var x (v, s))).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun i => !x (var v i), ?_⟩
  ext s
  simp only [Satisface, not_exists, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h; funext i; have := h i; cases hx : x (var v i) <;> cases hs : s i <;> simp_all
  · rintro rfl i; simp

omit [Fintype V] in
lemma cuenta_satisface (x : Fin n → Bool) (v : V) :
    (univ.filter (fun s : Fin 3 → Bool => Satisface var x (v, s))).card = 7 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin 3 → Bool))) (p := fun s => Satisface var x (v, s))
  rw [cuenta_no_satisface, Finset.card_univ] at h
  simp at h
  omega

/-- Una asignación fija satisface `7 · |V|` de las `8 · |V|` cláusulas. -/
lemma suma_satisface (x : Fin n → Bool) :
    (∑ c : Clausula V, if Satisface var x c then (1 : ℝ) else 0) = 7 * Fintype.card V := by
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_boole, cuenta_satisface]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- El número de soluciones de una fórmula de `m` cláusulas: la función de partición a temperatura cero. -/
def numSol {m : ℕ} (F : Fin m → Clausula V) : ℕ :=
  (univ.filter (fun x : Fin n → Bool => ∀ j, Satisface var x (F j))).card

omit [Fintype V] in
lemma numSol_eq_sum {m : ℕ} (F : Fin m → Clausula V) :
    (numSol var F : ℝ) = ∑ x : Fin n → Bool, ∏ j, (if Satisface var x (F j) then (1 : ℝ) else 0) := by
  rw [numSol, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : ∀ j, Satisface var x (F j)
  · simp [h]
  · push Not at h
    obtain ⟨j, hj⟩ := h
    simp only [show ¬ (∀ j, Satisface var x (F j)) from fun h => hj (h j), ite_false]
    rw [eq_comm]
    exact Finset.prod_eq_zero (mem_univ j) (by simp [hj])

/-- **El primer momento**: `E[S] = 2ⁿ · (7/8)^m` bajo la ley uniforme sobre `m` cláusulas independientes. -/
theorem esperanza_soluciones [Nonempty V] (m : ℕ) :
    (uniforme (Fin m → Clausula V)).esp (fun F => (numSol var F : ℝ)) = 2 ^ n * (7 / 8) ^ m := by
  rw [esp_uniforme]
  simp_rw [numSol_eq_sum]
  rw [Finset.sum_comm]
  have hprod : ∀ x : Fin n → Bool,
      (∑ F : Fin m → Clausula V, ∏ j, (if Satisface var x (F j) then (1 : ℝ) else 0))
        = (7 * Fintype.card V) ^ m := by
    intro x
    rw [← Fintype.prod_sum (fun (_ : Fin m) (c : Clausula V) => if Satisface var x c then (1 : ℝ) else 0)]
    simp only [suma_satisface, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hprod]
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_prod, nsmul_eq_mul]
  push_cast
  rw [mul_div_assoc, div_pow, mul_pow, mul_pow]
  field_simp

end PrimerMomento

/-! ## 2. Markov y el umbral -/

section Markov

variable {Ω : Type*} [Fintype Ω]

/-- **Markov** para una variable con valores en `ℕ`: `P(X ≥ 1) ≤ E[X]`. -/
theorem markov (P : Ley Ω) (X : Ω → ℕ) : P.prob (fun ω => 1 ≤ X ω) ≤ P.esp (fun ω => (X ω : ℝ)) := by
  unfold Ley.prob Ley.esp
  refine Finset.sum_le_sum fun ω _ => ?_
  have hw := P.no_neg ω
  split_ifs with h
  · have : (1 : ℝ) ≤ X ω := by exact_mod_cast h
    nlinarith
  · positivity

variable {n : ℕ} {V : Type*} [Fintype V] (var : V → Fin 3 → Fin n)

/-- `P(la fórmula es satisfacible) ≤ 2ⁿ · (7/8)^m`. -/
theorem prob_sat_le [Nonempty V] (m : ℕ) :
    (uniforme (Fin m → Clausula V)).prob (fun F => 1 ≤ numSol var F) ≤ 2 ^ n * (7 / 8) ^ m := by
  rw [← esperanza_soluciones var m]
  exact markov _ _

/-- Con `c > ln 2 / ln (8/7)`, la razón `2 · (7/8)^c` es `< 1`. -/
lemma razon_lt_uno {c : ℝ} (hc : log 2 / log (8 / 7) < c) : 2 * (7 / 8 : ℝ) ^ c < 1 := by
  have h87 : 0 < log (8 / 7 : ℝ) := Real.log_pos (by norm_num)
  have h1 : log 2 < c * log (8 / 7 : ℝ) := by rwa [div_lt_iff₀ h87] at hc
  have h78 : log (7 / 8 : ℝ) = - log (8 / 7) := by
    rw [show (7 / 8 : ℝ) = (8 / 7)⁻¹ by norm_num, Real.log_inv]
  rw [Real.rpow_def_of_pos (by norm_num), h78]
  have : Real.exp (-log (8 / 7) * c) < Real.exp (- log 2) := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
  linarith

lemma razon_pos (c : ℝ) : 0 < 2 * (7 / 8 : ℝ) ^ c := by positivity

/-- **La cota del umbral**: con `m ≥ c·n`, `P(sat) ≤ (2 · (7/8)^c)ⁿ`. -/
theorem prob_sat_le_geom [Nonempty V] {c : ℝ} {m : ℕ} (hm : c * n ≤ m) :
    (uniforme (Fin m → Clausula V)).prob (fun F => 1 ≤ numSol var F) ≤ (2 * (7 / 8 : ℝ) ^ c) ^ n := by
  refine (prob_sat_le var m).trans ?_
  rw [mul_pow, ← Real.rpow_natCast ((7 / 8 : ℝ) ^ c), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast (7 / 8 : ℝ) m]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hm) (by positivity)

lemma prob_no_neg {Ω : Type*} [Fintype Ω] (P : Ley Ω) (A : Ω → Prop) [DecidablePred A] : 0 ≤ P.prob A := by
  unfold Ley.prob
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [P.no_neg ω]

/-- `P(sat)`, definida también cuando no hay ternas (entonces vale `0`). -/
noncomputable def probSat (V : Type*) [Fintype V] {n : ℕ} (var : V → Fin 3 → Fin n) (m : ℕ) : ℝ :=
  @dite _ (Nonempty V) (Classical.propDecidable _)
    (fun h => haveI := h; (uniforme (Fin m → Clausula V)).prob (fun F => 1 ≤ numSol var F))
    (fun _ => 0)

lemma probSat_eq [Nonempty V] (m : ℕ) :
    probSat V var m = (uniforme (Fin m → Clausula V)).prob (fun F => 1 ≤ numSol var F) := by
  unfold probSat
  split
  · rfl
  · rename_i h; exact absurd ‹Nonempty V› h

/-- **El umbral de Markov**: si `m n ≥ c·n` con `c > ln 2 / ln (8/7)` (≈ 5,19), casi ninguna fórmula es satisfacible.
La familia de ternas `V n` es cualquiera, con tal de que a partir de algún `n` haya al menos una. -/
theorem prob_sat_tiende_cero (V : ℕ → Type*) [∀ n, Fintype (V n)] (var : ∀ n, V n → Fin 3 → Fin n)
    (hV : ∀ᶠ n in atTop, Nonempty (V n)) {c : ℝ} (hc : log 2 / log (8 / 7) < c)
    (m : ℕ → ℕ) (hm : ∀ n, c * n ≤ m n) :
    Tendsto (fun n => probSat (V n) (var n) (m n)) atTop (𝓝 0) := by
  have hc0 : 0 ≤ c := by
    have : 0 < log 2 / log (8 / 7 : ℝ) :=
      div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
    linarith
  have hq := razon_lt_uno hc
  have hgeom : Tendsto (fun n : ℕ => (2 * (7 / 8 : ℝ) ^ c) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (razon_pos c).le hq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeom ?_ ?_
  · filter_upwards [hV] with n hn
    rw [probSat_eq]
    exact prob_no_neg _ _
  · filter_upwards [hV] with n hn
    rw [probSat_eq]
    exact prob_sat_le_geom (var n) (hm n)

/-- El caso del enunciado: tres variables **distintas** (`Fin 3 ↪ Fin n`), que existen desde `n = 3`. -/
theorem prob_sat_tiende_cero_distintas {c : ℝ} (hc : log 2 / log (8 / 7) < c)
    (m : ℕ → ℕ) (hm : ∀ n, c * n ≤ m n) :
    Tendsto (fun n => probSat (Fin 3 ↪ Fin n) (fun e => ⇑e) (m n)) atTop (𝓝 0) := by
  refine prob_sat_tiende_cero (fun n => Fin 3 ↪ Fin n) (fun n e => ⇑e) ?_ hc m hm
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact ⟨⟨Fin.castLE hn, Fin.castLE_injective hn⟩⟩

end Markov

/-! ## 3. Recocido contra templado -/

section Jensen

variable {Ω : Type*} [Fintype Ω]

/-- **Jensen**: la entropía templada no supera a la recocida, `E[log Z] ≤ log E[Z]`. -/
theorem templada_le_recocida (P : Ley Ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 < Z ω) :
    P.esp (fun ω => log (Z ω)) ≤ log (P.esp Z) := by
  have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := univ) (w := P.w) (p := Z)
    (fun ω _ => P.no_neg ω) P.suma (fun ω _ => hZ ω)
  simpa [Ley.esp, smul_eq_mul] using this

/-- La igualdad, con pesos positivos, vale si y solo si `Z` es constante. -/
theorem templada_eq_recocida_iff (P : Ley Ω) (hw : ∀ ω, 0 < P.w ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 < Z ω) :
    log (P.esp Z) = P.esp (fun ω => log (Z ω)) ↔ ∀ a b, Z a = Z b := by
  have := strictConcaveOn_log_Ioi.map_sum_eq_iff_of_pos (t := univ) (w := P.w) (p := Z)
    (fun ω _ => hw ω) P.suma (fun ω _ => hZ ω)
  simpa [Ley.esp, smul_eq_mul] using this

end Jensen

/-! ## 4. El segundo momento -/

section SegundoMomento

variable {Ω : Type*} [Fintype Ω]

/-- `E[Z]² ≤ E[Z²] · P(Z > 0)` para `Z ≥ 0` (Cauchy–Schwarz). -/
theorem sq_esp_le (P : Ley Ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω) :
    P.esp Z ^ 2 ≤ P.esp (fun ω => Z ω ^ 2) * P.prob (fun ω => 0 < Z ω) := by
  unfold Ley.esp Ley.prob
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul univ (fun ω _ => ?_) (fun ω _ => ?_) (fun ω _ => ?_)
  · have := P.no_neg ω; positivity
  · split_ifs <;> simp [P.no_neg ω]
  · have hw := P.no_neg ω
    split_ifs with h
    · nlinarith [sq_nonneg (P.w ω * Z ω)]
    · have : Z ω = 0 := le_antisymm (not_lt.mp h) (hZ ω)
      simp [this]

/-- **Paley–Zygmund**: `P(Z > 0) ≥ E[Z]² / E[Z²]` para `Z ≥ 0` con `E[Z] > 0`. -/
theorem paley_zygmund (P : Ley Ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω) (hE : 0 < P.esp Z) :
    P.esp Z ^ 2 / P.esp (fun ω => Z ω ^ 2) ≤ P.prob (fun ω => 0 < Z ω) := by
  have h := sq_esp_le P Z hZ
  have h2 : 0 < P.esp (fun ω => Z ω ^ 2) := by
    by_contra hneg
    push Not at hneg
    have hp : 0 ≤ P.prob (fun ω => 0 < Z ω) := prob_no_neg _ _
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg hp, sq_pos_of_pos hE]
  rw [div_le_iff₀ h2]
  linarith

/-- Aplicado a 3-SAT: `P(sat) ≥ E[S]² / E[S²]`. -/
theorem prob_sat_ge {n : ℕ} {V : Type*} [Fintype V] [Nonempty V] (var : V → Fin 3 → Fin n) (m : ℕ) :
    (uniforme (Fin m → Clausula V)).esp (fun F => (numSol var F : ℝ)) ^ 2 /
        (uniforme (Fin m → Clausula V)).esp (fun F => (numSol var F : ℝ) ^ 2)
      ≤ (uniforme (Fin m → Clausula V)).prob (fun F => 1 ≤ numSol var F) := by
  have hE : 0 < (uniforme (Fin m → Clausula V)).esp (fun F => (numSol var F : ℝ)) := by
    rw [esperanza_soluciones]; positivity
  have := paley_zygmund _ (fun F => (numSol var F : ℝ)) (fun _ => by positivity) hE
  refine this.trans_eq ?_
  unfold Ley.prob
  refine Finset.sum_congr rfl fun F _ => ?_
  simp [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

end SegundoMomento

/-! ## 5. El truco de las réplicas -/

section Replicas

variable {Ω : Type*} [Fintype Ω]

/-- `r ↦ E[Z^r]`. -/
noncomputable def momento (P : Ley Ω) (Z : Ω → ℝ) (r : ℝ) : ℝ := ∑ ω, P.w ω * Z ω ^ r

lemma momento_cero (P : Ley Ω) (Z : Ω → ℝ) : momento P Z 0 = 1 := by
  simp [momento, P.suma]

/-- La derivada de `r ↦ E[Z^r]` en `0` es `E[log Z]`. -/
theorem replicas_deriv (P : Ley Ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 < Z ω) :
    HasDerivAt (momento P Z) (P.esp (fun ω => log (Z ω))) 0 := by
  unfold momento Ley.esp
  have : ∀ ω ∈ (univ : Finset Ω),
      HasDerivAt (fun r : ℝ => P.w ω * Z ω ^ r) (P.w ω * log (Z ω)) 0 := by
    intro ω _
    have h := (hasStrictDerivAt_const_rpow (hZ ω) 0).hasDerivAt.const_mul (P.w ω)
    simpa using h
  have h := HasDerivAt.sum this
  convert h using 1
  ext r; simp

/-- **Las réplicas, la parte rigurosa**: `lím_{r→0} (E[Z^r] − 1)/r = E[log Z]`. -/
theorem replicas (P : Ley Ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 < Z ω) :
    Tendsto (fun r => (momento P Z r - 1) / r) (𝓝[≠] 0) (𝓝 (P.esp (fun ω => log (Z ω)))) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (replicas_deriv P Z hZ)
  refine h.congr fun r => ?_
  simp [slope_def_field, momento_cero]

/-- **Lo que no es riguroso**: los valores en los enteros no fijan la derivada en `0`. `E[Z^r] + sin(π r)` coincide
con `E[Z^r]` en todo entero y su derivada en `0` es `E[log Z] + π`. -/
theorem enteros_no_bastan (P : Ley Ω) (Z : Ω → ℝ) (hZ : ∀ ω, 0 < Z ω) :
    (∀ k : ℕ, momento P Z k + sin (π * k) = momento P Z k) ∧
      HasDerivAt (fun r => momento P Z r + sin (π * r)) (P.esp (fun ω => log (Z ω)) + π) 0 := by
  refine ⟨fun k => by rw [mul_comm, Real.sin_nat_mul_pi, add_zero], ?_⟩
  have hs : HasDerivAt (fun r => sin (π * r)) π 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul π).sin
    simpa using this
  exact (replicas_deriv P Z hZ).add hs

end Replicas

end Sagitta.Map.FisicaEstadistica
