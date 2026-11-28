import Mathlib.Probability.ProductMeasure

/-!
# Al azar, una descripción infinita oscila

La pregunta de José (24 nov 2026), en la nota «El borde es un hueco»: ¿lo incomprimible vive como los
irracionales de la recta? En el modelo de juguete del espacio de Cantor (una descripción infinita es `d : ℕ → Bool`, y
la máquina de descripción `d` gasta `2^n` donde `d` marca `true` y `n` donde marca `false`), quedar **abajo** del borde
de P es que `d` termine en `false`, y quedar **arriba** es que termine en `true`. Las dos cosas son raras: son conjuntos
numerables. Lo genérico es oscilar.

Aquí se prueba la parte de probabilidad, sin el modelo de tiempo: si cada bit de `d` se elige con una moneda justa e
independiente, **casi seguro `d` tiene infinitos `true` e infinitos `false`**.

## Lo que se prueba

* `moneda`: la moneda justa sobre `Bool` (`moneda_singleton`: cada lado pesa `2⁻¹`); `lanzar`: la medida producto
  infinita de Mathlib (`Measure.infinitePi`) sobre `ℕ → Bool`, una moneda por bit.
* `lanzar_cola_constante` : para cada `N` y cada `b`, el conjunto de las `d` que valen `b` desde `N` mide `0`. La prueba
  no usa Borel–Cantelli: ese conjunto está dentro de «vale `b` en `N, …, N+k−1`», que mide `2⁻ᵏ` (`infinitePi_pi`)
  para todo `k`.
* `lanzar_finalmente` : las `d` que finalmente valen `b` miden `0` (unión numerable sobre `N`).
* **`casi_seguro_oscila`** : `∀ᵐ d ∂lanzar, (∃ᶠ n in atTop, d n = true) ∧ (∃ᶠ n in atTop, d n = false)`.

## Lo que no se prueba aquí

* La conexión con el borde de P (`t d ∈ Pol ↔` finitos `true`, y que con infinitos de cada uno `t d` oscila) es de
  `Sagitta/Map/Continuo/ClaseNoContinua.lean` (agendado para la madrugada del 25 nov 2026, partes (b) y (f)); el corolario
  «casi toda descripción da un tiempo que oscila» se arma en la fase B1 (`Sagitta/Map/Borde/`).
* Nada de aleatoriedad de Martin-Löf ni de complejidad de Kolmogorov: «al azar» es aquí «casi seguro para la medida de
  la moneda», que es la versión clásica. Que las sucesiones aleatorias en el sentido de Martin-Löf también oscilen es
  cierto (una sucesión que termina en constante es computable), pero no está en Mathlib y no se intenta.
-/

open MeasureTheory Filter

namespace Sagitta.Map.Continuo.Moneda

/-- La moneda justa sobre `Bool`. -/
noncomputable def moneda : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

theorem moneda_singleton (b : Bool) : moneda {b} = 2⁻¹ := by
  cases b <;> simp [moneda]

instance : IsProbabilityMeasure moneda := by
  constructor
  simp [moneda]
  exact ENNReal.inv_two_add_inv_two

/-- Una moneda justa e independiente por cada bit. -/
noncomputable def lanzar : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => moneda)

instance : IsProbabilityMeasure lanzar := by
  unfold lanzar; infer_instance

/-- Valer `b` en `N, …, N+k−1` mide `2⁻ᵏ`. -/
theorem lanzar_bloque (N k : ℕ) (b : Bool) :
    lanzar (Set.pi (Finset.Ico N (N + k) : Set ℕ) (fun _ => {b})) = 2⁻¹ ^ k := by
  rw [lanzar, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton b)]
  simp [moneda_singleton]

/-- Las descripciones que valen `b` desde `N` miden `0`. -/
theorem lanzar_cola_constante (N : ℕ) (b : Bool) : lanzar {d | ∀ n, N ≤ n → d n = b} = 0 := by
  apply le_antisymm _ (zero_le)
  have hk : ∀ k, lanzar {d | ∀ n, N ≤ n → d n = b} ≤ 2⁻¹ ^ k := by
    intro k
    rw [← lanzar_bloque N k b]
    apply measure_mono
    intro d hd n hn
    simp only [Finset.coe_Ico, Set.mem_Ico] at hn
    exact hd n hn.1
  have ht : Tendsto (fun k : ℕ => (2⁻¹ : ENNReal) ^ k) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact ge_of_tendsto' ht hk

/-- Las descripciones que finalmente valen `b` miden `0`. -/
theorem lanzar_finalmente (b : Bool) : lanzar {d | ∀ᶠ n in atTop, d n = b} = 0 := by
  have : {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} = ⋃ N, {d | ∀ n, N ≤ n → d n = b} := by
    ext d; simp [eventually_atTop]
  rw [this]
  exact measure_iUnion_null (fun N => lanzar_cola_constante N b)

/-- **Al azar, una descripción infinita oscila**: casi seguro tiene infinitos `true` e infinitos `false`. -/
theorem casi_seguro_oscila :
    ∀ᵐ d ∂lanzar, (∃ᶠ n in atTop, d n = true) ∧ (∃ᶠ n in atTop, d n = false) := by
  rw [ae_iff]
  apply measure_mono_null _ (measure_union_null (lanzar_finalmente false) (lanzar_finalmente true))
  intro d hd
  simp only [Set.mem_ofPred_eq, not_and_or, not_frequently] at hd
  rcases hd with h | h
  · left; simpa using h
  · right; simpa using h

/-! ## Controles -/

/-- La moneda no es trivial: un bit fijo vale `true` con probabilidad `1/2`, no `0` ni `1`. -/
example : lanzar {d | d 0 = true} = 2⁻¹ := by
  have : {d : ℕ → Bool | d 0 = true} = Set.pi (Finset.Ico 0 (0 + 1) : Set ℕ) (fun _ => {true}) := by
    ext d; simp
  rw [this, lanzar_bloque]; simp

/-- Una descripción concreta que oscila (alterna), para ver que el conjunto de las que oscilan no es vacío de manera
trivial. -/
example : (∃ᶠ n in atTop, (fun n : ℕ => decide (n % 2 = 0)) n = true) ∧
    (∃ᶠ n in atTop, (fun n : ℕ => decide (n % 2 = 0)) n = false) := by
  constructor
  · rw [frequently_atTop]; intro a; exact ⟨2 * a, by omega, by simp⟩
  · rw [frequently_atTop]; intro a; exact ⟨2 * a + 1, by omega, by simp⟩

/-- Y una que no oscila (termina en `false`): está en el conjunto de medida cero. Muestra que `lanzar_finalmente` habla
de algo habitado. -/
example : (fun _ : ℕ => false) ∈ {d : ℕ → Bool | ∀ᶠ n in atTop, d n = false} := by
  simp

/- Mutante probado (24 nov 2026, en /tmp): cambiar en `lanzar_bloque` el exponente `k` por `k + 1`
(`= 2⁻¹ ^ (k + 1)`) deja de compilar: el producto sobre `Finset.Ico N (N + k)` tiene exactamente `k` factores. -/

end Sagitta.Map.Continuo.Moneda
