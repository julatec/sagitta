import Sagitta.Map.Borde.HuecosFlacos
import Mathlib.Probability.BorelCantelli

/-!
# Dos ceros seguidos: al azar aparecen infinitas veces (la medida cero que faltaba)

En `HuecosFlacos.lean` (noche del 25 nov 2026) quedó probado que «finalmente no hay dos ceros seguidos» es **magro**
(`sin_dos_ceros_magro`), y quedó pendiente su **medida cero** bajo la moneda `lanzar` de `MonedaOscila.lean`. Aquí se
cierra: el conjunto es flaco en los dos sentidos, por categoría y por medida.

## Lo que se prueba

* `bloque j = {2j, 2j+1}` y `Cero j`: los dos bits del bloque `j` valen `false`. Los bloques son disjuntos
  (`bloques_disjuntos`).
* `lanzar_ceros`: para un conjunto finito `u` de bits, «todos valen `false` en `u`» mide `∏ i ∈ u, 2⁻¹`
  (`Measure.infinitePi_pi`). Con eso, **`ceros_independientes`**: los sucesos `Cero j` son independientes
  (`iIndepSet`). La prueba es la cuenta directa: la intersección de finitos `Cero j` es «todos `false` en la unión de
  sus bloques», que es otra caja; como los bloques son disjuntos, el producto sobre la unión se parte por bloques
  (`Finset.prod_biUnion`). No se usa la independencia de las coordenadas de `CeroUno.lean`.
* `lanzar_cero`: cada `Cero j` mide `2⁻¹ ^ 2 = 1/4`.
* **`casi_seguro_dos_ceros_bloques`**: casi seguro, infinitos bloques son «00». Es el **segundo** lema de
  Borel–Cantelli de Mathlib (`ProbabilityTheory.measure_limsup_eq_one`): sucesos independientes cuyas medidas suman `∞`.
* **`casi_seguro_dos_ceros`**: casi seguro hay infinitos `n` con `d n = d (n+1) = false`.
* **`sin_dos_ceros_nulo`**: el conjunto de `sin_dos_ceros_magro` mide `0`. Y `sin_dos_ceros_flaco` junta las dos
  cosas: magro y de medida cero.

## Controles

* `cero_no_trivial`: un bloque «00» mide `1/4`, no `0` ni `1`: los sucesos no son triviales.
* El conjunto nulo está habitado: la sucesión constante `true` no tiene dos ceros seguidos (ejemplo abajo).
* Mutante (fuera del repositorio): ver el comentario al final.

## La lectura

Juntando con `HuecosFlacos.lean`: «finalmente no hay dos ceros seguidos» es magro **y** nulo. A diferencia de las
ventanas libres (nulas pero residuales), acá medida y categoría coinciden. Sigue sin probarse que la sucesión de bits
de SAT caiga en este conjunto: `huecos_de_sat` da infinitas ventanas libres, no que todos los ceros queden separados.
-/

open MeasureTheory ProbabilityTheory Filter Set

namespace Sagitta.Map.Continuo.DosCeros

open _root_.Sagitta.Map.Continuo.Moneda

/-- El bloque `j`: los bits `2j` y `2j+1`. -/
def bloque (j : ℕ) : Finset ℕ := Finset.Ico (2 * j) (2 * j + 2)

/-- Los dos bits del bloque `j` valen `false`. -/
def Cero (j : ℕ) : Set (ℕ → Bool) := Set.pi (bloque j : Set ℕ) (fun _ => {false})

theorem medible_cero (j : ℕ) : MeasurableSet (Cero j) :=
  MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton false)

theorem mem_cero {d : ℕ → Bool} {j : ℕ} : d ∈ Cero j ↔ d (2 * j) = false ∧ d (2 * j + 1) = false := by
  simp only [Cero, bloque, Set.mem_pi, Finset.coe_Ico, Set.mem_Ico, Set.mem_singleton_iff]
  constructor
  · intro h; exact ⟨h _ ⟨le_rfl, by omega⟩, h _ ⟨by omega, by omega⟩⟩
  · rintro ⟨h0, h1⟩ i ⟨hi, hi'⟩
    rcases (show i = 2 * j ∨ i = 2 * j + 1 by omega) with rfl | rfl
    · exact h0
    · exact h1

/-- Los bloques no se pisan. -/
theorem bloques_disjuntos : (Set.univ : Set ℕ).PairwiseDisjoint bloque := by
  intro j _ j' _ hjj'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [bloque, Finset.mem_Ico] at hi hi'
  exact hjj' (by omega)

/-- «Todo `false` en `u`» mide el producto de las mitades. -/
theorem lanzar_ceros (u : Finset ℕ) :
    lanzar (Set.pi (u : Set ℕ) (fun _ => {false})) = ∏ _i ∈ u, (2⁻¹ : ENNReal) := by
  rw [lanzar, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton false)]
  simp [moneda_singleton]

/-- Un bloque «00» mide `1/4`. -/
theorem lanzar_cero (j : ℕ) : lanzar (Cero j) = 2⁻¹ ^ 2 := lanzar_bloque (2 * j) 2 false

/-- **Los bloques «00» son independientes**: la cuenta directa sobre bloques disjuntos. -/
theorem ceros_independientes : iIndepSet Cero lanzar := by
  rw [iIndepSet_iff_meas_biInter medible_cero]
  intro s
  have hinter : (⋂ j ∈ s, Cero j) = Set.pi ((s.biUnion bloque : Finset ℕ) : Set ℕ) (fun _ => {false}) := by
    ext d
    simp only [Cero, Set.mem_iInter, Set.mem_pi, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro h i ⟨j, hj, hi⟩; exact h j hj i hi
    · intro h j hj i hi; exact h i ⟨j, hj, hi⟩
  rw [hinter, lanzar_ceros, Finset.prod_biUnion (bloques_disjuntos.subset (Set.subset_univ _))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← lanzar_ceros]
  rfl

/-- **Casi seguro, infinitos bloques son «00»** (segundo lema de Borel–Cantelli). -/
theorem casi_seguro_dos_ceros_bloques : ∀ᵐ d ∂lanzar, ∃ᶠ j in atTop, d ∈ Cero j := by
  have hsuma : (∑' j, lanzar (Cero j)) = ⊤ := by
    simp_rw [lanzar_cero]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by simp)
  have h1 := measure_limsup_eq_one medible_cero ceros_independientes hsuma
  have hmed : MeasurableSet (limsup Cero atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => medible_cero i
  rw [← prob_compl_eq_zero_iff hmed] at h1
  rw [ae_iff]
  refine measure_mono_null (fun d hd => ?_) h1
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_compl_iff]
  rwa [Filter.mem_limsup_iff_frequently_mem]

/-- **Casi seguro hay infinitos pares de ceros seguidos.** -/
theorem casi_seguro_dos_ceros : ∀ᵐ d ∂lanzar, ∃ᶠ n in atTop, d n = false ∧ d (n + 1) = false := by
  filter_upwards [casi_seguro_dos_ceros_bloques] with d hd
  rw [frequently_atTop] at hd ⊢
  intro N
  obtain ⟨j, hj, hc⟩ := hd N
  exact ⟨2 * j, by omega, mem_cero.1 hc⟩

/-- **«Finalmente no hay dos ceros seguidos» mide cero.** -/
theorem sin_dos_ceros_nulo :
    lanzar {d : ℕ → Bool | ∀ᶠ n in atTop, d n = true ∨ d (n + 1) = true} = 0 := by
  have h0 := casi_seguro_dos_ceros
  rw [ae_iff] at h0
  refine measure_mono_null (fun d hd => ?_) h0
  simp only [Set.mem_ofPred_eq] at hd ⊢
  intro hf
  obtain ⟨n, hn⟩ := (hd.and_frequently hf).exists
  rcases hn.1 with h | h
  · rw [hn.2.1] at h; exact Bool.false_ne_true h
  · rw [hn.2.2] at h; exact Bool.false_ne_true h

/-- **Flaco en los dos sentidos**: magro (`HuecosFlacos.sin_dos_ceros_magro`) y de medida cero. -/
theorem sin_dos_ceros_flaco :
    IsMeagre {d : ℕ → Bool | ∀ᶠ n in atTop, d n = true ∨ d (n + 1) = true} ∧
      lanzar {d : ℕ → Bool | ∀ᶠ n in atTop, d n = true ∨ d (n + 1) = true} = 0 :=
  ⟨Borde.HuecosFlacos.sin_dos_ceros_magro, sin_dos_ceros_nulo⟩

/-! ## Controles -/

/-- Un bloque «00» no es un suceso trivial: mide `1/4`, ni `0` ni `1`. -/
theorem cero_no_trivial (j : ℕ) : lanzar (Cero j) ≠ 0 ∧ lanzar (Cero j) ≠ 1 := by
  rw [lanzar_cero]
  refine ⟨by simp, ?_⟩
  intro h
  have : (2⁻¹ : ENNReal) ^ 2 < 1 := pow_lt_one₀ (by simp) (ENNReal.inv_lt_one.2 (by norm_num)) (by norm_num)
  exact this.ne h

/-- El conjunto nulo está habitado: la constante `true` nunca tiene dos ceros seguidos. -/
example : (fun _ : ℕ => true) ∈ {d : ℕ → Bool | ∀ᶠ n in atTop, d n = true ∨ d (n + 1) = true} := by
  simp

/-- Y el suceso de `casi_seguro_dos_ceros` no es «todo»: la constante `true` está fuera. -/
example : ¬ ∃ᶠ n in atTop, (fun _ : ℕ => true) n = false ∧ (fun _ : ℕ => true) (n + 1) = false := by
  simp

/- Mutante probado (25 nov 2026, fuera del repositorio, `MutDos.lean`): con bloques que se pisan,
`bloque j := Finset.Ico j (j + 2)`, no compila: `omega` no puede probar `bloques_disjuntos` (los bloques `j` y `j+1`
comparten el bit `j+1`), y sin disjuntos `Finset.prod_biUnion` no parte el producto, así que la cuenta de
`ceros_independientes` se cae. La independencia sale de la disjunción, no de otra cosa. -/

end Sagitta.Map.Continuo.DosCeros
