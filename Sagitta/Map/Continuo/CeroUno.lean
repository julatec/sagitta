import Sagitta.Map.Continuo.MonedaOscila
import Sagitta.Map.Continuo.ClaseNoContinua
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Independence.InfinitePi

/-!
# La ley 0–1 para la complejidad: la cola y el principio

La pregunta de José (24 nov 2026): «¿cómo se caracterizan las funciones que tenemos?». Una respuesta parcial y
exacta: **toda pregunta asintótica sobre una descripción al azar tiene probabilidad 0 o 1**. Es la ley 0–1 de
Kolmogorov, que está en Mathlib (`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`), puesta en el
espacio de Cantor con la moneda justa `lanzar` de `MonedaOscila.lean`.

## Lo que se prueba

* `coord n`: la σ-álgebra que genera el bit `n` (`MeasurableSpace.comap (· n)`). `coord_le`: está dentro de la de
  `ℕ → Bool`.
* **`coord_independientes`**: bajo `lanzar`, las `coord n` son independientes (`iIndep`). Sale de
  `ProbabilityTheory.iIndepFun_infinitePi` (Mathlib, para `Measure.infinitePi`) y `iIndepFun_iff_iIndep`.
* `Cola S`: `S` no cambia al modificar finitos bits. **`cola_medible`**: un conjunto medible con `Cola S` es medible
  para la σ-álgebra de cola `limsup coord atTop`. La prueba: para cada `n`, `S` es la preimagen de sí mismo por
  `borrar n` (poner en `false` los primeros `n` bits), y `borrar n` es medible desde `⨆ i ≥ n, coord i`.
* **`cero_uno`**: todo conjunto medible de descripciones con `Cola S` mide `0` o `1` bajo `lanzar`.
* `Asintotica Q`: una propiedad de los costos `Q : (ℕ → ℕ) → Prop` que no distingue funciones que coinciden desde
  algún punto. **`cero_uno_costos`**: si `Q` es asintótica y `{d | Q (t d)}` es medible, mide `0` o `1`, con el
  `t d n = if d n then 2^n else n` de `ClaseNoContinua.lean`.

## Controles

* `pol_asintotica` y `medible_pol`: «`t d ∈ Pol`» es asintótica y medible; **`lanzar_pol`**: mide `0` (con
  `t_pol_iff_finalmente` y `lanzar_finalmente`).
* `oscila_cola` y `medible_oscila`: «oscila» (infinitos `true` e infinitos `false`) cumple `Cola` y es medible;
  **`lanzar_oscila`**: mide `1` (con `casi_seguro_oscila`).
* `lanzar_bit0`: el control negativo. `{d | d 0 = true}` mide `1/2`, así que **no** cumple `Cola` (`bit0_no_cola`):
  una pregunta que mira el principio no está sujeta a la ley.

## La lectura

La complejidad mira la cola; la topología, el principio. Lo continuo (`continuo_iff_prefijo`) depende de un prefijo;
lo asintótico no depende de ningún prefijo. Por eso, al azar, toda pregunta de complejidad sobre una descripción
infinita tiene una respuesta casi segura. La ley no dice **cuál**: decir si «`t d` oscila» mide `1` y «`t d ∈ Pol`»
mide `0` pide un argumento aparte (`casi_seguro_oscila`, `lanzar_finalmente`).

## Lo que no se prueba

* La ley 0–1 topológica (todo conjunto con la propiedad de Baire que cumple `Cola` es magro o comagro) está en
  `Sagitta/Map/Continuo/CeroUnoTopologica.lean`, junto con la ley de este archivo para conjuntos nulo-medibles. Las clases
  de Baire (el tiempo es de clase 0, parar de clase 1, estar en P de clase 2) y la dimensión efectiva de Lutz se
  mencionan en las notas del proyecto, sin formalizar.
* La medibilidad de una `Q` general es una hipótesis; se prueba solo para los dos ejemplos.
* La ley 0–1 es de Kolmogorov (1933) y está en Mathlib; lo propio es ponerla en el modelo de Sagitta.
-/

open MeasureTheory ProbabilityTheory Filter Set

namespace Sagitta.Map.Continuo.CeroUno

open _root_.Sagitta.Map.Continuo.Moneda Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Continuo

/-- La σ-álgebra del bit `n`. -/
@[instance_reducible] def coord (n : ℕ) : MeasurableSpace (ℕ → Bool) := MeasurableSpace.comap (fun d => d n) inferInstance

theorem coord_le (n : ℕ) : coord n ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  (measurable_pi_apply n).comap_le

/-- **Los bits de la moneda son independientes.** -/
theorem coord_independientes : iIndep coord lanzar := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => moneda) (X := fun _ (b : Bool) => b) (fun _ => measurable_id)
  rw [iIndepFun_iff_iIndep] at h
  exact h

/-- `S` no cambia al modificar finitos bits. -/
def Cola (S : Set (ℕ → Bool)) : Prop :=
  ∀ d d' : ℕ → Bool, (∀ᶠ n in atTop, d n = d' n) → (d ∈ S ↔ d' ∈ S)

/-- Borrar los primeros `n` bits (ponerlos en `false`). -/
def borrar (n : ℕ) (d : ℕ → Bool) : ℕ → Bool := fun i => if i < n then false else d i

theorem borrar_medible (n : ℕ) :
    @Measurable _ _ (⨆ i ≥ n, coord i) inferInstance (borrar n) := by
  rw [@measurable_pi_iff]
  intro i
  by_cases hi : i < n
  · simp only [borrar, hi, ite_true]
    exact @measurable_const _ _ _ (⨆ i ≥ n, coord i) _
  · simp only [borrar, hi, ite_false]
    have h1 : @Measurable _ _ (coord i) inferInstance (fun d : ℕ → Bool => d i) := comap_measurable _
    exact h1.mono (le_iSup₂ (f := fun j (_ : j ≥ n) => coord j) i (Nat.le_of_not_lt hi)) le_rfl

/-- **Lo que no mira el principio es de cola.** -/
theorem cola_medible {S : Set (ℕ → Bool)} (hS : MeasurableSet S) (hc : Cola S) :
    MeasurableSet[limsup coord atTop] S := by
  rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro n
  have e : S = borrar n ⁻¹' S := by
    ext d
    refine hc d (borrar n d) ?_
    rw [eventually_atTop]
    exact ⟨n, fun i hi => by simp [borrar, Nat.not_lt.2 hi]⟩
  rw [e]
  exact (borrar_medible n) hS

/-- **La ley 0–1 en el espacio de Cantor.** -/
theorem cero_uno {S : Set (ℕ → Bool)} (hS : MeasurableSet S) (hc : Cola S) : lanzar S = 0 ∨ lanzar S = 1 :=
  measure_zero_or_one_of_measurableSet_limsup_atTop coord_le coord_independientes (cola_medible hS hc)

/-- Una propiedad de los costos es asintótica si no distingue funciones que coinciden desde algún punto. -/
def Asintotica (Q : (ℕ → ℕ) → Prop) : Prop := ∀ f g : ℕ → ℕ, (∀ᶠ n in atTop, f n = g n) → (Q f ↔ Q g)

theorem cola_de_asintotica {Q : (ℕ → ℕ) → Prop} (hQ : Asintotica Q) : Cola {d | Q (t d)} := by
  intro d d' hd
  apply hQ
  filter_upwards [hd] with n hn
  simp [t, hn]

/-- **Toda pregunta asintótica sobre el costo de una descripción al azar tiene probabilidad 0 o 1.** -/
theorem cero_uno_costos {Q : (ℕ → ℕ) → Prop} (hQ : Asintotica Q) (hm : MeasurableSet {d | Q (t d)}) :
    lanzar {d | Q (t d)} = 0 ∨ lanzar {d | Q (t d)} = 1 :=
  cero_uno hm (cola_de_asintotica hQ)

/-! ## Controles -/

/-- `Pol` no mira el principio. -/
theorem pol_asintotica : Asintotica (· ∈ Pol) := by
  have un : ∀ f g : ℕ → ℕ, (∀ᶠ n in atTop, f n = g n) → g ∈ Pol → f ∈ Pol := by
    intro f g hfg hg
    rw [pol_iff_O] at hg ⊢
    obtain ⟨k, C, N, hN⟩ := hg
    obtain ⟨M, hM⟩ := eventually_atTop.1 hfg
    exact ⟨k, C, max N M, fun n hn => by
      rw [hM n (le_of_max_le_right hn)]; exact hN n (le_of_max_le_left hn)⟩
  intro f g hfg
  exact ⟨un g f (hfg.mono fun _ h => h.symm), un f g hfg⟩

theorem medible_bit (n : ℕ) (b : Bool) : MeasurableSet {d : ℕ → Bool | d n = b} :=
  measurableSet_eq_fun (measurable_pi_apply n) measurable_const

theorem medible_finalmente (b : Bool) : MeasurableSet {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} := by
  have : {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} = ⋃ N, ⋂ n, ⋂ (_ : N ≤ n), {d | d n = b} := by
    ext d; simp [eventually_atTop]
  rw [this]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    medible_bit n b

theorem medible_frecuente (b : Bool) : MeasurableSet {d : ℕ → Bool | ∃ᶠ n in atTop, d n = b} := by
  have : {d : ℕ → Bool | ∃ᶠ n in atTop, d n = b} = ⋂ N, ⋃ n, ⋃ (_ : N ≤ n), {d | d n = b} := by
    ext d; simp [frequently_atTop]
  rw [this]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
    medible_bit n b

theorem medible_pol : MeasurableSet {d : ℕ → Bool | t d ∈ Pol} := by
  have : {d : ℕ → Bool | t d ∈ Pol} = {d | ∀ᶠ n in atTop, d n = false} := by
    ext d; exact t_pol_iff_finalmente d
  rw [this]; exact medible_finalmente false

/-- La ley se aplica a «`t d ∈ Pol`» … -/
example : lanzar {d | t d ∈ Pol} = 0 ∨ lanzar {d | t d ∈ Pol} = 1 :=
  cero_uno_costos pol_asintotica medible_pol

/-- … y la respuesta es `0`. -/
theorem lanzar_pol : lanzar {d | t d ∈ Pol} = 0 := by
  have : {d : ℕ → Bool | t d ∈ Pol} = {d | ∀ᶠ n in atTop, d n = false} := by
    ext d; exact t_pol_iff_finalmente d
  rw [this]; exact lanzar_finalmente false

/-- El conjunto de las descripciones que oscilan. -/
def Oscila : Set (ℕ → Bool) := {d | (∃ᶠ n in atTop, d n = true) ∧ (∃ᶠ n in atTop, d n = false)}

theorem oscila_cola : Cola Oscila := by
  have fr : ∀ (b : Bool) (d d' : ℕ → Bool), (∀ᶠ n in atTop, d n = d' n) →
      (∃ᶠ n in atTop, d n = b) → (∃ᶠ n in atTop, d' n = b) := fun b d d' hd hf =>
    (hf.and_eventually hd).mono fun n ⟨h1, h2⟩ => h2 ▸ h1
  intro d d' hd
  have hd' : ∀ᶠ n in atTop, d' n = d n := hd.mono fun _ h => h.symm
  exact ⟨fun ⟨a, b⟩ => ⟨fr _ _ _ hd a, fr _ _ _ hd b⟩, fun ⟨a, b⟩ => ⟨fr _ _ _ hd' a, fr _ _ _ hd' b⟩⟩

theorem medible_oscila : MeasurableSet Oscila := (medible_frecuente true).inter (medible_frecuente false)

example : lanzar Oscila = 0 ∨ lanzar Oscila = 1 := cero_uno medible_oscila oscila_cola

/-- **Al azar, se oscila**: la respuesta es `1`. -/
theorem lanzar_oscila : lanzar Oscila = 1 := by
  have h0 : lanzar Oscilaᶜ = 0 := ae_iff.1 casi_seguro_oscila
  exact (prob_compl_eq_zero_iff medible_oscila).1 h0

/-- El control negativo: el primer bit mide `1/2`. -/
theorem lanzar_bit0 : lanzar {d | d 0 = true} = 2⁻¹ := by
  have : {d : ℕ → Bool | d 0 = true} = Set.pi (Finset.Ico 0 (0 + 1) : Set ℕ) (fun _ => {true}) := by
    ext d; simp
  rw [this, lanzar_bloque]; simp

/-- … así que mirar el primer bit no es una pregunta de cola. -/
theorem bit0_no_cola : ¬ Cola {d : ℕ → Bool | d 0 = true} := by
  intro hc
  rcases cero_uno (medible_bit 0 true) hc with h | h <;>
    rw [lanzar_bit0] at h <;> norm_num at h

/- Mutante (probado en /tmp/claude-noche/MutCeroUno1.lean, 25 nov 2026): con `Cola` definida como «no cambia al
modificar **un** bit fijo, el `0`» (`d ∈ S ↔ Function.update d 0 b ∈ S`), `cola_medible` no compila: borrar los
primeros `n` bits necesita invariancia ante `n` cambios. -/

end Sagitta.Map.Continuo.CeroUno
