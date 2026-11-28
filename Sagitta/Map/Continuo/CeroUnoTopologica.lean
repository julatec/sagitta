import Sagitta.Map.Continuo.CeroUno
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# La ley 0–1 topológica: lo de cola es magro o comagro

`CeroUno.lean` prueba la ley 0–1 de Kolmogorov en el espacio de Cantor: lo que no mira el principio mide `0` o `1`.
Este archivo prueba la versión de categoría, que allí quedó en «lo que no se prueba»: **un conjunto con la propiedad
de Baire que no cambia al modificar finitos bits es magro o comagro**. Y la aplica a «oscila» y a «`t d ∈ Pol`»,
como `CeroUno.lean` con la medida: en los dos ejemplos medida y categoría dan la misma respuesta.

## Lo que se prueba

* `voltear F`: invertir los bits de un conjunto finito `F`. `voltearH F`: es un homeomorfismo (involutivo) del espacio
  de Cantor; `voltear_cola`: cambia finitos bits, así que un conjunto de cola es invariante (`preimagen_cola`).
* `voltear_cubre`: si `U` es abierto y no vacío, las imágenes `voltear F ⁻¹' U` (con `F` recorriendo los conjuntos
  finitos, que son numerables) cubren todo el espacio. Es la **transitividad topológica** de la acción de los cambios
  finitos: cada cilindro se lleva a cualquier otro del mismo largo.
* **`cero_uno_topologica`**: si `S` tiene la propiedad de Baire (`BaireMeasurableSet`) y `Cola S`, entonces `S` es
  magro o `Sᶜ` es magro. La prueba: `S` difiere de un abierto `U` en un magro; si `U = ∅`, `S` es magro; si no,
  `U \ S` es magro, cada `voltear F` lo lleva a `voltear F ⁻¹' U \ S` (magro, porque `voltear F` es homeomorfismo y
  `S` es de cola), y esos cubren `Sᶜ`: unión numerable de magros.
* `cero_uno_topologica_costos`: lo mismo para una propiedad asintótica de los costos `t d` (`Asintotica`).
* `finalmente_magro`: «finalmente `d n = b`» es magro (unión numerable de cerrados sin interior).
* Las aplicaciones: **`oscila_comagro`** (`Oscilaᶜ` es magro) y **`pol_magro`** (`{d | t d ∈ Pol}` es magro), y la ley
  aplicada a los dos (`cero_uno_topologica` con `medible_oscila` y `medible_pol`).
* **La hipótesis de Baire hace falta** (`sierpinski_no_baire`): con el ultrafiltro libre de Mathlib (`hyperfilter ℕ`),
  el conjunto de Sierpiński (las `d` cuyos `true` caen en el ultrafiltro) es de cola y ni magro ni comagro, porque
  `negar` (un homeomorfismo) lo cambia por su complemento. Por la ley, no tiene la propiedad de Baire (ni es
  boreliano). Usa elección.
* **En medida** (`cero_uno_nulo`, `sierpinski_no_nulo_medible`): la ley de Kolmogorov vale también para los conjuntos
  de cola medibles para la compleción de `lanzar` (el núcleo `⋂ F, voltear F ⁻¹' T` de un boreliano `T` casi igual es
  boreliano y de cola, porque voltear preserva la moneda, `preserva_lanzar`); y el conjunto de Sierpiński no es
  nulo-medible, porque `negar` preserva la moneda y mediría lo mismo que su complemento.
* El control negativo, **`bit0_no_cola_top`**: `{d | d 0 = true}` es abierto y cerrado, ni magro ni comagro (el
  espacio de Cantor es de Baire), así que no es de cola; es la versión topológica de `bit0_no_cola`.

## La lectura

La ley de Kolmogorov y esta son la misma idea con dos nociones de «casi todo»: la invariancia ante cambios finitos
fuerza a lo trivial. Aquí la herramienta es que el grupo de los cambios finitos actúa por homeomorfismos y lleva
cualquier abierto a cubrir el espacio con numerables copias. En «oscila» y «`Pol`» las dos leyes coinciden (oscila
mide `1` y es comagro; `Pol` mide `0` y es magro). No siempre: `HuecosFlacos.lean` tiene las ventanas libres, de
medida `0` y residuales, y las dos son de cola.

## Lo que no se prueba

* Que «tener la propiedad de Baire» sea automático para las preguntas de complejidad: se pide como hipótesis; para
  los dos ejemplos sale de que son borelianos (`MeasurableSet.baireMeasurableSet`).
* La ley es clásica (Oxtoby, *Measure and Category*, cap. 21, «the zero-one law»; de memoria, no lo leí en esta
  sesión). Lo propio es la formalización en el modelo de Sagitta.
-/

open Filter Set Topology

namespace Sagitta.Map.Continuo.CeroUnoTop

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Continuo
open Sagitta.Map.Continuo.CeroUno

/-! ## Voltear finitos bits -/

/-- Invertir los bits de `F`. -/
def voltear (F : Finset ℕ) (d : ℕ → Bool) : ℕ → Bool := fun i => xor (d i) (decide (i ∈ F))

theorem voltear_voltear (F : Finset ℕ) (d : ℕ → Bool) : voltear F (voltear F d) = d := by
  funext i; simp [voltear]

theorem voltear_continuo (F : Finset ℕ) : Continuous (voltear F) :=
  continuous_pi fun i => (continuous_of_discreteTopology (f := fun b : Bool => xor b (decide (i ∈ F)))).comp
    (continuous_apply i)

/-- `voltear F` es un homeomorfismo, su propio inverso. -/
def voltearH (F : Finset ℕ) : (ℕ → Bool) ≃ₜ (ℕ → Bool) where
  toFun := voltear F
  invFun := voltear F
  left_inv := voltear_voltear F
  right_inv := voltear_voltear F
  continuous_toFun := voltear_continuo F
  continuous_invFun := voltear_continuo F

/-- `voltear F` cambia finitos bits. -/
theorem voltear_cola (F : Finset ℕ) (d : ℕ → Bool) : ∀ᶠ n in atTop, voltear F d n = d n := by
  rw [eventually_atTop]
  refine ⟨F.sup id + 1, fun n hn => ?_⟩
  have : n ∉ F := fun h => by have := Finset.le_sup (f := id) h; simp at this; omega
  simp [voltear, this]

theorem preimagen_cola {S : Set (ℕ → Bool)} (hc : Cola S) (F : Finset ℕ) : voltear F ⁻¹' S = S := by
  ext d
  exact hc (voltear F d) d (voltear_cola F d)

/-- **Transitividad**: las copias volteadas de un abierto no vacío cubren el espacio. -/
theorem voltear_cubre {U : Set (ℕ → Bool)} (hU : IsOpen U) {x : ℕ → Bool} (hx : x ∈ U) (y : ℕ → Bool) :
    ∃ F : Finset ℕ, y ∈ voltear F ⁻¹' U := by
  obtain ⟨N, hN⟩ := (mem_nhds_iff_cilindro x U).1 (hU.mem_nhds hx)
  refine ⟨(Finset.range N).filter fun i => y i ≠ x i, hN _ fun i hi => ?_⟩
  by_cases h : y i = x i <;> simp [voltear, hi, h]
  cases hy : y i <;> cases hxi : x i <;> simp_all

/-! ## La ley -/

/-- **La ley 0–1 topológica en el espacio de Cantor**: un conjunto de cola con la propiedad de Baire es magro o
comagro. -/
theorem cero_uno_topologica {S : Set (ℕ → Bool)} (hS : BaireMeasurableSet S) (hc : Cola S) :
    IsMeagre S ∨ IsMeagre Sᶜ := by
  obtain ⟨U, hU, hSU⟩ := hS.residualEq_isOpen
  rcases U.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · left
    change {d | d ∈ Sᶜ} ∈ residual (ℕ → Bool)
    filter_upwards [hSU] with d hd
    simpa using hd
  · right
    -- `U \ S` es magro.
    have hUS : IsMeagre (U \ S) := by
      change {d | d ∈ (U \ S)ᶜ} ∈ residual (ℕ → Bool)
      filter_upwards [hSU] with d hd
      have : d ∈ S ↔ d ∈ U := hd
      simp [this]
    -- Sus copias volteadas también, y cubren `Sᶜ`.
    have hcopia : ∀ F : Finset ℕ, IsMeagre (voltear F ⁻¹' (U \ S)) := fun F =>
      hUS.preimage_of_isOpenMap (voltearH F).continuous (voltearH F).isOpenMap
    refine (isMeagre_iUnion hcopia).mono fun y hy => ?_
    obtain ⟨F, hF⟩ := voltear_cubre hU hx y
    refine mem_iUnion.2 ⟨F, hF, ?_⟩
    rw [← preimagen_cola hc F] at hy
    exact hy

/-- **Toda pregunta asintótica sobre el costo, con la propiedad de Baire, es magra o comagra.** -/
theorem cero_uno_topologica_costos {Q : (ℕ → ℕ) → Prop} (hQ : Asintotica Q)
    (hb : BaireMeasurableSet {d | Q (t d)}) :
    IsMeagre {d | Q (t d)} ∨ IsMeagre {d | Q (t d)}ᶜ :=
  cero_uno_topologica hb (cola_de_asintotica hQ)

/-! ## Las aplicaciones: oscila y `Pol` -/

instance : BorelSpace (ℕ → Bool) := ⟨borel_igual⟩

/-- «Desde `N`, todos los bits son `b`» es cerrado y sin interior. -/
theorem desde_raro (b : Bool) (N : ℕ) : IsNowhereDense {d : ℕ → Bool | ∀ n, N ≤ n → d n = b} := by
  have hcl : IsClosed {d : ℕ → Bool | ∀ n, N ≤ n → d n = b} := by
    have : {d : ℕ → Bool | ∀ n, N ≤ n → d n = b} = ⋂ n, ⋂ (_ : N ≤ n), (fun d : ℕ → Bool => d n) ⁻¹' {b} := by
      ext d; simp
    rw [this]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      (isClosed_discrete {b}).preimage (continuous_apply n)
  refine hcl.isNowhereDense_iff.2 (eq_empty_iff_forall_notMem.2 fun e he => ?_)
  obtain ⟨M, hM⟩ := (mem_nhds_iff_cilindro e _).1 (mem_interior_iff_mem_nhds.1 he)
  have h := hM (pegar e M (!b)) (pegar_prefijo e M (!b)) (max M N) (le_max_right M N)
  simp [pegar] at h

/-- **«Finalmente `d n = b`» es magro.** -/
theorem finalmente_magro (b : Bool) : IsMeagre {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} := by
  have : {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} = ⋃ N, {d : ℕ → Bool | ∀ n, N ≤ n → d n = b} := by
    ext d; simp [eventually_atTop]
  rw [this]
  exact isMeagre_iUnion fun N => (desde_raro b N).isMeagre

/-- La ley se aplica a «oscila» … -/
example : IsMeagre Oscila ∨ IsMeagre Oscilaᶜ :=
  cero_uno_topologica medible_oscila.baireMeasurableSet oscila_cola

/-- … y la respuesta es **comagro**: lo que no oscila es finalmente constante. -/
theorem oscila_comagro : IsMeagre Oscilaᶜ := by
  refine ((finalmente_magro true).union (finalmente_magro false)).mono fun d hd => ?_
  simp only [Oscila, mem_compl_iff, mem_ofPred_eq, not_and_or, not_frequently] at hd
  rcases hd with h | h
  · right; exact h.mono fun n hn => by simpa using hn
  · left; exact h.mono fun n hn => by simpa using hn

/-- La ley se aplica a «`t d ∈ Pol`» … -/
example : IsMeagre {d | t d ∈ Pol} ∨ IsMeagre {d | t d ∈ Pol}ᶜ :=
  cero_uno_topologica_costos pol_asintotica medible_pol.baireMeasurableSet

/-- … y la respuesta es **magro**. -/
theorem pol_magro : IsMeagre {d : ℕ → Bool | t d ∈ Pol} := by
  have : {d : ℕ → Bool | t d ∈ Pol} = {d | ∀ᶠ n in atTop, d n = false} := by
    ext d; exact t_pol_iff_finalmente d
  rw [this]; exact finalmente_magro false

/-- Medida y categoría coinciden en los dos ejemplos. -/
theorem oscila_y_pol :
    (Sagitta.Map.Continuo.Moneda.lanzar Oscila = 1 ∧ IsMeagre Oscilaᶜ) ∧
      (Sagitta.Map.Continuo.Moneda.lanzar {d | t d ∈ Pol} = 0 ∧ IsMeagre {d : ℕ → Bool | t d ∈ Pol}) :=
  ⟨⟨lanzar_oscila, oscila_comagro⟩, ⟨lanzar_pol, pol_magro⟩⟩

/-! ## Control negativo -/

/-- Un abierto no vacío no es magro (el espacio de Cantor es de Baire). -/
theorem abierto_no_magro {V : Set (ℕ → Bool)} (hV : IsOpen V) (hne : V.Nonempty) : ¬ IsMeagre V := by
  intro hm
  obtain ⟨d, hdV, hdc⟩ := (dense_of_mem_residual hm).inter_open_nonempty V hV hne
  exact hdc hdV

/-- **Mirar el primer bit no es una pregunta de cola**, ahora por categoría. -/
theorem bit0_no_cola_top : ¬ Cola {d : ℕ → Bool | d 0 = true} := by
  have hab : IsOpen {d : ℕ → Bool | d 0 = true} :=
    (isOpen_discrete {true}).preimage (continuous_apply (A := fun _ : ℕ => Bool) 0)
  have hab' : IsOpen {d : ℕ → Bool | d 0 = true}ᶜ := by
    have : {d : ℕ → Bool | d 0 = true}ᶜ = (fun d : ℕ → Bool => d 0) ⁻¹' {false} := by ext d; simp
    rw [this]; exact (isOpen_discrete {false}).preimage (continuous_apply 0)
  intro hc
  rcases cero_uno_topologica hab.baireMeasurableSet hc with h | h
  · exact abierto_no_magro hab ⟨fun _ => true, rfl⟩ h
  · exact abierto_no_magro hab' ⟨fun _ => false, by simp⟩ h

/-! ## Sin la propiedad de Baire, la ley no vale -/

/-- **El conjunto de Sierpiński**: las descripciones cuyos `true` caen en el ultrafiltro libre `hyperfilter ℕ`. -/
def Sierpinski : Set (ℕ → Bool) := {d | {n | d n = true} ∈ (hyperfilter ℕ : Filter ℕ)}

/-- Cambiar finitos bits no cambia nada: el ultrafiltro es libre. -/
theorem sierpinski_cola : Cola Sierpinski := by
  intro d d' hd
  have h : {n | d n = d' n} ∈ (hyperfilter ℕ : Filter ℕ) := Nat.hyperfilter_le_atTop hd
  constructor
  · intro hs
    change {n | d' n = true} ∈ (hyperfilter ℕ : Filter ℕ)
    filter_upwards [show {n | d n = true} ∈ (hyperfilter ℕ : Filter ℕ) from hs, h] with n h1 h2
    rw [← h2]; exact h1
  · intro hs
    change {n | d n = true} ∈ (hyperfilter ℕ : Filter ℕ)
    filter_upwards [show {n | d' n = true} ∈ (hyperfilter ℕ : Filter ℕ) from hs, h] with n h1 h2
    rw [h2]; exact h1

/-- Negar todos los bits. -/
def negar (d : ℕ → Bool) : ℕ → Bool := fun n => !d n

theorem negar_continuo : Continuous negar :=
  continuous_pi fun i => (continuous_of_discreteTopology (f := fun b : Bool => !b)).comp (continuous_apply i)

/-- `negar` es un homeomorfismo, su propio inverso. -/
def negarH : (ℕ → Bool) ≃ₜ (ℕ → Bool) where
  toFun := negar
  invFun := negar
  left_inv d := by funext n; simp [negar]
  right_inv d := by funext n; simp [negar]
  continuous_toFun := negar_continuo
  continuous_invFun := negar_continuo

/-- `negar` cambia el conjunto de Sierpiński por su complemento: exactamente uno de `A`, `Aᶜ` está en el
ultrafiltro. -/
theorem negar_sierpinski : negar ⁻¹' Sierpinski = Sierpinskiᶜ := by
  ext d
  have e : {n | negar d n = true} = {n | d n = true}ᶜ := by ext n; simp [negar]
  change {n | negar d n = true} ∈ (hyperfilter ℕ : Filter ℕ) ↔ {n | d n = true} ∉ (hyperfilter ℕ : Filter ℕ)
  rw [e]
  exact Ultrafilter.compl_mem_iff_notMem

/-- **Ni magro ni comagro**: si uno de los dos lo fuera, por `negar` el otro también, y el espacio entero sería
magro. -/
theorem sierpinski_ni_magro_ni_comagro : ¬ IsMeagre Sierpinski ∧ ¬ IsMeagre Sierpinskiᶜ := by
  have huniv : ¬ IsMeagre (univ : Set (ℕ → Bool)) := abierto_no_magro isOpen_univ ⟨fun _ => true, trivial⟩
  have hc : ∀ {A : Set (ℕ → Bool)}, IsMeagre A → IsMeagre (negar ⁻¹' A) := fun h =>
    h.preimage_of_isOpenMap negarH.continuous negarH.isOpenMap
  constructor
  · intro h
    have h' := hc h
    rw [negar_sierpinski] at h'
    exact huniv ((h.union h').mono fun d _ => em _)
  · intro h
    have h' := hc h
    rw [preimage_compl, negar_sierpinski, compl_compl] at h'
    exact huniv ((h'.union h).mono fun d _ => em _)

/-- **La hipótesis de Baire hace falta**: el conjunto de Sierpiński es de cola y no es magro ni comagro, así que,
por `cero_uno_topologica`, no tiene la propiedad de Baire. (Usa elección: el ultrafiltro libre.) -/
theorem sierpinski_no_baire : ¬ BaireMeasurableSet Sierpinski := fun h =>
  (cero_uno_topologica h sierpinski_cola).elim sierpinski_ni_magro_ni_comagro.1 sierpinski_ni_magro_ni_comagro.2

/-- En particular no es boreliano. (Que tampoco sea medible para la compleción de `lanzar`, el «no medible» de
Sierpiński, no se prueba aquí: pide la ley de Kolmogorov para conjuntos nulo-medibles.) -/
theorem sierpinski_no_medible : ¬ MeasurableSet Sierpinski := fun h =>
  sierpinski_no_baire h.baireMeasurableSet

/-! ## Sierpiński, también en medida

La ley de Kolmogorov de `CeroUno.lean` pide un conjunto boreliano. Aquí se extiende a los conjuntos medibles para la
compleción de `lanzar` (nulo-medibles): un conjunto de cola nulo-medible coincide casi seguro con uno boreliano de cola.
Con eso, el conjunto de Sierpiński tampoco es nulo-medible: `negar` preserva la moneda y lo cambia por su complemento,
así que mediría `1/2`. -/

section Medida

open MeasureTheory _root_.Sagitta.Map.Continuo.Moneda

/-- La moneda no distingue `b` de `!b`. -/
theorem moneda_not (A : Set Bool) : moneda ((fun b => !b) ⁻¹' A) = moneda A := by
  have e : ∀ b : Bool, b ∈ (fun b => !b) ⁻¹' A ↔ (!b) ∈ A := fun _ => Iff.rfl
  by_cases ht : true ∈ A <;> by_cases hf : false ∈ A <;>
    simp [moneda, Set.indicator, ht, hf, e, add_comm]

/-- Cambiar cada bit por una función que preserva la moneda preserva `lanzar`. -/
theorem preserva_lanzar (g : ℕ → Bool → Bool) (hg : ∀ i A, moneda (g i ⁻¹' A) = moneda A) :
    MeasurePreserving (fun d : ℕ → Bool => fun i => g i (d i)) lanzar lanzar := by
  have hm : Measurable (fun d : ℕ → Bool => fun i => g i (d i)) :=
    measurable_pi_iff.mpr fun i => (measurable_of_countable (g i)).comp (measurable_pi_apply i)
  refine ⟨hm, ?_⟩
  unfold lanzar
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have e : (fun d : ℕ → Bool => fun i => g i (d i)) ⁻¹' Set.pi (s : Set ℕ) t =
      Set.pi (s : Set ℕ) fun i => g i ⁻¹' t i := by
    ext d; simp [Set.mem_pi]
  rw [e, Measure.infinitePi_pi _ fun i _ => MeasurableSet.of_discrete]
  exact Finset.prod_congr rfl fun i _ => hg i (t i)

theorem moneda_voltear (F : Finset ℕ) (i : ℕ) (A : Set Bool) :
    moneda ((fun b => xor b (decide (i ∈ F))) ⁻¹' A) = moneda A := by
  by_cases h : i ∈ F
  · simpa [h] using moneda_not A
  · simp [h]

theorem voltear_preserva (F : Finset ℕ) : MeasurePreserving (voltear F) lanzar lanzar :=
  preserva_lanzar (fun i b => xor b (decide (i ∈ F))) (moneda_voltear F)

theorem negar_preserva : MeasurePreserving negar lanzar lanzar :=
  preserva_lanzar (fun _ b => !b) fun _ A => moneda_not A

theorem voltear_comp (F G : Finset ℕ) (d : ℕ → Bool) : voltear F (voltear G d) = voltear (symmDiff F G) d := by
  funext i
  by_cases hF : i ∈ F <;> by_cases hG : i ∈ G <;> simp [voltear, Finset.mem_symmDiff, hF, hG]

/-- Dos descripciones que coinciden desde algún punto difieren en el volteo de un conjunto finito. -/
theorem cola_es_volteo {d d' : ℕ → Bool} (h : ∀ᶠ n in atTop, d n = d' n) : ∃ G : Finset ℕ, d' = voltear G d := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨(Finset.range N).filter fun i => d i ≠ d' i, funext fun i => ?_⟩
  by_cases hi : i < N
  · by_cases hd : d i = d' i
    · simp [voltear, hd]
    · simp only [voltear, Finset.mem_filter, Finset.mem_range, hi, ne_eq, hd, not_false_eq_true, and_self,
        decide_true]
      cases h1 : d i <;> cases h2 : d' i <;> simp_all
  · have : d i = d' i := hN i (by omega)
    simp [voltear, this, hi]

/-- **La ley 0–1 para conjuntos de cola nulo-medibles.** -/
theorem cero_uno_nulo {S : Set (ℕ → Bool)} (hS : NullMeasurableSet S lanzar) (hc : Cola S) :
    lanzar S = 0 ∨ lanzar S = 1 := by
  set T := toMeasurable lanzar S
  have hT : T =ᵐ[lanzar] S := hS.toMeasurable_ae_eq
  -- El núcleo invariante: `T` volteado de todas las maneras finitas.
  set T' := ⋂ F : Finset ℕ, voltear F ⁻¹' T
  have hT'm : MeasurableSet T' :=
    MeasurableSet.iInter fun F => (voltear_preserva F).measurable (measurableSet_toMeasurable _ _)
  have hT'ae : T' =ᵐ[lanzar] S := by
    have h1 : ∀ F : Finset ℕ, voltear F ⁻¹' T =ᵐ[lanzar] S := fun F => by
      have := (voltear_preserva F).quasiMeasurePreserving.preimage_ae_eq hT
      rwa [preimagen_cola hc F] at this
    have h2 := EventuallyEqSet.countable_iInter (l := ae lanzar) h1
    rwa [Set.iInter_const] at h2
  have hT'c : Cola T' := by
    intro d d' hd
    obtain ⟨G, rfl⟩ := cola_es_volteo hd
    simp only [T', mem_iInter, mem_preimage, voltear_comp]
    constructor
    · intro h F; exact h (symmDiff F G)
    · intro h F
      have := h (symmDiff F G)
      rwa [symmDiff_symmDiff_cancel_right] at this
  rw [← measure_congr hT'ae]
  exact CeroUno.cero_uno hT'm hT'c

/-- **Sierpiński no es medible ni para la compleción de la moneda**: si lo fuera, mediría `0` o `1` por la ley, y
`negar` (que preserva la moneda) lo cambia por su complemento, así que mediría lo mismo que él. -/
theorem sierpinski_no_nulo_medible : ¬ NullMeasurableSet Sierpinski lanzar := by
  intro h
  have hc : lanzar Sierpinskiᶜ = lanzar Sierpinski := by
    rw [← negar_sierpinski]; exact negar_preserva.measure_preimage h
  have hsum := measure_add_measure_compl₀ h
  rw [hc, measure_univ] at hsum
  rcases cero_uno_nulo h sierpinski_cola with h0 | h1
  · rw [h0] at hsum; simp at hsum
  · rw [h1] at hsum; norm_num at hsum

end Medida

/- Mutantes (25 nov 2026, fuera del repositorio):
* MutCT1: `cero_uno_topologica` sin `Cola S`: falla donde la copia volteada de `U \ S` se identifica con
  `voltear F ⁻¹' U \ S` (`preimagen_cola`); y es falso: `{d | d 0 = true}` es abierto, ni magro ni comagro.
* MutCT2: con conclusión `IsMeagre S ∨ IsMeagre S`: falla en la rama `U ≠ ∅`, donde lo que se cubre es `Sᶜ`.
* MutCT3: `oscila_comagro` con `IsMeagre Oscila`: falla al repartir `Oscilaᶜ` en los dos «finalmente constante»;
  y es falso (un abierto no vacío no es magro, y `Oscila` es comagro).
* MutCT4: en `cero_uno_nulo`, el núcleo `T'` cambiado por un solo volteo (`voltear ∅ ⁻¹' T`): falla que `T'` sea de
  cola (y, por forma, la cuenta casi segura); sin intersecar sobre todos los volteos el boreliano no es invariante. -/

end Sagitta.Map.Continuo.CeroUnoTop
