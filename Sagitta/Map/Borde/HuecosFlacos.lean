import Sagitta.Map.Borde.SatEnElBorde

/-!
# Si SAT oscila, oscila de manera nada típica (B2, la parte de medida y categoría)

La pregunta de José (24 nov 2026): «¿cómo se vería SAT en este mundo?». Para cada polinomio `c·(n+1)^k`, la sucesión de
bits de SAT marca `true` en los largos difíciles y `false` en los buenos (`bitsDificiles`). Es un punto del espacio de
Cantor `ℕ → Bool`, el mismo donde `Tricotomia.lean` probó que lo típico oscila con ceros frecuentes.

## Lo que se prueba

* `hueco_iff_ventana`: un hueco de `Relleno.lean` es una **ventana libre** en la sucesión de bits: todos `true` entre
  `n` y `a·(n+1)^b`. Y `sat_ventanas_libres`: si `satBits ∉ PsobrePoly`, para todo polinomio y toda ventana la
  sucesión de bits de `satMarco` tiene infinitas ventanas libres (`VentanasLibres`).
* **Medida cero** (`ventanas_nulas`, `ventanas_nulas_de`): para la moneda `lanzar` de `MonedaOscila.lean`, las
  sucesiones con infinitas ventanas libres de largo `2n` (y con más razón las de cualquier ventana `a·(n+1)^b` con
  `a ≥ 2`, `b ≥ 1`) miden `0`. Es Borel–Cantelli de Mathlib (`measure_setOfPred_frequently_eq_zero`): la ventana en `n`
  pesa a lo sumo `2⁻ⁿ`. Con `sat_bits_en_nulo`: si SAT está fuera de P/poly, sus bits caen, para todo polinomio, en
  ese conjunto de medida cero.
* **Pero no magro** (`ventanas_residual`): el mismo conjunto es **residual**, para toda ventana. Lo que da
  `huecos_de_sat` es atípico por medida y típico por categoría. Es el fenómeno clásico de que medida y categoría no
  coinciden (Oxtoby, *Measure and Category*; no lo leí en esta sesión).
* **La versión de la tarea, magra** (`sin_dos_ceros_magro`): «finalmente no hay dos ceros seguidos» es magro (unión
  numerable de cerrados sin interior). Pero `huecos_de_sat` **no** pone a SAT ahí: da infinitos huecos, no que todos
  los ceros queden separados. Ese enunciado más fuerte no se prueba.
* **Lo que sí vale para todo punto concreto** (`numerable_nulo`, `numerable_magro`): un conjunto numerable de
  descripciones mide `0` y es magro. Las sucesiones computables son numerables, así que la sucesión de SAT (que es
  computable: el menor circuito se halla por fuerza bruta) vive en un conjunto flaco en los dos sentidos, esté donde
  esté. Ni la computabilidad de `bitsDificiles` ni la numerabilidad de lo computable se formalizan aquí.

## Lo que no

* La medida cero de `sin_dos_ceros` (pide independencia por bloques de dos bits bajo `Measure.infinitePi`; no se hizo).
* Que la sucesión de SAT esté en el conjunto magro `sin_dos_ceros`: no se sigue de `huecos_de_sat`.
-/

open Filter Set MeasureTheory Topology

namespace Sagitta.Map.Borde.HuecosFlacos

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Finitud
open Sagitta.Map.Tiempo.Relleno Sagitta.Map.Continuo Sagitta.Map.Continuo.Moneda

/-- Los bits de los largos difíciles de `L` para el polinomio `c·(n+1)^k`: `true` si el óptimo pasa del polinomio. -/
noncomputable def bitsDificiles (L : Problema) (c k n : ℕ) : Bool := decide (c * (n + 1) ^ k < sucNat L n)

/-- Una **ventana libre** en `n`: todos los bits entre `n` y `a·(n+1)^b` valen `true`. -/
def Ventana (a b : ℕ) (d : ℕ → Bool) (n : ℕ) : Prop := ∀ m, n ≤ m → m ≤ a * (n + 1) ^ b → d m = true

/-- Infinitas ventanas libres. -/
def VentanasLibres (a b : ℕ) (d : ℕ → Bool) : Prop := ∃ᶠ n in atTop, Ventana a b d n

theorem hueco_iff_ventana {L : Problema} {c k a b n : ℕ} :
    Hueco L c k a b n ↔ Ventana a b (bitsDificiles L c k) n := by
  simp [Hueco, Ventana, bitsDificiles]

/-- **Los huecos de SAT, como bits.** -/
theorem sat_ventanas_libres (h : CookS12.satBits ∉ PsobrePoly) (c k a b : ℕ) :
    VentanasLibres a b (bitsDificiles satMarco c k) :=
  Nat.frequently_atTop_iff_infinite.2 ((huecos_de_sat h c k a b).mono fun _ hn => hueco_iff_ventana.1 hn)

/-- Si el costo de SAT oscila, hay un polinomio cuyos bits tienen infinitos ceros (largos buenos). -/
theorem sat_oscila_ceros (h : Tricotomia.Oscila (sucNat satMarco)) :
    ∃ c k, ∃ᶠ n in atTop, bitsDificiles satMarco c k n = false := by
  obtain ⟨⟨c, k, hinf⟩, -⟩ := SatEnElBorde.sat_oscila_iff.1 h
  refine ⟨c, k, (Nat.frequently_atTop_iff_infinite.2 hinf).mono fun n hn => ?_⟩
  simp only [bitsDificiles, decide_eq_false_iff_not, not_lt]
  exact hn

/-! ## Medida cero -/

theorem ventana_sub (n : ℕ) :
    {d : ℕ → Bool | Ventana 2 1 d n} ⊆ Set.pi (Finset.Ico n (n + n) : Set ℕ) (fun _ => {true}) := by
  intro d hd m hm
  simp only [Finset.coe_Ico, mem_Ico] at hm
  exact hd m hm.1 (by simp only [pow_one]; omega)

theorem lanzar_ventana (n : ℕ) : lanzar {d : ℕ → Bool | Ventana 2 1 d n} ≤ 2⁻¹ ^ n := by
  rw [← lanzar_bloque n n true]
  exact measure_mono (ventana_sub n)

/-- **Las ventanas libres de largo `2n` miden cero** (Borel–Cantelli). -/
theorem ventanas_nulas : lanzar {d : ℕ → Bool | VentanasLibres 2 1 d} = 0 := by
  apply measure_setOfPred_frequently_eq_zero
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum lanzar_ventana)
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

/-- Con una ventana más ancha, con más razón. -/
theorem ventanas_mono {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) {d : ℕ → Bool} (h : VentanasLibres a b d) :
    VentanasLibres 2 1 d :=
  h.mono fun n hn m h1 h2 => hn m h1 (h2.trans (Nat.mul_le_mul ha (Nat.pow_le_pow_right (by omega) hb)))

theorem ventanas_nulas_de {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    lanzar {d : ℕ → Bool | VentanasLibres a b d} = 0 :=
  measure_mono_null (fun _ hd => ventanas_mono ha hb hd) ventanas_nulas

/-- **Si SAT está fuera de P/poly, sus bits caen en un conjunto de medida cero**, para todo polinomio. -/
theorem sat_bits_en_nulo (h : CookS12.satBits ∉ PsobrePoly) (c k : ℕ) :
    bitsDificiles satMarco c k ∈ {d : ℕ → Bool | VentanasLibres 2 1 d} ∧
      lanzar {d : ℕ → Bool | VentanasLibres 2 1 d} = 0 :=
  ⟨sat_ventanas_libres h c k 2 1, ventanas_nulas⟩

/-! ## Pero residual -/

theorem abierto_bit (m : ℕ) : IsOpen {d : ℕ → Bool | d m = true} := by
  have : {d : ℕ → Bool | d m = true} = (fun d : ℕ → Bool => d m) ⁻¹' {true} := by ext d; simp
  rw [this]
  exact (isOpen_discrete {true}).preimage (continuous_apply m)

theorem abierto_ventana (a b n : ℕ) : IsOpen {d : ℕ → Bool | Ventana a b d n} := by
  have : {d : ℕ → Bool | Ventana a b d n} =
      ⋂ m ∈ Finset.Icc n (a * (n + 1) ^ b), {d : ℕ → Bool | d m = true} := by
    ext d; simp [Ventana]
  rw [this]
  exact isOpen_biInter_finset fun m _ => abierto_bit m

/-- `d` hasta `M`, y después todo `true`, tiene una ventana libre en cada `n ≥ M`. -/
theorem ventana_pegar (d : ℕ → Bool) (a b : ℕ) {M n : ℕ} (h : M ≤ n) : Ventana a b (pegar d M true) n :=
  fun m hm _ => by simp [pegar, Nat.not_lt.2 (h.trans hm)]

/-- **Las ventanas libres son residuales**, para toda ventana: típicas por categoría. -/
theorem ventanas_residual (a b : ℕ) : ∀ᶠ d in residual (ℕ → Bool), VentanasLibres a b d := by
  have heq : {d : ℕ → Bool | VentanasLibres a b d} = ⋂ N, ⋃ n, ⋃ (_ : N ≤ n), {d | Ventana a b d n} := by
    ext d; simp [VentanasLibres, frequently_atTop]
  show {d : ℕ → Bool | VentanasLibres a b d} ∈ residual (ℕ → Bool)
  rw [heq, countable_iInter_mem]
  intro N
  refine residual_of_dense_open (isOpen_iUnion fun n => isOpen_iUnion fun _ => abierto_ventana a b n) ?_
  intro d
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨M, hM⟩ := (mem_nhds_iff_cilindro d t).1 ht
  refine ⟨pegar d (max M N) true, hM _ fun i hi => pegar_prefijo d _ true i (by omega), ?_⟩
  exact mem_iUnion.2 ⟨max M N, mem_iUnion.2 ⟨le_max_right _ _, ventana_pegar d a b le_rfl⟩⟩

/-! ## La versión de la tarea: sin dos ceros seguidos, magra -/

/-- Desde `N`, nunca dos ceros seguidos. -/
def SinDosCerosDesde (N : ℕ) : Set (ℕ → Bool) := {d | ∀ n, N ≤ n → d n = true ∨ d (n + 1) = true}

theorem sinDosCeros_cerrado (N : ℕ) : IsClosed (SinDosCerosDesde N) := by
  have : SinDosCerosDesde N = ⋂ n, ⋂ (_ : N ≤ n), ({d : ℕ → Bool | d n = true} ∪ {d | d (n + 1) = true}) := by
    ext d; simp [SinDosCerosDesde]
  rw [this]
  exact isClosed_iInter fun n => isClosed_iInter fun _ =>
    (isClosed_eq (continuous_apply n) continuous_const).union (isClosed_eq (continuous_apply _) continuous_const)

theorem sinDosCeros_interior (N : ℕ) : interior (SinDosCerosDesde N) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro d hd
  obtain ⟨M, hM⟩ := (mem_nhds_iff_cilindro d _).1 (mem_interior_iff_mem_nhds.1 hd)
  set K := max M N
  have h := hM (Function.update (Function.update d K false) (K + 1) false) (fun i hi => by
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
  rcases h K (le_max_right M N) with h1 | h1
  · rw [Function.update_of_ne (by omega), Function.update_self] at h1
    exact Bool.false_ne_true h1
  · rw [Function.update_self] at h1
    exact Bool.false_ne_true h1

/-- **«Finalmente no hay dos ceros seguidos» es magro.** -/
theorem sin_dos_ceros_magro :
    IsMeagre {d : ℕ → Bool | ∀ᶠ n in atTop, d n = true ∨ d (n + 1) = true} := by
  have : {d : ℕ → Bool | ∀ᶠ n in atTop, d n = true ∨ d (n + 1) = true} = ⋃ N, SinDosCerosDesde N := by
    ext d; simp [SinDosCerosDesde, eventually_atTop]
  rw [this]
  exact isMeagre_iUnion fun N =>
    ((sinDosCeros_cerrado N).isNowhereDense_iff.2 (sinDosCeros_interior N)).isMeagre

/-! ## Todo punto concreto vive en un conjunto flaco -/

/-- La moneda no tiene átomos: un punto mide `0`. -/
theorem lanzar_punto (d : ℕ → Bool) : lanzar {d} = 0 := by
  apply le_antisymm _ (zero_le)
  have hk : ∀ k, lanzar {d} ≤ 2⁻¹ ^ k := by
    intro k
    have hsub : ({d} : Set (ℕ → Bool)) ⊆ Set.pi (Finset.range k : Set ℕ) (fun i => {d i}) := by
      intro e he i _; rw [mem_singleton_iff.1 he]; rfl
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [lanzar, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp [moneda_singleton]
  have ht : Tendsto (fun k : ℕ => (2⁻¹ : ENNReal) ^ k) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact ge_of_tendsto' ht hk

instance : NullSingletonClass lanzar := ⟨lanzar_punto⟩

/-- **Un conjunto numerable de descripciones mide cero.** -/
theorem numerable_nulo {S : Set (ℕ → Bool)} (hS : S.Countable) : lanzar S = 0 :=
  hS.measure_zero lanzar

/-- Un punto es cerrado y sin interior. -/
theorem punto_raro (d : ℕ → Bool) : IsNowhereDense ({d} : Set (ℕ → Bool)) := by
  refine isClosed_singleton.isNowhereDense_iff.2 (eq_empty_iff_forall_notMem.2 fun e he => ?_)
  obtain ⟨M, hM⟩ := (mem_nhds_iff_cilindro e _).1 (mem_interior_iff_mem_nhds.1 he)
  have h1 := hM (Function.update e M (!e M)) (fun i hi => by rw [Function.update_of_ne (by omega)])
  have h2 := hM e (fun _ _ => rfl)
  rw [mem_singleton_iff] at h1 h2
  have := congrFun (h1.trans h2.symm) M
  simp at this

/-- **Un conjunto numerable de descripciones es magro.** -/
theorem numerable_magro {S : Set (ℕ → Bool)} (hS : S.Countable) : IsMeagre S := by
  have : S = ⋃ d ∈ S, {d} := by ext; simp
  rw [this]
  exact isMeagre_biUnion hS fun d _ => (punto_raro d).isMeagre

/-! ## Controles -/

/-- Las ventanas libres no son todo: la sucesión constante `false` no tiene ninguna (de largo positivo). -/
example : ¬ VentanasLibres 2 1 (fun _ => false) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists
  have := hn n le_rfl (by simp only [pow_one]; omega)
  simp at this

/-- Y la constante `true` las tiene todas: el conjunto de medida cero está habitado. -/
example : VentanasLibres 2 1 (fun _ => true) :=
  Frequently.of_forall fun _ _ _ _ => rfl

/-- Un hueco para SAT es una afirmación de ventana sobre sus bits, no sobre otro objeto: control de
`hueco_iff_ventana` con la constante `false` como problema (todo largo es bueno, no hay ventanas libres
para `c ≥ 1`). -/
example (n : ℕ) : ¬ Hueco (fun _ => false) 1 0 2 1 n := by
  intro h
  have := h n le_rfl (by simp only [pow_one]; omega)
  have h0 : sucNat (fun _ : List Bool => false) n ≤ 1 := by
    have : rebanada (fun _ : List Bool => false) n = fun _ => false := rfl
    have hs : sucesion (fun _ : List Bool => false) n ≤ 1 := by
      rw [sucesion, this, tamMin]
      exact iInf_le_of_le 1 (iInf_le_of_le (Shannon.falso n)
        (iInf_le_of_le (Infinito.calcula_falso n) (by norm_num)))
    rw [sucesion_eq] at hs; exact_mod_cast hs
  simp at this
  omega

/- Mutante probado (25 nov 2026, en /tmp/claude-noche/MutHue.lean): en `ventana_sub`, cambiar el bloque
`Finset.Ico n (n + n)` por `Finset.Ico n (n + n + 4)` no compila: la ventana `[n, 2n+2]` no cubre `2n+3`. -/

end Sagitta.Map.Borde.HuecosFlacos
